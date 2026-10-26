import V185TrunkScan23Chunk1202

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7126463 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 6, 4]
def baseStart_7126463 : Nat := 118140960795 + 7126463 * 2 ^ 59
def prefixEnd_7126463 : Nat := 4983230072969 + 3 ^ 40 * 7126463 * 2
def baseEnd_7126463 : Nat := 1219766961827418804812833

theorem tailTrace_7126463 : CollatzResearch.WordTrace tailWord_7126463 prefixEnd_7126463 1219766961827418804812833 := by
  unfold tailWord_7126463
  simp only [CollatzResearch.WordTrace]
  refine ⟨259923459181049128826992043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173282306120699419217994695 259923459181049128826992043)
  ·
    refine ⟨389885188771573693240488065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259923459181049128826992043 389885188771573693240488065)
    ·
      refine ⟨292413891578680269930366049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389885188771573693240488065 292413891578680269930366049)
      ·
        refine ⟨219310418684010202447774537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292413891578680269930366049 219310418684010202447774537)
        ·
          refine ⟨164482814013007651835830903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219310418684010202447774537 164482814013007651835830903)
          ·
            refine ⟨246724221019511477753746355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164482814013007651835830903 246724221019511477753746355)
            ·
              refine ⟨370086331529267216630619533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246724221019511477753746355 370086331529267216630619533)
              ·
                refine ⟨138782374323475206236482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370086331529267216630619533 138782374323475206236482325)
                ·
                  refine ⟨6505423796412900292335109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138782374323475206236482325 6505423796412900292335109)
                  ·
                    refine ⟨1219766961827418804812833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505423796412900292335109 1219766961827418804812833)
                    ·
                      rfl

theorem cell23_7126463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_7126463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126463 prefixEnd_7126463 := by exact prefixLift 7126463
  have htrace : WordTrace (prefixWord ++ tailWord_7126463) baseStart_7126463 baseEnd_7126463 := by
    simpa [prefixWord, tailWord_7126463, baseEnd_7126463] using wordTrace_append hprefix tailTrace_7126463
  have hstable : (prefixWord ++ tailWord_7126463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126463).length < 2 ^ (prefixWord ++ tailWord_7126463).sum := by decide
  have hdescent : baseEnd_7126463 < baseStart_7126463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126490 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_7126490 : Nat := 118140960795 + 7126490 * 2 ^ 59
def prefixEnd_7126490 : Nat := 4983230072969 + 3 ^ 40 * 7126490 * 2
def baseEnd_7126490 : Nat := 3659314749459927808800875

theorem tailTrace_7126490 : CollatzResearch.WordTrace tailWord_7126490 prefixEnd_7126490 3659314749459927808800875 := by
  unfold tailWord_7126490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64981110987987828109556231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173282962634634208292149949 64981110987987828109556231)
  ·
    refine ⟨97471666481981742164334347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64981110987987828109556231 97471666481981742164334347)
    ·
      refine ⟨146207499722972613246501521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97471666481981742164334347 146207499722972613246501521)
      ·
        refine ⟨109655624792229459934876141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146207499722972613246501521 109655624792229459934876141)
        ·
          refine ⟨41120859297086047475578553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109655624792229459934876141 41120859297086047475578553)
          ·
            refine ⟨30840644472814535606683915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41120859297086047475578553 30840644472814535606683915)
            ·
              refine ⟨46260966709221803410025873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30840644472814535606683915 46260966709221803410025873)
              ·
                refine ⟨34695725031916352557519405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46260966709221803410025873 34695725031916352557519405)
                ·
                  refine ⟨13010896886968632209069777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34695725031916352557519405 13010896886968632209069777)
                  ·
                    refine ⟨9758172665226474156802333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13010896886968632209069777 9758172665226474156802333)
                    ·
                      refine ⟨3659314749459927808800875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758172665226474156802333 3659314749459927808800875)
                      ·
                        rfl

theorem cell23_7126490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_7126490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126490 prefixEnd_7126490 := by exact prefixLift 7126490
  have htrace : WordTrace (prefixWord ++ tailWord_7126490) baseStart_7126490 baseEnd_7126490 := by
    simpa [prefixWord, tailWord_7126490, baseEnd_7126490] using wordTrace_append hprefix tailTrace_7126490
  have hstable : (prefixWord ++ tailWord_7126490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126490).length < 2 ^ (prefixWord ++ tailWord_7126490).sum := by decide
  have hdescent : baseEnd_7126490 < baseStart_7126490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126510 : List Nat := [4, 1, 2, 1, 2, 1, 5, 7]
def baseStart_7126510 : Nat := 118140960795 + 7126510 * 2 ^ 59
def prefixEnd_7126510 : Nat := 4983230072969 + 3 ^ 40 * 7126510 * 2
def baseEnd_7126510 : Nat := 135530556261963619650029

theorem tailTrace_7126510 : CollatzResearch.WordTrace tailWord_7126510 prefixEnd_7126510 135530556261963619650029 := by
  unfold tailWord_7126510
  simp only [CollatzResearch.WordTrace]
  refine ⟨32490646676484856981744123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173283448941252570569301989 32490646676484856981744123)
  ·
    refine ⟨48735970014727285472616185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32490646676484856981744123 48735970014727285472616185)
    ·
      refine ⟨36551977511045464104462139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48735970014727285472616185 36551977511045464104462139)
      ·
        refine ⟨54827966266568196156693209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36551977511045464104462139 54827966266568196156693209)
        ·
          refine ⟨41120974699926147117519907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54827966266568196156693209 41120974699926147117519907)
          ·
            refine ⟨61681462049889220676279861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41120974699926147117519907 61681462049889220676279861)
            ·
              refine ⟨5782637067177114438401237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61681462049889220676279861 5782637067177114438401237)
              ·
                refine ⟨135530556261963619650029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5782637067177114438401237 135530556261963619650029)
                ·
                  rfl

theorem cell23_7126510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_7126510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126510 prefixEnd_7126510 := by exact prefixLift 7126510
  have htrace : WordTrace (prefixWord ++ tailWord_7126510) baseStart_7126510 baseEnd_7126510 := by
    simpa [prefixWord, tailWord_7126510, baseEnd_7126510] using wordTrace_append hprefix tailTrace_7126510
  have hstable : (prefixWord ++ tailWord_7126510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126510).length < 2 ^ (prefixWord ++ tailWord_7126510).sum := by decide
  have hdescent : baseEnd_7126510 < baseStart_7126510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126517 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7126517 : Nat := 118140960795 + 7126517 * 2 ^ 59
def prefixEnd_7126517 : Nat := 4983230072969 + 3 ^ 40 * 7126517 * 2
def baseEnd_7126517 : Nat := 3659328613437599203163251

theorem tailTrace_7126517 : CollatzResearch.WordTrace tailWord_7126517 prefixEnd_7126517 3659328613437599203163251 := by
  unfold tailWord_7126517
  simp only [CollatzResearch.WordTrace]
  refine ⟨259925428722853496049457805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173283619148568997366305203 259925428722853496049457805)
  ·
    refine ⟨97472035771070061018546677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259925428722853496049457805 97472035771070061018546677)
    ·
      refine ⟨9138003353537818220488751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97472035771070061018546677 9138003353537818220488751)
      ·
        refine ⟨13707005030306727330733127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138003353537818220488751 13707005030306727330733127)
        ·
          refine ⟨20560507545460090996099691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13707005030306727330733127 20560507545460090996099691)
          ·
            refine ⟨30840761318190136494149537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560507545460090996099691 30840761318190136494149537)
            ·
              refine ⟨23130570988642602370612153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30840761318190136494149537 23130570988642602370612153)
              ·
                refine ⟨17347928241481951777959115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23130570988642602370612153 17347928241481951777959115)
                ·
                  refine ⟨26021892362222927666938673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17347928241481951777959115 26021892362222927666938673)
                  ·
                    refine ⟨19516419271667195750204005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26021892362222927666938673 19516419271667195750204005)
                    ·
                      refine ⟨3659328613437599203163251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19516419271667195750204005 3659328613437599203163251)
                      ·
                        rfl

theorem cell23_7126517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7126517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126517 prefixEnd_7126517 := by exact prefixLift 7126517
  have htrace : WordTrace (prefixWord ++ tailWord_7126517) baseStart_7126517 baseEnd_7126517 := by
    simpa [prefixWord, tailWord_7126517, baseEnd_7126517] using wordTrace_append hprefix tailTrace_7126517
  have hstable : (prefixWord ++ tailWord_7126517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126517).length < 2 ^ (prefixWord ++ tailWord_7126517).sum := by decide
  have hdescent : baseEnd_7126517 < baseStart_7126517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126520 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_7126520 : Nat := 118140960795 + 7126520 * 2 ^ 59
def prefixEnd_7126520 : Nat := 4983230072969 + 3 ^ 40 * 7126520 * 2
def baseEnd_7126520 : Nat := 3659330153879562691425737

theorem tailTrace_7126520 : CollatzResearch.WordTrace tailWord_7126520 prefixEnd_7126520 3659330153879562691425737 := by
  unfold tailWord_7126520
  simp only [CollatzResearch.WordTrace]
  refine ⟨129962769070921313780908507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173283692094561751707878009 129962769070921313780908507)
  ·
    refine ⟨194944153606381970671362761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129962769070921313780908507 194944153606381970671362761)
    ·
      refine ⟨146208115204786478003522071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194944153606381970671362761 146208115204786478003522071)
      ·
        refine ⟨219312172807179717005283107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146208115204786478003522071 219312172807179717005283107)
        ·
          refine ⟨328968259210769575507924661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219312172807179717005283107 328968259210769575507924661)
          ·
            refine ⟨30840774301009647703867937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328968259210769575507924661 30840774301009647703867937)
            ·
              refine ⟨23130580725757235777900953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30840774301009647703867937 23130580725757235777900953)
              ·
                refine ⟨17347935544317926833425715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23130580725757235777900953 17347935544317926833425715)
                ·
                  refine ⟨26021903316476890250138573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17347935544317926833425715 26021903316476890250138573)
                  ·
                    refine ⟨9758213743678833843801965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26021903316476890250138573 9758213743678833843801965)
                    ·
                      refine ⟨3659330153879562691425737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758213743678833843801965 3659330153879562691425737)
                      ·
                        rfl

theorem cell23_7126520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_7126520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126520 prefixEnd_7126520 := by exact prefixLift 7126520
  have htrace : WordTrace (prefixWord ++ tailWord_7126520) baseStart_7126520 baseEnd_7126520 := by
    simpa [prefixWord, tailWord_7126520, baseEnd_7126520] using wordTrace_append hprefix tailTrace_7126520
  have hstable : (prefixWord ++ tailWord_7126520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126520).length < 2 ^ (prefixWord ++ tailWord_7126520).sum := by decide
  have hdescent : baseEnd_7126520 < baseStart_7126520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126605 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7126605 : Nat := 118140960795 + 7126605 * 2 ^ 59
def prefixEnd_7126605 : Nat := 4983230072969 + 3 ^ 40 * 7126605 * 2
def baseEnd_7126605 : Nat := 3659373799735194858862847

theorem tailTrace_7126605 : CollatzResearch.WordTrace tailWord_7126605 prefixEnd_7126605 3659373799735194858862847 := by
  unfold tailWord_7126605
  simp only [CollatzResearch.WordTrace]
  refine ⟨259928638346534687078661269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173285758897689791385774179 259928638346534687078661269)
  ·
    refine ⟨12184154922493813456812247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259928638346534687078661269 12184154922493813456812247)
    ·
      refine ⟨18276232383740720185218371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12184154922493813456812247 18276232383740720185218371)
      ·
        refine ⟨27414348575611080277827557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276232383740720185218371 27414348575611080277827557)
        ·
          refine ⟨5140190357927077552092667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27414348575611080277827557 5140190357927077552092667)
          ·
            refine ⟨7710285536890616328139001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140190357927077552092667 7710285536890616328139001)
            ·
              refine ⟨5782714152667962246104251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7710285536890616328139001 5782714152667962246104251)
              ·
                refine ⟨8674071229001943369156377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782714152667962246104251 8674071229001943369156377)
                ·
                  refine ⟨6505553421751457526867283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674071229001943369156377 6505553421751457526867283)
                  ·
                    refine ⟨9758330132627186290300925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6505553421751457526867283 9758330132627186290300925)
                    ·
                      refine ⟨3659373799735194858862847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758330132627186290300925 3659373799735194858862847)
                      ·
                        rfl

theorem cell23_7126605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7126605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126605 prefixEnd_7126605 := by exact prefixLift 7126605
  have htrace : WordTrace (prefixWord ++ tailWord_7126605) baseStart_7126605 baseEnd_7126605 := by
    simpa [prefixWord, tailWord_7126605, baseEnd_7126605] using wordTrace_append hprefix tailTrace_7126605
  have hstable : (prefixWord ++ tailWord_7126605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126605).length < 2 ^ (prefixWord ++ tailWord_7126605).sum := by decide
  have hdescent : baseEnd_7126605 < baseStart_7126605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126640 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_7126640 : Nat := 118140960795 + 7126640 * 2 ^ 59
def prefixEnd_7126640 : Nat := 4983230072969 + 3 ^ 40 * 7126640 * 2
def baseEnd_7126640 : Nat := 3659391771558102221925185

theorem tailTrace_7126640 : CollatzResearch.WordTrace tailWord_7126640 prefixEnd_7126640 3659391771558102221925185 := by
  unfold tailWord_7126640
  simp only [CollatzResearch.WordTrace]
  refine ⟨129964957450703944028092687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173286609934271925370790249 129964957450703944028092687)
  ·
    refine ⟨194947436176055916042139031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129964957450703944028092687 194947436176055916042139031)
    ·
      refine ⟨292421154264083874063208547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194947436176055916042139031 292421154264083874063208547)
      ·
        refine ⟨438631731396125811094812821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292421154264083874063208547 438631731396125811094812821)
        ·
          refine ⟨20560862409193397395069351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 438631731396125811094812821 20560862409193397395069351)
          ·
            refine ⟨30841293613790096092604027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560862409193397395069351 30841293613790096092604027)
            ·
              refine ⟨46261940420685144138906041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30841293613790096092604027 46261940420685144138906041)
              ·
                refine ⟨34696455315513858104179531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46261940420685144138906041 34696455315513858104179531)
                ·
                  refine ⟨52044682973270787156269297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34696455315513858104179531 52044682973270787156269297)
                  ·
                    refine ⟨39033512229953090367201973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52044682973270787156269297 39033512229953090367201973)
                    ·
                      refine ⟨3659391771558102221925185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39033512229953090367201973 3659391771558102221925185)
                      ·
                        rfl

theorem cell23_7126640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_7126640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126640 prefixEnd_7126640 := by exact prefixLift 7126640
  have htrace : WordTrace (prefixWord ++ tailWord_7126640) baseStart_7126640 baseEnd_7126640 := by
    simpa [prefixWord, tailWord_7126640, baseEnd_7126640] using wordTrace_append hprefix tailTrace_7126640
  have hstable : (prefixWord ++ tailWord_7126640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126640).length < 2 ^ (prefixWord ++ tailWord_7126640).sum := by decide
  have hdescent : baseEnd_7126640 < baseStart_7126640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126643 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 8]
def baseStart_7126643 : Nat := 118140960795 + 7126643 * 2 ^ 59
def prefixEnd_7126643 : Nat := 4983230072969 + 3 ^ 40 * 7126643 * 2
def baseEnd_7126643 : Nat := 1219797770666688570062557

theorem tailTrace_7126643 : CollatzResearch.WordTrace tailWord_7126643 prefixEnd_7126643 1219797770666688570062557 := by
  unfold tailWord_7126643
  simp only [CollatzResearch.WordTrace]
  refine ⟨259930024320397019568544583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173286682880264679712363055 259930024320397019568544583)
  ·
    refine ⟨389895036480595529352816875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259930024320397019568544583 389895036480595529352816875)
    ·
      refine ⟨584842554720893294029225313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389895036480595529352816875 584842554720893294029225313)
      ·
        refine ⟨438631916040669970521918985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584842554720893294029225313 438631916040669970521918985)
        ·
          refine ⟨328973937030502477891439239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438631916040669970521918985 328973937030502477891439239)
          ·
            refine ⟨493460905545753716837158859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328973937030502477891439239 493460905545753716837158859)
            ·
              refine ⟨740191358318630575255738289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493460905545753716837158859 740191358318630575255738289)
              ·
                refine ⟨555143518738972931441803717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740191358318630575255738289 555143518738972931441803717)
                ·
                  refine ⟨104089409763557424645338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555143518738972931441803717 104089409763557424645338197)
                  ·
                    refine ⟨1219797770666688570062557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104089409763557424645338197 1219797770666688570062557)
                    ·
                      rfl

theorem cell23_7126643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_7126643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126643 prefixEnd_7126643 := by exact prefixLift 7126643
  have htrace : WordTrace (prefixWord ++ tailWord_7126643) baseStart_7126643 baseEnd_7126643 := by
    simpa [prefixWord, tailWord_7126643, baseEnd_7126643] using wordTrace_append hprefix tailTrace_7126643
  have hstable : (prefixWord ++ tailWord_7126643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126643).length < 2 ^ (prefixWord ++ tailWord_7126643).sum := by decide
  have hdescent : baseEnd_7126643 < baseStart_7126643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126650 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_7126650 : Nat := 118140960795 + 7126650 * 2 ^ 59
def prefixEnd_7126650 : Nat := 4983230072969 + 3 ^ 40 * 7126650 * 2
def baseEnd_7126650 : Nat := 3659396906364647182800139

theorem tailTrace_7126650 : CollatzResearch.WordTrace tailWord_7126650 prefixEnd_7126650 3659396906364647182800139 := by
  unfold tailWord_7126650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64982569907842914941012351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173286853087581106509366269 64982569907842914941012351)
  ·
    refine ⟨97473854861764372411518527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64982569907842914941012351 97473854861764372411518527)
    ·
      refine ⟨146210782292646558617277791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97473854861764372411518527 146210782292646558617277791)
      ·
        refine ⟨219316173438969837925916687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146210782292646558617277791 219316173438969837925916687)
        ·
          refine ⟨328974260158454756888875031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219316173438969837925916687 328974260158454756888875031)
          ·
            refine ⟨493461390237682135333312547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328974260158454756888875031 493461390237682135333312547)
            ·
              refine ⟨740192085356523202999968821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493461390237682135333312547 740192085356523202999968821)
              ·
                refine ⟨69393008002174050281247077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740192085356523202999968821 69393008002174050281247077)
                ·
                  refine ⟨13011189000407634427733827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69393008002174050281247077 13011189000407634427733827)
                  ·
                    refine ⟨19516783500611451641600741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13011189000407634427733827 19516783500611451641600741)
                    ·
                      refine ⟨3659396906364647182800139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19516783500611451641600741 3659396906364647182800139)
                      ·
                        rfl

theorem cell23_7126650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_7126650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126650 prefixEnd_7126650 := by exact prefixLift 7126650
  have htrace : WordTrace (prefixWord ++ tailWord_7126650) baseStart_7126650 baseEnd_7126650 := by
    simpa [prefixWord, tailWord_7126650, baseEnd_7126650] using wordTrace_append hprefix tailTrace_7126650
  have hstable : (prefixWord ++ tailWord_7126650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126650).length < 2 ^ (prefixWord ++ tailWord_7126650).sum := by decide
  have hdescent : baseEnd_7126650 < baseStart_7126650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126667 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 4, 2]
def baseStart_7126667 : Nat := 118140960795 + 7126667 * 2 ^ 59
def prefixEnd_7126667 : Nat := 4983230072969 + 3 ^ 40 * 7126667 * 2
def baseEnd_7126667 : Nat := 3659405635535773616287561

theorem tailTrace_7126667 : CollatzResearch.WordTrace tailWord_7126667 prefixEnd_7126667 3659405635535773616287561 := by
  unfold tailWord_7126667
  simp only [CollatzResearch.WordTrace]
  refine ⟨259930899672310071667418255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173287266448206714444945503 259930899672310071667418255)
  ·
    refine ⟨389896349508465107501127383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259930899672310071667418255 389896349508465107501127383)
    ·
      refine ⟨584844524262697661251691075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389896349508465107501127383 584844524262697661251691075)
      ·
        refine ⟨877266786394046491877536613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584844524262697661251691075 877266786394046491877536613)
        ·
          refine ⟨164487522448883717227038115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877266786394046491877536613 164487522448883717227038115)
          ·
            refine ⟨246731283673325575840557173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164487522448883717227038115 246731283673325575840557173)
            ·
              refine ⟨23131057844374272735052235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246731283673325575840557173 23131057844374272735052235)
              ·
                refine ⟨34696586766561409102578353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23131057844374272735052235 34696586766561409102578353)
                ·
                  refine ⟨26022440074921056826933765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34696586766561409102578353 26022440074921056826933765)
                  ·
                    refine ⟨4879207514047698155050081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26022440074921056826933765 4879207514047698155050081)
                    ·
                      refine ⟨3659405635535773616287561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879207514047698155050081 3659405635535773616287561)
                      ·
                        rfl

theorem cell23_7126667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4, 2].length) (baseStart_7126667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126667 prefixEnd_7126667 := by exact prefixLift 7126667
  have htrace : WordTrace (prefixWord ++ tailWord_7126667) baseStart_7126667 baseEnd_7126667 := by
    simpa [prefixWord, tailWord_7126667, baseEnd_7126667] using wordTrace_append hprefix tailTrace_7126667
  have hstable : (prefixWord ++ tailWord_7126667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126667).length < 2 ^ (prefixWord ++ tailWord_7126667).sum := by decide
  have hdescent : baseEnd_7126667 < baseStart_7126667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126700 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_7126700 : Nat := 118140960795 + 7126700 * 2 ^ 59
def prefixEnd_7126700 : Nat := 4983230072969 + 3 ^ 40 * 7126700 * 2
def baseEnd_7126700 : Nat := 3659422580397371987174909

theorem tailTrace_7126700 : CollatzResearch.WordTrace tailWord_7126700 prefixEnd_7126700 3659422580397371987174909 := by
  unfold tailWord_7126700
  simp only [CollatzResearch.WordTrace]
  refine ⟨129966051640595259151684777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173288068854127012202246369 129966051640595259151684777)
  ·
    refine ⟨97474538730446444363763583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129966051640595259151684777 97474538730446444363763583)
    ·
      refine ⟨146211808095669666545645375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97474538730446444363763583 146211808095669666545645375)
      ·
        refine ⟨219317712143504499818468063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146211808095669666545645375 219317712143504499818468063)
        ·
          refine ⟨328976568215256749727702095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219317712143504499818468063 328976568215256749727702095)
          ·
            refine ⟨493464852322885124591553143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328976568215256749727702095 493464852322885124591553143)
            ·
              refine ⟨740197278484327686887329715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493464852322885124591553143 740197278484327686887329715)
              ·
                refine ⟨1110295917726491530330994573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740197278484327686887329715 1110295917726491530330994573)
                ·
                  refine ⟨416360969147434323874122965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110295917726491530330994573 416360969147434323874122965)
                  ·
                    refine ⟨9758460214392991965799757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 416360969147434323874122965 9758460214392991965799757)
                    ·
                      refine ⟨3659422580397371987174909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758460214392991965799757 3659422580397371987174909)
                      ·
                        rfl

theorem cell23_7126700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_7126700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126700 prefixEnd_7126700 := by exact prefixLift 7126700
  have htrace : WordTrace (prefixWord ++ tailWord_7126700) baseStart_7126700 baseEnd_7126700 := by
    simpa [prefixWord, tailWord_7126700, baseEnd_7126700] using wordTrace_append hprefix tailTrace_7126700
  have hstable : (prefixWord ++ tailWord_7126700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126700).length < 2 ^ (prefixWord ++ tailWord_7126700).sum := by decide
  have hdescent : baseEnd_7126700 < baseStart_7126700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126724 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 6]
def baseStart_7126724 : Nat := 118140960795 + 7126724 * 2 ^ 59
def prefixEnd_7126724 : Nat := 4983230072969 + 3 ^ 40 * 7126724 * 2
def baseEnd_7126724 : Nat := 406603878214786654808311

theorem tailTrace_7126724 : CollatzResearch.WordTrace tailWord_7126724 prefixEnd_7126724 406603878214786654808311 := by
  unfold tailWord_7126724
  simp only [CollatzResearch.WordTrace]
  refine ⟨129966489316551785201121613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173288652422069046934828817 129966489316551785201121613)
  ·
    refine ⟨48737433493706919450420605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129966489316551785201121613 48737433493706919450420605)
    ·
      refine ⟨18276537560140094793907727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48737433493706919450420605 18276537560140094793907727)
      ·
        refine ⟨27414806340210142190861591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276537560140094793907727 27414806340210142190861591)
        ·
          refine ⟨41122209510315213286292387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27414806340210142190861591 41122209510315213286292387)
          ·
            refine ⟨61683314265472819929438581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41122209510315213286292387 61683314265472819929438581)
            ·
              refine ⟨5782810712388076868384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61683314265472819929438581 5782810712388076868384867)
              ·
                refine ⟨8674216068582115302577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782810712388076868384867 8674216068582115302577301)
                ·
                  refine ⟨406603878214786654808311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8674216068582115302577301 406603878214786654808311)
                  ·
                    rfl

theorem cell23_7126724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_7126724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126724 prefixEnd_7126724 := by exact prefixLift 7126724
  have htrace : WordTrace (prefixWord ++ tailWord_7126724) baseStart_7126724 baseEnd_7126724 := by
    simpa [prefixWord, tailWord_7126724, baseEnd_7126724] using wordTrace_append hprefix tailTrace_7126724
  have hstable : (prefixWord ++ tailWord_7126724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126724).length < 2 ^ (prefixWord ++ tailWord_7126724).sum := by decide
  have hdescent : baseEnd_7126724 < baseStart_7126724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126727 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_7126727 : Nat := 118140960795 + 7126727 * 2 ^ 59
def prefixEnd_7126727 : Nat := 4983230072969 + 3 ^ 40 * 7126727 * 2
def baseEnd_7126727 : Nat := 3659436444375043381537285

theorem tailTrace_7126727 : CollatzResearch.WordTrace tailWord_7126727 prefixEnd_7126727 3659436444375043381537285 := by
  unfold tailWord_7126727
  simp only [CollatzResearch.WordTrace]
  refine ⟨259933088052092701914602435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173288725368061801276401623 259933088052092701914602435)
  ·
    refine ⟨389899632078139052871903653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259933088052092701914602435 389899632078139052871903653)
    ·
      refine ⟨73106181014651072413481935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389899632078139052871903653 73106181014651072413481935)
      ·
        refine ⟨109659271521976608620222903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73106181014651072413481935 109659271521976608620222903)
        ·
          refine ⟨164488907282964912930334355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109659271521976608620222903 164488907282964912930334355)
          ·
            refine ⟨246733360924447369395501533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164488907282964912930334355 246733360924447369395501533)
            ·
              refine ⟨92525010346667763523313075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246733360924447369395501533 92525010346667763523313075)
              ·
                refine ⟨138787515520001645284969613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92525010346667763523313075 138787515520001645284969613)
                ·
                  refine ⟨52045318320000616981863605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138787515520001645284969613 52045318320000616981863605)
                  ·
                    refine ⟨4879248592500057842049713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52045318320000616981863605 4879248592500057842049713)
                    ·
                      refine ⟨3659436444375043381537285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879248592500057842049713 3659436444375043381537285)
                      ·
                        rfl

theorem cell23_7126727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_7126727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126727 prefixEnd_7126727 := by exact prefixLift 7126727
  have htrace : WordTrace (prefixWord ++ tailWord_7126727) baseStart_7126727 baseEnd_7126727 := by
    simpa [prefixWord, tailWord_7126727, baseEnd_7126727] using wordTrace_append hprefix tailTrace_7126727
  have hstable : (prefixWord ++ tailWord_7126727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126727).length < 2 ^ (prefixWord ++ tailWord_7126727).sum := by decide
  have hdescent : baseEnd_7126727 < baseStart_7126727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126734 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_7126734 : Nat := 118140960795 + 7126734 * 2 ^ 59
def prefixEnd_7126734 : Nat := 4983230072969 + 3 ^ 40 * 7126734 * 2
def baseEnd_7126734 : Nat := 3659440038739624854149753

theorem tailTrace_7126734 : CollatzResearch.WordTrace tailWord_7126734 prefixEnd_7126734 3659440038739624854149753 := by
  unfold tailWord_7126734
  simp only [CollatzResearch.WordTrace]
  refine ⟨32491667920383417763763407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173288895575378228073404837 32491667920383417763763407)
  ·
    refine ⟨48737501880575126645645111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32491667920383417763763407 48737501880575126645645111)
    ·
      refine ⟨73106252820862689968467667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48737501880575126645645111 73106252820862689968467667)
      ·
        refine ⟨109659379231294034952701501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73106252820862689968467667 109659379231294034952701501)
        ·
          refine ⟨41122267211735263107263063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109659379231294034952701501 41122267211735263107263063)
          ·
            refine ⟨61683400817602894660894595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41122267211735263107263063 61683400817602894660894595)
            ·
              refine ⟨92525101226404341991341893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61683400817602894660894595 92525101226404341991341893)
              ·
                refine ⟨17348456479950814123376605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92525101226404341991341893 17348456479950814123376605)
                ·
                  refine ⟨6505671179981555296266227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17348456479950814123376605 6505671179981555296266227)
                  ·
                    refine ⟨9758506769972332944399341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6505671179981555296266227 9758506769972332944399341)
                    ·
                      refine ⟨3659440038739624854149753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758506769972332944399341 3659440038739624854149753)
                      ·
                        rfl

theorem cell23_7126734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_7126734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126734 prefixEnd_7126734 := by exact prefixLift 7126734
  have htrace : WordTrace (prefixWord ++ tailWord_7126734) baseStart_7126734 baseEnd_7126734 := by
    simpa [prefixWord, tailWord_7126734, baseEnd_7126734] using wordTrace_append hprefix tailTrace_7126734
  have hstable : (prefixWord ++ tailWord_7126734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126734).length < 2 ^ (prefixWord ++ tailWord_7126734).sum := by decide
  have hdescent : baseEnd_7126734 < baseStart_7126734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126737 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_7126737 : Nat := 118140960795 + 7126737 * 2 ^ 59
def prefixEnd_7126737 : Nat := 4983230072969 + 3 ^ 40 * 7126737 * 2
def baseEnd_7126737 : Nat := 1219813859727196114137413

theorem tailTrace_7126737 : CollatzResearch.WordTrace tailWord_7126737 prefixEnd_7126737 1219813859727196114137413 := by
  unfold tailWord_7126737
  simp only [CollatzResearch.WordTrace]
  refine ⟨259933452782056473622466465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173288968521370982414977643 259933452782056473622466465)
  ·
    refine ⟨194950089586542355216849849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259933452782056473622466465 194950089586542355216849849)
    ·
      refine ⟨146212567189906766412637387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194950089586542355216849849 146212567189906766412637387)
      ·
        refine ⟨219318850784860149618956081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146212567189906766412637387 219318850784860149618956081)
        ·
          refine ⟨164489138088645112214217061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219318850784860149618956081 164489138088645112214217061)
          ·
            refine ⟨30841713391620958540165699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164489138088645112214217061 30841713391620958540165699)
            ·
              refine ⟨46262570087431437810248549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30841713391620958540165699 46262570087431437810248549)
              ·
                refine ⟨8674231891393394589421603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46262570087431437810248549 8674231891393394589421603)
                ·
                  refine ⟨13011347837090091884132405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8674231891393394589421603 13011347837090091884132405)
                  ·
                    refine ⟨1219813859727196114137413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13011347837090091884132405 1219813859727196114137413)
                    ·
                      rfl

theorem cell23_7126737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_7126737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126737 prefixEnd_7126737 := by exact prefixLift 7126737
  have htrace : WordTrace (prefixWord ++ tailWord_7126737) baseStart_7126737 baseEnd_7126737 := by
    simpa [prefixWord, tailWord_7126737, baseEnd_7126737] using wordTrace_append hprefix tailTrace_7126737
  have hstable : (prefixWord ++ tailWord_7126737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126737).length < 2 ^ (prefixWord ++ tailWord_7126737).sum := by decide
  have hdescent : baseEnd_7126737 < baseStart_7126737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126744 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_7126744 : Nat := 118140960795 + 7126744 * 2 ^ 59
def prefixEnd_7126744 : Nat := 4983230072969 + 3 ^ 40 * 7126744 * 2
def baseEnd_7126744 : Nat := 3659445173546169815024707

theorem tailTrace_7126744 : CollatzResearch.WordTrace tailWord_7126744 prefixEnd_7126744 3659445173546169815024707 := by
  unfold tailWord_7126744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129966854046515556908985643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173289138728687409211980857 129966854046515556908985643)
  ·
    refine ⟨194950281069773335363478465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129966854046515556908985643 194950281069773335363478465)
    ·
      refine ⟨146212710802330001522608849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194950281069773335363478465 146212710802330001522608849)
      ·
        refine ⟨109659533101747501141956637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146212710802330001522608849 109659533101747501141956637)
        ·
          refine ⟨41122324913155312928233739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109659533101747501141956637 41122324913155312928233739)
          ·
            refine ⟨61683487369732969392350609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41122324913155312928233739 61683487369732969392350609)
            ·
              refine ⟨46262615527299727044262957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61683487369732969392350609 46262615527299727044262957)
              ·
                refine ⟨17348480822737397641598609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46262615527299727044262957 17348480822737397641598609)
                ·
                  refine ⟨13011360617053048231198957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17348480822737397641598609 13011360617053048231198957)
                  ·
                    refine ⟨4879260231394893086699609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13011360617053048231198957 4879260231394893086699609)
                    ·
                      refine ⟨3659445173546169815024707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879260231394893086699609 3659445173546169815024707)
                      ·
                        rfl

theorem cell23_7126744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_7126744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126744 prefixEnd_7126744 := by exact prefixLift 7126744
  have htrace : WordTrace (prefixWord ++ tailWord_7126744) baseStart_7126744 baseEnd_7126744 := by
    simpa [prefixWord, tailWord_7126744, baseEnd_7126744] using wordTrace_append hprefix tailTrace_7126744
  have hstable : (prefixWord ++ tailWord_7126744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126744).length < 2 ^ (prefixWord ++ tailWord_7126744).sum := by decide
  have hdescent : baseEnd_7126744 < baseStart_7126744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126767 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 4, 4]
def baseStart_7126767 : Nat := 118140960795 + 7126767 * 2 ^ 59
def prefixEnd_7126767 : Nat := 4983230072969 + 3 ^ 40 * 7126767 * 2
def baseEnd_7126767 : Nat := 1219818994533741075012367

theorem tailTrace_7126767 : CollatzResearch.WordTrace tailWord_7126767 prefixEnd_7126767 1219818994533741075012367 := by
  unfold tailWord_7126767
  simp only [CollatzResearch.WordTrace]
  refine ⟨259934546971947788746058555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173289697981298525830705703 259934546971947788746058555)
  ·
    refine ⟨389901820457921683119087833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259934546971947788746058555 389901820457921683119087833)
    ·
      refine ⟨292426365343441262339315875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389901820457921683119087833 292426365343441262339315875)
      ·
        refine ⟨438639548015161893508973813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292426365343441262339315875 438639548015161893508973813)
        ·
          refine ⟨41122457626421427516466295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 438639548015161893508973813 41122457626421427516466295)
          ·
            refine ⟨61683686439632141274699443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41122457626421427516466295 61683686439632141274699443)
            ·
              refine ⟨92525529659448211912049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61683686439632141274699443 92525529659448211912049165)
              ·
                refine ⟨34697073622293079467018437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92525529659448211912049165 34697073622293079467018437)
                ·
                  refine ⟨6505701304179952400065957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34697073622293079467018437 6505701304179952400065957)
                  ·
                    refine ⟨1219818994533741075012367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505701304179952400065957 1219818994533741075012367)
                    ·
                      rfl

theorem cell23_7126767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_7126767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126767 prefixEnd_7126767 := by exact prefixLift 7126767
  have htrace : WordTrace (prefixWord ++ tailWord_7126767) baseStart_7126767 baseEnd_7126767 := by
    simpa [prefixWord, tailWord_7126767, baseEnd_7126767] using wordTrace_append hprefix tailTrace_7126767
  have hstable : (prefixWord ++ tailWord_7126767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126767).length < 2 ^ (prefixWord ++ tailWord_7126767).sum := by decide
  have hdescent : baseEnd_7126767 < baseStart_7126767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126794 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_7126794 : Nat := 118140960795 + 7126794 * 2 ^ 59
def prefixEnd_7126794 : Nat := 4983230072969 + 3 ^ 40 * 7126794 * 2
def baseEnd_7126794 : Nat := 3659470847578894619399477

theorem tailTrace_7126794 : CollatzResearch.WordTrace tailWord_7126794 prefixEnd_7126794 3659470847578894619399477 := by
  unfold tailWord_7126794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64983882935712493089322859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173290354495233314904860957 64983882935712493089322859)
  ·
    refine ⟨97475824403568739633984289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64983882935712493089322859 97475824403568739633984289)
    ·
      refine ⟨73106868302676554725488217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97475824403568739633984289 73106868302676554725488217)
      ·
        refine ⟨54830151227007416044116163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73106868302676554725488217 54830151227007416044116163)
        ·
          refine ⟨82245226840511124066174245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54830151227007416044116163 82245226840511124066174245)
          ·
            refine ⟨15420980032595835762407671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82245226840511124066174245 15420980032595835762407671)
            ·
              refine ⟨23131470048893753643611507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15420980032595835762407671 23131470048893753643611507)
              ·
                refine ⟨34697205073340630465417261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23131470048893753643611507 34697205073340630465417261)
                ·
                  refine ⟨13011451902502736424531473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34697205073340630465417261 13011451902502736424531473)
                  ·
                    refine ⟨9758588926877052318398605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13011451902502736424531473 9758588926877052318398605)
                    ·
                      refine ⟨3659470847578894619399477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758588926877052318398605 3659470847578894619399477)
                      ·
                        rfl

theorem cell23_7126794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_7126794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126794 prefixEnd_7126794 := by exact prefixLift 7126794
  have htrace : WordTrace (prefixWord ++ tailWord_7126794) baseStart_7126794 baseEnd_7126794 := by
    simpa [prefixWord, tailWord_7126794, baseEnd_7126794] using wordTrace_append hprefix tailTrace_7126794
  have hstable : (prefixWord ++ tailWord_7126794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126794).length < 2 ^ (prefixWord ++ tailWord_7126794).sum := by decide
  have hdescent : baseEnd_7126794 < baseStart_7126794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126814 : List Nat := [4, 3, 2, 2, 12]
def baseStart_7126814 : Nat := 118140960795 + 7126814 * 2 ^ 59
def prefixEnd_7126814 : Nat := 4983230072969 + 3 ^ 40 * 7126814 * 2
def baseEnd_7126814 : Nat := 5019864358288044638065

theorem tailTrace_7126814 : CollatzResearch.WordTrace tailWord_7126814 prefixEnd_7126814 5019864358288044638065 := by
  unfold tailWord_7126814
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492032650347189471627437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173290840801851677182012997 32492032650347189471627437)
  ·
    refine ⟨12184512243880196051860289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32492032650347189471627437 12184512243880196051860289)
    ·
      refine ⟨9138384182910147038895217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12184512243880196051860289 9138384182910147038895217)
      ·
        refine ⟨6853788137182610279171413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9138384182910147038895217 6853788137182610279171413)
        ·
          refine ⟨5019864358288044638065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6853788137182610279171413 5019864358288044638065)
          ·
            rfl

theorem cell23_7126814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 12].length) (baseStart_7126814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126814 prefixEnd_7126814 := by exact prefixLift 7126814
  have htrace : WordTrace (prefixWord ++ tailWord_7126814) baseStart_7126814 baseEnd_7126814 := by
    simpa [prefixWord, tailWord_7126814, baseEnd_7126814] using wordTrace_append hprefix tailTrace_7126814
  have hstable : (prefixWord ++ tailWord_7126814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126814).length < 2 ^ (prefixWord ++ tailWord_7126814).sum := by decide
  have hdescent : baseEnd_7126814 < baseStart_7126814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126868 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_7126868 : Nat := 118140960795 + 7126868 * 2 ^ 59
def prefixEnd_7126868 : Nat := 4983230072969 + 3 ^ 40 * 7126868 * 2
def baseEnd_7126868 : Nat := 3659508845147327329874137

theorem tailTrace_7126868 : CollatzResearch.WordTrace tailWord_7126868 prefixEnd_7126868 3659508845147327329874137 := by
  unfold tailWord_7126868
  simp only [CollatzResearch.WordTrace]
  refine ⟨129969115372290941497742629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173292153829721255330323505 129969115372290941497742629)
  ·
    refine ⟨24369209132304551530826743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129969115372290941497742629 24369209132304551530826743)
    ·
      refine ⟨36553813698456827296240115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24369209132304551530826743 36553813698456827296240115)
      ·
        refine ⟨54830720547685240944360173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36553813698456827296240115 54830720547685240944360173)
        ·
          refine ⟨20561520205381965354135065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54830720547685240944360173 20561520205381965354135065)
          ·
            refine ⟨15421140154036474015601299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20561520205381965354135065 15421140154036474015601299)
            ·
              refine ⟨23131710231054711023401949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15421140154036474015601299 23131710231054711023401949)
              ·
                refine ⟨8674391336645516633775731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23131710231054711023401949 8674391336645516633775731)
                ·
                  refine ⟨13011587004968274950663597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8674391336645516633775731 13011587004968274950663597)
                  ·
                    refine ⟨4879345126863103106498849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13011587004968274950663597 4879345126863103106498849)
                    ·
                      refine ⟨3659508845147327329874137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879345126863103106498849 3659508845147327329874137)
                      ·
                        rfl

theorem cell23_7126868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_7126868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126868 prefixEnd_7126868 := by exact prefixLift 7126868
  have htrace : WordTrace (prefixWord ++ tailWord_7126868) baseStart_7126868 baseEnd_7126868 := by
    simpa [prefixWord, tailWord_7126868, baseEnd_7126868] using wordTrace_append hprefix tailTrace_7126868
  have hstable : (prefixWord ++ tailWord_7126868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126868).length < 2 ^ (prefixWord ++ tailWord_7126868).sum := by decide
  have hdescent : baseEnd_7126868 < baseStart_7126868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126881 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_7126881 : Nat := 118140960795 + 7126881 * 2 ^ 59
def prefixEnd_7126881 : Nat := 4983230072969 + 3 ^ 40 * 7126881 * 2
def baseEnd_7126881 : Nat := 3659515520395835779011577

theorem tailTrace_7126881 : CollatzResearch.WordTrace tailWord_7126881 prefixEnd_7126881 3659515520395835779011577 := by
  unfold tailWord_7126881
  simp only [CollatzResearch.WordTrace]
  refine ⟨259938704893534786215708497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173292469929023190810472331 259938704893534786215708497)
  ·
    refine ⟨194954028670151089661781373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259938704893534786215708497 194954028670151089661781373)
    ·
      refine ⟨73107760751306658623168015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194954028670151089661781373 73107760751306658623168015)
      ·
        refine ⟨109661641126959987934752023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73107760751306658623168015 109661641126959987934752023)
        ·
          refine ⟨164492461690439981902128035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109661641126959987934752023 164492461690439981902128035)
          ·
            refine ⟨246738692535659972853192053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164492461690439981902128035 246738692535659972853192053)
            ·
              refine ⟨23131752425218122454986755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246738692535659972853192053 23131752425218122454986755)
              ·
                refine ⟨34697628637827183682480133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23131752425218122454986755 34697628637827183682480133)
                ·
                  refine ⟨6505805369592596940465025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34697628637827183682480133 6505805369592596940465025)
                  ·
                    refine ⟨4879354027194447705348769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505805369592596940465025 4879354027194447705348769)
                    ·
                      refine ⟨3659515520395835779011577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879354027194447705348769 3659515520395835779011577)
                      ·
                        rfl

theorem cell23_7126881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_7126881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126881 prefixEnd_7126881 := by exact prefixLift 7126881
  have htrace : WordTrace (prefixWord ++ tailWord_7126881) baseStart_7126881 baseEnd_7126881 := by
    simpa [prefixWord, tailWord_7126881, baseEnd_7126881] using wordTrace_append hprefix tailTrace_7126881
  have hstable : (prefixWord ++ tailWord_7126881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126881).length < 2 ^ (prefixWord ++ tailWord_7126881).sum := by decide
  have hdescent : baseEnd_7126881 < baseStart_7126881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126917 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_7126917 : Nat := 118140960795 + 7126917 * 2 ^ 59
def prefixEnd_7126917 : Nat := 4983230072969 + 3 ^ 40 * 7126917 * 2
def baseEnd_7126917 : Nat := 1219844668566465879387137

theorem tailTrace_7126917 : CollatzResearch.WordTrace tailWord_7126917 prefixEnd_7126917 1219844668566465879387137 := by
  unfold tailWord_7126917
  simp only [CollatzResearch.WordTrace]
  refine ⟨259940017921404364364019005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173293345280936242909346003 259940017921404364364019005)
  ·
    refine ⟨97477506720526636636507127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259940017921404364364019005 97477506720526636636507127)
    ·
      refine ⟨146216260080789954954760691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97477506720526636636507127 146216260080789954954760691)
      ·
        refine ⟨219324390121184932432141037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146216260080789954954760691 219324390121184932432141037)
        ·
          refine ⟨82246646295444349662052889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219324390121184932432141037 82246646295444349662052889)
          ·
            refine ⟨61684984721583262246539667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82246646295444349662052889 61684984721583262246539667)
            ·
              refine ⟨92527477082374893369809501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61684984721583262246539667 92527477082374893369809501)
              ·
                refine ⟨34697803905890585013678563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92527477082374893369809501 34697803905890585013678563)
                ·
                  refine ⟨52046705858835877520517845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34697803905890585013678563 52046705858835877520517845)
                  ·
                    refine ⟨1219844668566465879387137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52046705858835877520517845 1219844668566465879387137)
                    ·
                      rfl

theorem cell23_7126917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_7126917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126917 prefixEnd_7126917 := by exact prefixLift 7126917
  have htrace : WordTrace (prefixWord ++ tailWord_7126917) baseStart_7126917 baseEnd_7126917 := by
    simpa [prefixWord, tailWord_7126917, baseEnd_7126917] using wordTrace_append hprefix tailTrace_7126917
  have hstable : (prefixWord ++ tailWord_7126917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126917).length < 2 ^ (prefixWord ++ tailWord_7126917).sum := by decide
  have hdescent : baseEnd_7126917 < baseStart_7126917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126924 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_7126924 : Nat := 118140960795 + 7126924 * 2 ^ 59
def prefixEnd_7126924 : Nat := 4983230072969 + 3 ^ 40 * 7126924 * 2
def baseEnd_7126924 : Nat := 3659537600063979110773879

theorem tailTrace_7126924 : CollatzResearch.WordTrace tailWord_7126924 prefixEnd_7126924 3659537600063979110773879 := by
  unfold tailWord_7126924
  simp only [CollatzResearch.WordTrace]
  refine ⟨129970136616189502279761913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173293515488252669706349217 129970136616189502279761913)
  ·
    refine ⟨97477602462142126709821435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129970136616189502279761913 97477602462142126709821435)
    ·
      refine ⟨146216403693213190064732153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97477602462142126709821435 146216403693213190064732153)
      ·
        refine ⟨109662302769909892548549115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146216403693213190064732153 109662302769909892548549115)
        ·
          refine ⟨164493454154864838822823673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109662302769909892548549115 164493454154864838822823673)
          ·
            refine ⟨123370090616148629117117755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164493454154864838822823673 123370090616148629117117755)
            ·
              refine ⟨185055135924222943675676633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123370090616148629117117755 185055135924222943675676633)
              ·
                refine ⟨138791351943167207756757475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185055135924222943675676633 138791351943167207756757475)
                ·
                  refine ⟨208187027914750811635136213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138791351943167207756757475 208187027914750811635136213)
                  ·
                    refine ⟨4879383466751972147698505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208187027914750811635136213 4879383466751972147698505)
                    ·
                      refine ⟨3659537600063979110773879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879383466751972147698505 3659537600063979110773879)
                      ·
                        rfl

theorem cell23_7126924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_7126924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126924 prefixEnd_7126924 := by exact prefixLift 7126924
  have htrace : WordTrace (prefixWord ++ tailWord_7126924) baseStart_7126924 baseEnd_7126924 := by
    simpa [prefixWord, tailWord_7126924, baseEnd_7126924] using wordTrace_append hprefix tailTrace_7126924
  have hstable : (prefixWord ++ tailWord_7126924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126924).length < 2 ^ (prefixWord ++ tailWord_7126924).sum := by decide
  have hdescent : baseEnd_7126924 < baseStart_7126924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126938 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_7126938 : Nat := 118140960795 + 7126938 * 2 ^ 59
def prefixEnd_7126938 : Nat := 4983230072969 + 3 ^ 40 * 7126938 * 2
def baseEnd_7126938 : Nat := 406616087643682450666535

theorem tailTrace_7126938 : CollatzResearch.WordTrace tailWord_7126938 prefixEnd_7126938 406616087643682450666535 := by
  unfold tailWord_7126938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64985195963582071237633367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173293855902885523300355645 64985195963582071237633367)
  ·
    refine ⟨97477793945373106856450051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64985195963582071237633367 97477793945373106856450051)
    ·
      refine ⟨146216690918059660284675077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97477793945373106856450051 146216690918059660284675077)
      ·
        refine ⟨27415629547136186303376577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146216690918059660284675077 27415629547136186303376577)
        ·
          refine ⟨20561722160352139727532433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27415629547136186303376577 20561722160352139727532433)
          ·
            refine ⟨15421291620264104795649325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20561722160352139727532433 15421291620264104795649325)
            ·
              refine ⟨5782984357599039298368497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15421291620264104795649325 5782984357599039298368497)
              ·
                refine ⟨4337238268199279473776373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782984357599039298368497 4337238268199279473776373)
                ·
                  refine ⟨406616087643682450666535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4337238268199279473776373 406616087643682450666535)
                  ·
                    rfl

theorem cell23_7126938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_7126938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126938 prefixEnd_7126938 := by exact prefixLift 7126938
  have htrace : WordTrace (prefixWord ++ tailWord_7126938) baseStart_7126938 baseEnd_7126938 := by
    simpa [prefixWord, tailWord_7126938, baseEnd_7126938] using wordTrace_append hprefix tailTrace_7126938
  have hstable : (prefixWord ++ tailWord_7126938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126938).length < 2 ^ (prefixWord ++ tailWord_7126938).sum := by decide
  have hdescent : baseEnd_7126938 < baseStart_7126938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126967 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_7126967 : Nat := 118140960795 + 7126967 * 2 ^ 59
def prefixEnd_7126967 : Nat := 4983230072969 + 3 ^ 40 * 7126967 * 2
def baseEnd_7126967 : Nat := 3659559679732122442536181

theorem tailTrace_7126967 : CollatzResearch.WordTrace tailWord_7126967 prefixEnd_7126967 3659559679732122442536181 := by
  unfold tailWord_7126967
  simp only [CollatzResearch.WordTrace]
  refine ⟨259941841571223222903339155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173294561047482148602226103 259941841571223222903339155)
  ·
    refine ⟨389912762356834834355008733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259941841571223222903339155 389912762356834834355008733)
    ·
      refine ⟨146217285883813062883128275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389912762356834834355008733 146217285883813062883128275)
      ·
        refine ⟨219325928825719594324692413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146217285883813062883128275 219325928825719594324692413)
        ·
          refine ⟨82247223309644847871759655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219325928825719594324692413 82247223309644847871759655)
          ·
            refine ⟨123370834964467271807639483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82247223309644847871759655 123370834964467271807639483)
            ·
              refine ⟨185056252446700907711459225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123370834964467271807639483 185056252446700907711459225)
              ·
                refine ⟨138792189335025680783594419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185056252446700907711459225 138792189335025680783594419)
                ·
                  refine ⟨208188284002538521175391629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138792189335025680783594419 208188284002538521175391629)
                  ·
                    refine ⟨78070606500951945440771861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208188284002538521175391629 78070606500951945440771861)
                    ·
                      refine ⟨3659559679732122442536181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78070606500951945440771861 3659559679732122442536181)
                      ·
                        rfl

theorem cell23_7126967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_7126967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126967 prefixEnd_7126967 := by exact prefixLift 7126967
  have htrace : WordTrace (prefixWord ++ tailWord_7126967) baseStart_7126967 baseEnd_7126967 := by
    simpa [prefixWord, tailWord_7126967, baseEnd_7126967] using wordTrace_append hprefix tailTrace_7126967
  have hstable : (prefixWord ++ tailWord_7126967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126967).length < 2 ^ (prefixWord ++ tailWord_7126967).sum := by decide
  have hdescent : baseEnd_7126967 < baseStart_7126967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127024 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_7127024 : Nat := 118140960795 + 7127024 * 2 ^ 59
def prefixEnd_7127024 : Nat := 4983230072969 + 3 ^ 40 * 7127024 * 2
def baseEnd_7127024 : Nat := 1219862982709809573174473

theorem tailTrace_7127024 : CollatzResearch.WordTrace tailWord_7127024 prefixEnd_7127024 1219862982709809573174473 := by
  unfold tailWord_7127024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129971960266008360819082063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173295947021344481092109417 129971960266008360819082063)
  ·
    refine ⟨194957940399012541228623095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129971960266008360819082063 194957940399012541228623095)
    ·
      refine ⟨292436910598518811842934643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194957940399012541228623095 292436910598518811842934643)
      ·
        refine ⟨438655365897778217764401965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292436910598518811842934643 438655365897778217764401965)
        ·
          refine ⟨164495762211666831661650737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438655365897778217764401965 164495762211666831661650737)
          ·
            refine ⟨123371821658750123746238053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164495762211666831661650737 123371821658750123746238053)
            ·
              refine ⟨23132216561015648202419635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123371821658750123746238053 23132216561015648202419635)
              ·
                refine ⟨34698324841523472303629453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23132216561015648202419635 34698324841523472303629453)
                ·
                  refine ⟨13011871815571302113861045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34698324841523472303629453 13011871815571302113861045)
                  ·
                    refine ⟨1219862982709809573174473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13011871815571302113861045 1219862982709809573174473)
                    ·
                      rfl

theorem cell23_7127024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_7127024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127024 prefixEnd_7127024 := by exact prefixLift 7127024
  have htrace : WordTrace (prefixWord ++ tailWord_7127024) baseStart_7127024 baseEnd_7127024 := by
    simpa [prefixWord, tailWord_7127024, baseEnd_7127024] using wordTrace_append hprefix tailTrace_7127024
  have hstable : (prefixWord ++ tailWord_7127024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127024).length < 2 ^ (prefixWord ++ tailWord_7127024).sum := by decide
  have hdescent : baseEnd_7127024 < baseStart_7127024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127025 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_7127025 : Nat := 118140960795 + 7127025 * 2 ^ 59
def prefixEnd_7127025 : Nat := 4983230072969 + 3 ^ 40 * 7127025 * 2
def baseEnd_7127025 : Nat := 3659589461610083215610915

theorem tailTrace_7127025 : CollatzResearch.WordTrace tailWord_7127025 prefixEnd_7127025 3659589461610083215610915 := by
  unfold tailWord_7127025
  simp only [CollatzResearch.WordTrace]
  refine ⟨259943957005013098808950529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173295971336675399205967019 259943957005013098808950529)
  ·
    refine ⟨194957967753759824106712897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259943957005013098808950529 194957967753759824106712897)
    ·
      refine ⟨146218475815319868080034673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194957967753759824106712897 146218475815319868080034673)
      ·
        refine ⟨109663856861489901060026005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146218475815319868080034673 109663856861489901060026005)
        ·
          refine ⟨5140493290382339112188719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109663856861489901060026005 5140493290382339112188719)
          ·
            refine ⟨7710739935573508668283079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140493290382339112188719 7710739935573508668283079)
            ·
              refine ⟨11566109903360263002424619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710739935573508668283079 11566109903360263002424619)
              ·
                refine ⟨17349164855040394503636929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566109903360263002424619 17349164855040394503636929)
                ·
                  refine ⟨13011873641280295877727697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17349164855040394503636929 13011873641280295877727697)
                  ·
                    refine ⟨9758905230960221908295773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13011873641280295877727697 9758905230960221908295773)
                    ·
                      refine ⟨3659589461610083215610915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9758905230960221908295773 3659589461610083215610915)
                      ·
                        rfl

theorem cell23_7127025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_7127025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127025 prefixEnd_7127025 := by exact prefixLift 7127025
  have htrace : WordTrace (prefixWord ++ tailWord_7127025) baseStart_7127025 baseEnd_7127025 := by
    simpa [prefixWord, tailWord_7127025, baseEnd_7127025] using wordTrace_append hprefix tailTrace_7127025
  have hstable : (prefixWord ++ tailWord_7127025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127025).length < 2 ^ (prefixWord ++ tailWord_7127025).sum := by decide
  have hdescent : baseEnd_7127025 < baseStart_7127025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127041 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7127041 : Nat := 118140960795 + 7127041 * 2 ^ 59
def prefixEnd_7127041 : Nat := 4983230072969 + 3 ^ 40 * 7127041 * 2
def baseEnd_7127041 : Nat := 1219865892433518384336947

theorem tailTrace_7127041 : CollatzResearch.WordTrace tailWord_7127041 prefixEnd_7127041 1219865892433518384336947 := by
  unfold tailWord_7127041
  simp only [CollatzResearch.WordTrace]
  refine ⟨259944540572955133541532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173296360381970089027688651 259944540572955133541532977)
  ·
    refine ⟨194958405429716350156149733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259944540572955133541532977 194958405429716350156149733)
    ·
      refine ⟨36554701018071815654278075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194958405429716350156149733 36554701018071815654278075)
      ·
        refine ⟨54832051527107723481417113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36554701018071815654278075 54832051527107723481417113)
        ·
          refine ⟨41124038645330792611062835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54832051527107723481417113 41124038645330792611062835)
          ·
            refine ⟨61686057967996188916594253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41124038645330792611062835 61686057967996188916594253)
            ·
              refine ⟨23132271737998570843722845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61686057967996188916594253 23132271737998570843722845)
              ·
                refine ⟨8674601901749464066396067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23132271737998570843722845 8674601901749464066396067)
                ·
                  refine ⟨13011902852624196099594101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8674601901749464066396067 13011902852624196099594101)
                  ·
                    refine ⟨1219865892433518384336947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13011902852624196099594101 1219865892433518384336947)
                    ·
                      rfl

theorem cell23_7127041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7127041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127041 prefixEnd_7127041 := by exact prefixLift 7127041
  have htrace : WordTrace (prefixWord ++ tailWord_7127041) baseStart_7127041 baseEnd_7127041 := by
    simpa [prefixWord, tailWord_7127041, baseEnd_7127041] using wordTrace_append hprefix tailTrace_7127041
  have hstable : (prefixWord ++ tailWord_7127041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127041).length < 2 ^ (prefixWord ++ tailWord_7127041).sum := by decide
  have hdescent : baseEnd_7127041 < baseStart_7127041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127114 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_7127114 : Nat := 118140960795 + 7127114 * 2 ^ 59
def prefixEnd_7127114 : Nat := 4983230072969 + 3 ^ 40 * 7127114 * 2
def baseEnd_7127114 : Nat := 1219878387129444455799335

theorem tailTrace_7127114 : CollatzResearch.WordTrace tailWord_7127114 prefixEnd_7127114 1219878387129444455799335 := by
  unfold tailWord_7127114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64986800775422666752235099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173298135401127111339293597 64986800775422666752235099)
  ·
    refine ⟨97480201163134000128352649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64986800775422666752235099 97480201163134000128352649)
    ·
      refine ⟨73110150872350500096264487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97480201163134000128352649 73110150872350500096264487)
      ·
        refine ⟨109665226308525750144396731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73110150872350500096264487 109665226308525750144396731)
        ·
          refine ⟨164497839462788625216595097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109665226308525750144396731 164497839462788625216595097)
          ·
            refine ⟨123373379597091468912446323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164497839462788625216595097 123373379597091468912446323)
            ·
              refine ⟨185060069395637203368669485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123373379597091468912446323 185060069395637203368669485)
              ·
                refine ⟨69397526023363951263251057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185060069395637203368669485 69397526023363951263251057)
                ·
                  refine ⟨52048144517522963447438293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69397526023363951263251057 52048144517522963447438293)
                  ·
                    refine ⟨1219878387129444455799335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52048144517522963447438293 1219878387129444455799335)
                    ·
                      rfl

theorem cell23_7127114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_7127114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127114 prefixEnd_7127114 := by exact prefixLift 7127114
  have htrace : WordTrace (prefixWord ++ tailWord_7127114) baseStart_7127114 baseEnd_7127114 := by
    simpa [prefixWord, tailWord_7127114, baseEnd_7127114] using wordTrace_append hprefix tailTrace_7127114
  have hstable : (prefixWord ++ tailWord_7127114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127114).length < 2 ^ (prefixWord ++ tailWord_7127114).sum := by decide
  have hdescent : baseEnd_7127114 < baseStart_7127114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127121 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_7127121 : Nat := 118140960795 + 7127121 * 2 ^ 59
def prefixEnd_7127121 : Nat := 4983230072969 + 3 ^ 40 * 7127121 * 2
def baseEnd_7127121 : Nat := 3659638755752914840010473

theorem tailTrace_7127121 : CollatzResearch.WordTrace tailWord_7127121 prefixEnd_7127121 3659638755752914840010473 := by
  unfold tailWord_7127121
  simp only [CollatzResearch.WordTrace]
  refine ⟨259947458412665307204445217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173298305608443538136296811 259947458412665307204445217)
  ·
    refine ⟨194960593809498980403333913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259947458412665307204445217 194960593809498980403333913)
    ·
      refine ⟨146220445357124235302500435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194960593809498980403333913 146220445357124235302500435)
      ·
        refine ⟨219330668035686352953750653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146220445357124235302500435 219330668035686352953750653)
        ·
          refine ⟨82249000513382382357656495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219330668035686352953750653 82249000513382382357656495)
          ·
            refine ⟨123373500770073573536484743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82249000513382382357656495 123373500770073573536484743)
            ·
              refine ⟨185060251155110360304727115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123373500770073573536484743 185060251155110360304727115)
              ·
                refine ⟨277590376732665540457090673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185060251155110360304727115 277590376732665540457090673)
                ·
                  refine ⟨208192782549499155342818005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277590376732665540457090673 208192782549499155342818005)
                  ·
                    refine ⟨4879518341003886453347297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208192782549499155342818005 4879518341003886453347297)
                    ·
                      refine ⟨3659638755752914840010473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879518341003886453347297 3659638755752914840010473)
                      ·
                        rfl

theorem cell23_7127121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_7127121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127121 prefixEnd_7127121 := by exact prefixLift 7127121
  have htrace : WordTrace (prefixWord ++ tailWord_7127121) baseStart_7127121 baseEnd_7127121 := by
    simpa [prefixWord, tailWord_7127121, baseEnd_7127121] using wordTrace_append hprefix tailTrace_7127121
  have hstable : (prefixWord ++ tailWord_7127121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127121).length < 2 ^ (prefixWord ++ tailWord_7127121).sum := by decide
  have hdescent : baseEnd_7127121 < baseStart_7127121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127122 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7127122 : Nat := 118140960795 + 7127122 * 2 ^ 59
def prefixEnd_7127122 : Nat := 4983230072969 + 3 ^ 40 * 7127122 * 2
def baseEnd_7127122 : Nat := 1219879756411189778699323

theorem tailTrace_7127122 : CollatzResearch.WordTrace tailWord_7127122 prefixEnd_7127122 1219879756411189778699323 := by
  unfold tailWord_7127122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64986873721415421093807905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173298329923774456250154413 64986873721415421093807905)
  ·
    refine ⟨48740155291061565820355929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64986873721415421093807905 48740155291061565820355929)
    ·
      refine ⟨36555116468296174365266947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48740155291061565820355929 36555116468296174365266947)
      ·
        refine ⟨54832674702444261547900421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36555116468296174365266947 54832674702444261547900421)
        ·
          refine ⟨10281126506708299040231329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54832674702444261547900421 10281126506708299040231329)
          ·
            refine ⟨7710844880031224280173497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281126506708299040231329 7710844880031224280173497)
            ·
              refine ⟨5783133660023418210130123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7710844880031224280173497 5783133660023418210130123)
              ·
                refine ⟨8674700490035127315195185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783133660023418210130123 8674700490035127315195185)
                ·
                  refine ⟨6506025367526345486396389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674700490035127315195185 6506025367526345486396389)
                  ·
                    refine ⟨1219879756411189778699323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506025367526345486396389 1219879756411189778699323)
                    ·
                      rfl

theorem cell23_7127122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7127122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127122 prefixEnd_7127122 := by exact prefixLift 7127122
  have htrace : WordTrace (prefixWord ++ tailWord_7127122) baseStart_7127122 baseEnd_7127122 := by
    simpa [prefixWord, tailWord_7127122, baseEnd_7127122] using wordTrace_append hprefix tailTrace_7127122
  have hstable : (prefixWord ++ tailWord_7127122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127122).length < 2 ^ (prefixWord ++ tailWord_7127122).sum := by decide
  have hdescent : baseEnd_7127122 < baseStart_7127122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127171 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3]
def baseStart_7127171 : Nat := 118140960795 + 7127171 * 2 ^ 59
def prefixEnd_7127171 : Nat := 4983230072969 + 3 ^ 40 * 7127171 * 2
def baseEnd_7127171 : Nat := 3659664429785639644385243

theorem tailTrace_7127171 : CollatzResearch.WordTrace tailWord_7127171 prefixEnd_7127171 3659664429785639644385243 := by
  unfold tailWord_7127171
  simp only [CollatzResearch.WordTrace]
  refine ⟨259949282062484165743765367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173299521374989443829176911 259949282062484165743765367)
  ·
    refine ⟨389923923093726248615648051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259949282062484165743765367 389923923093726248615648051)
    ·
      refine ⟨584885884640589372923472077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389923923093726248615648051 584885884640589372923472077)
      ·
        refine ⟨219332206740221014846302029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584885884640589372923472077 219332206740221014846302029)
        ·
          refine ⟨82249577527582880567363261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219332206740221014846302029 82249577527582880567363261)
          ·
            refine ⟨30843591572843580212761223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82249577527582880567363261 30843591572843580212761223)
            ·
              refine ⟨46265387359265370319141835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30843591572843580212761223 46265387359265370319141835)
              ·
                refine ⟨69398081038898055478712753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46265387359265370319141835 69398081038898055478712753)
                ·
                  refine ⟨52048560779173541609034565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69398081038898055478712753 52048560779173541609034565)
                  ·
                    refine ⟨9759105146095039051693981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52048560779173541609034565 9759105146095039051693981)
                    ·
                      refine ⟨3659664429785639644385243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9759105146095039051693981 3659664429785639644385243)
                      ·
                        rfl

theorem cell23_7127171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_7127171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127171 prefixEnd_7127171 := by exact prefixLift 7127171
  have htrace : WordTrace (prefixWord ++ tailWord_7127171) baseStart_7127171 baseEnd_7127171 := by
    simpa [prefixWord, tailWord_7127171, baseEnd_7127171] using wordTrace_append hprefix tailTrace_7127171
  have hstable : (prefixWord ++ tailWord_7127171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127171).length < 2 ^ (prefixWord ++ tailWord_7127171).sum := by decide
  have hdescent : baseEnd_7127171 < baseStart_7127171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127241 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_7127241 : Nat := 118140960795 + 7127241 * 2 ^ 59
def prefixEnd_7127241 : Nat := 4983230072969 + 3 ^ 40 * 7127241 * 2
def baseEnd_7127241 : Nat := 3659700373431454370509921

theorem tailTrace_7127241 : CollatzResearch.WordTrace tailWord_7127241 prefixEnd_7127241 3659700373431454370509921 := by
  unfold tailWord_7127241
  simp only [CollatzResearch.WordTrace]
  refine ⟨259951835172230567698813577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173301223448153711799209051 259951835172230567698813577)
  ·
    refine ⟨194963876379172925774110183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259951835172230567698813577 194963876379172925774110183)
    ·
      refine ⟨292445814568759388661165275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194963876379172925774110183 292445814568759388661165275)
      ·
        refine ⟨438668721853139082991747913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292445814568759388661165275 438668721853139082991747913)
        ·
          refine ⟨329001541389854312243810935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438668721853139082991747913 329001541389854312243810935)
          ·
            refine ⟨493502312084781468365716403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329001541389854312243810935 493502312084781468365716403)
            ·
              refine ⟨740253468127172202548574605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493502312084781468365716403 740253468127172202548574605)
              ·
                refine ⟨277595050547689575955715477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740253468127172202548574605 277595050547689575955715477)
                ·
                  refine ⟨13012267994422948872924163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277595050547689575955715477 13012267994422948872924163)
                  ·
                    refine ⟨19518401991634423309386245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13012267994422948872924163 19518401991634423309386245)
                    ·
                      refine ⟨3659700373431454370509921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19518401991634423309386245 3659700373431454370509921)
                      ·
                        rfl

theorem cell23_7127241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_7127241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127241 prefixEnd_7127241 := by exact prefixLift 7127241
  have htrace : WordTrace (prefixWord ++ tailWord_7127241) baseStart_7127241 baseEnd_7127241 := by
    simpa [prefixWord, tailWord_7127241, baseEnd_7127241] using wordTrace_append hprefix tailTrace_7127241
  have hstable : (prefixWord ++ tailWord_7127241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127241).length < 2 ^ (prefixWord ++ tailWord_7127241).sum := by decide
  have hdescent : baseEnd_7127241 < baseStart_7127241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127258 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_7127258 : Nat := 118140960795 + 7127258 * 2 ^ 59
def prefixEnd_7127258 : Nat := 4983230072969 + 3 ^ 40 * 7127258 * 2
def baseEnd_7127258 : Nat := 3659709102602580803997343

theorem tailTrace_7127258 : CollatzResearch.WordTrace tailWord_7127258 prefixEnd_7127258 3659709102602580803997343 := by
  unfold tailWord_7127258
  simp only [CollatzResearch.WordTrace]
  refine ⟨64988113803292244900545607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173301636808779319734788285 64988113803292244900545607)
  ·
    refine ⟨97482170704938367350818411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64988113803292244900545607 97482170704938367350818411)
    ·
      refine ⟨146223256057407551026227617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97482170704938367350818411 146223256057407551026227617)
      ·
        refine ⟨109667442043055663269670713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146223256057407551026227617 109667442043055663269670713)
        ·
          refine ⟨82250581532291747452253035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109667442043055663269670713 82250581532291747452253035)
          ·
            refine ⟨123375872298437621178379553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82250581532291747452253035 123375872298437621178379553)
            ·
              refine ⟨92531904223828215883784665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123375872298437621178379553 92531904223828215883784665)
              ·
                refine ⟨69398928167871161912838499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92531904223828215883784665 69398928167871161912838499)
                ·
                  refine ⟨104098392251806742869257749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69398928167871161912838499 104098392251806742869257749)
                  ·
                    refine ⟨4879612136803441071996457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104098392251806742869257749 4879612136803441071996457)
                    ·
                      refine ⟨3659709102602580803997343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879612136803441071996457 3659709102602580803997343)
                      ·
                        rfl

theorem cell23_7127258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_7127258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127258 prefixEnd_7127258 := by exact prefixLift 7127258
  have htrace : WordTrace (prefixWord ++ tailWord_7127258) baseStart_7127258 baseEnd_7127258 := by
    simpa [prefixWord, tailWord_7127258, baseEnd_7127258] using wordTrace_append hprefix tailTrace_7127258
  have hstable : (prefixWord ++ tailWord_7127258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127258).length < 2 ^ (prefixWord ++ tailWord_7127258).sum := by decide
  have hdescent : baseEnd_7127258 < baseStart_7127258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127281 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 8]
def baseStart_7127281 : Nat := 118140960795 + 7127281 * 2 ^ 59
def prefixEnd_7127281 : Nat := 4983230072969 + 3 ^ 40 * 7127281 * 2
def baseEnd_7127281 : Nat := 406635656961959357112193

theorem tailTrace_7127281 : CollatzResearch.WordTrace tailWord_7127281 prefixEnd_7127281 406635656961959357112193 := by
  unfold tailWord_7127281
  simp only [CollatzResearch.WordTrace]
  refine ⟨259953294092085654530269697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173302196061390436353513131 259953294092085654530269697)
  ·
    refine ⟨194964970569064240897702273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259953294092085654530269697 194964970569064240897702273)
    ·
      refine ⟨146223727926798180673276705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194964970569064240897702273 146223727926798180673276705)
      ·
        refine ⟨109667795945098635504957529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146223727926798180673276705 109667795945098635504957529)
        ·
          refine ⟨82250846958823976628718147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109667795945098635504957529 82250846958823976628718147)
          ·
            refine ⟨123376270438235964943077221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82250846958823976628718147 123376270438235964943077221)
            ·
              refine ⟨23133050707169243426826979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123376270438235964943077221 23133050707169243426826979)
              ·
                refine ⟨34699576060753865140240469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23133050707169243426826979 34699576060753865140240469)
                ·
                  refine ⟨406635656961959357112193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34699576060753865140240469 406635656961959357112193)
                  ·
                    rfl

theorem cell23_7127281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_7127281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127281 prefixEnd_7127281 := by exact prefixLift 7127281
  have htrace : WordTrace (prefixWord ++ tailWord_7127281) baseStart_7127281 baseEnd_7127281 := by
    simpa [prefixWord, tailWord_7127281, baseEnd_7127281] using wordTrace_append hprefix tailTrace_7127281
  have hstable : (prefixWord ++ tailWord_7127281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127281).length < 2 ^ (prefixWord ++ tailWord_7127281).sum := by decide
  have hdescent : baseEnd_7127281 < baseStart_7127281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127336 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7127336 : Nat := 118140960795 + 7127336 * 2 ^ 59
def prefixEnd_7127336 : Nat := 4983230072969 + 3 ^ 40 * 7127336 * 2
def baseEnd_7127336 : Nat := 1219916384697877166273995

theorem tailTrace_7127336 : CollatzResearch.WordTrace tailWord_7127336 prefixEnd_7127336 1219916384697877166273995 := by
  unfold tailWord_7127336
  simp only [CollatzResearch.WordTrace]
  refine ⟨129977650053443199461760931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173303533404590932615681241 129977650053443199461760931)
  ·
    refine ⟨194966475080164799192641397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129977650053443199461760931 194966475080164799192641397)
    ·
      refine ⟨18278107038765449924310131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194966475080164799192641397 18278107038765449924310131)
      ·
        refine ⟨27417160558148174886465197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18278107038765449924310131 27417160558148174886465197)
        ·
          refine ⟨10281435209305565582424449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27417160558148174886465197 10281435209305565582424449)
          ·
            refine ⟨7711076406979174186818337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281435209305565582424449 7711076406979174186818337)
            ·
              refine ⟨5783307305234380640113753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7711076406979174186818337 5783307305234380640113753)
              ·
                refine ⟨4337480478925785480085315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783307305234380640113753 4337480478925785480085315)
                ·
                  refine ⟨6506220718388678220127973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337480478925785480085315 6506220718388678220127973)
                  ·
                    refine ⟨1219916384697877166273995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506220718388678220127973 1219916384697877166273995)
                    ·
                      rfl

theorem cell23_7127336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7127336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127336 prefixEnd_7127336 := by exact prefixLift 7127336
  have htrace : WordTrace (prefixWord ++ tailWord_7127336) baseStart_7127336 baseEnd_7127336 := by
    simpa [prefixWord, tailWord_7127336, baseEnd_7127336] using wordTrace_append hprefix tailTrace_7127336
  have hstable : (prefixWord ++ tailWord_7127336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127336).length < 2 ^ (prefixWord ++ tailWord_7127336).sum := by decide
  have hdescent : baseEnd_7127336 < baseStart_7127336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127399 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_7127399 : Nat := 118140960795 + 7127399 * 2 ^ 59
def prefixEnd_7127399 : Nat := 4983230072969 + 3 ^ 40 * 7127399 * 2
def baseEnd_7127399 : Nat := 3659781503374864752334195

theorem tailTrace_7127399 : CollatzResearch.WordTrace tailWord_7127399 prefixEnd_7127399 3659781503374864752334195 := by
  unfold tailWord_7127399
  simp only [CollatzResearch.WordTrace]
  refine ⟨259957597905658160683065251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173305065270438773788710167 259957597905658160683065251)
  ·
    refine ⟨389936396858487241024597877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259957597905658160683065251 389936396858487241024597877)
    ·
      refine ⟨36556537205483178846056051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389936396858487241024597877 36556537205483178846056051)
      ·
        refine ⟨54834805808224768269084077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36556537205483178846056051 54834805808224768269084077)
        ·
          refine ⟨20563052178084288100906529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54834805808224768269084077 20563052178084288100906529)
          ·
            refine ⟨15422289133563216075679897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20563052178084288100906529 15422289133563216075679897)
            ·
              refine ⟨11566716850172412056759923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15422289133563216075679897 11566716850172412056759923)
              ·
                refine ⟨17350075275258618085139885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566716850172412056759923 17350075275258618085139885)
                ·
                  refine ⟨6506278228221981781927457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17350075275258618085139885 6506278228221981781927457)
                  ·
                    refine ⟨4879708671166486336445593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6506278228221981781927457 4879708671166486336445593)
                    ·
                      refine ⟨3659781503374864752334195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879708671166486336445593 3659781503374864752334195)
                      ·
                        rfl

theorem cell23_7127399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_7127399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127399 prefixEnd_7127399 := by exact prefixLift 7127399
  have htrace : WordTrace (prefixWord ++ tailWord_7127399) baseStart_7127399 baseEnd_7127399 := by
    simpa [prefixWord, tailWord_7127399, baseEnd_7127399] using wordTrace_append hprefix tailTrace_7127399
  have hstable : (prefixWord ++ tailWord_7127399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127399).length < 2 ^ (prefixWord ++ tailWord_7127399).sum := by decide
  have hdescent : baseEnd_7127399 < baseStart_7127399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127428 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7127428 : Nat := 118140960795 + 7127428 * 2 ^ 59
def prefixEnd_7127428 : Nat := 4983230072969 + 3 ^ 40 * 7127428 * 2
def baseEnd_7127428 : Nat := 3659796394313845138871561

theorem tailTrace_7127428 : CollatzResearch.WordTrace tailWord_7127428 prefixEnd_7127428 3659796394313845138871561 := by
  unfold tailWord_7127428
  simp only [CollatzResearch.WordTrace]
  refine ⟨129979327811276549317935469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173305770415035399090580625 129979327811276549317935469)
  ·
    refine ⟨48742247929228705994225801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129979327811276549317935469 48742247929228705994225801)
    ·
      refine ⟨36556685946921529495669351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48742247929228705994225801 36556685946921529495669351)
      ·
        refine ⟨54835028920382294243504027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36556685946921529495669351 54835028920382294243504027)
        ·
          refine ⟨82252543380573441365256041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54835028920382294243504027 82252543380573441365256041)
          ·
            refine ⟨61689407535430081023942031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82252543380573441365256041 61689407535430081023942031)
            ·
              refine ⟨92534111303145121535913047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61689407535430081023942031 92534111303145121535913047)
              ·
                refine ⟨138801166954717682303869571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92534111303145121535913047 138801166954717682303869571)
                ·
                  refine ⟨208201750432076523455804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138801166954717682303869571 208201750432076523455804357)
                  ·
                    refine ⟨39037828206014348147963317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208201750432076523455804357 39037828206014348147963317)
                    ·
                      refine ⟨3659796394313845138871561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39037828206014348147963317 3659796394313845138871561)
                      ·
                        rfl

theorem cell23_7127428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7127428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127428 prefixEnd_7127428 := by exact prefixLift 7127428
  have htrace : WordTrace (prefixWord ++ tailWord_7127428) baseStart_7127428 baseEnd_7127428 := by
    simpa [prefixWord, tailWord_7127428, baseEnd_7127428] using wordTrace_append hprefix tailTrace_7127428
  have hstable : (prefixWord ++ tailWord_7127428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127428).length < 2 ^ (prefixWord ++ tailWord_7127428).sum := by decide
  have hdescent : baseEnd_7127428 < baseStart_7127428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127468 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_7127468 : Nat := 118140960795 + 7127468 * 2 ^ 59
def prefixEnd_7127468 : Nat := 4983230072969 + 3 ^ 40 * 7127468 * 2
def baseEnd_7127468 : Nat := 3659816933540024982371377

theorem tailTrace_7127468 : CollatzResearch.WordTrace tailWord_7127468 prefixEnd_7127468 3659816933540024982371377 := by
  unfold tailWord_7127468
  simp only [CollatzResearch.WordTrace]
  refine ⟨129980057271204092733663529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173306743028272123644884705 129980057271204092733663529)
  ·
    refine ⟨97485042953403069550247647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129980057271204092733663529 97485042953403069550247647)
    ·
      refine ⟨146227564430104604325371471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97485042953403069550247647 146227564430104604325371471)
      ·
        refine ⟨219341346645156906488057207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146227564430104604325371471 219341346645156906488057207)
        ·
          refine ⟨329012019967735359732085811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219341346645156906488057207 329012019967735359732085811)
          ·
            refine ⟨493518029951603039598128717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329012019967735359732085811 493518029951603039598128717)
            ·
              refine ⟨185069261231851139849298269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493518029951603039598128717 185069261231851139849298269)
              ·
                refine ⟨69400972961944177443486851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185069261231851139849298269 69400972961944177443486851)
                ·
                  refine ⟨104101459442916266165230277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69400972961944177443486851 104101459442916266165230277)
                  ·
                    refine ⟨19519023645546799905980677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104101459442916266165230277 19519023645546799905980677)
                    ·
                      refine ⟨3659816933540024982371377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19519023645546799905980677 3659816933540024982371377)
                      ·
                        rfl

theorem cell23_7127468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_7127468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127468 prefixEnd_7127468 := by exact prefixLift 7127468
  have htrace : WordTrace (prefixWord ++ tailWord_7127468) baseStart_7127468 baseEnd_7127468 := by
    simpa [prefixWord, tailWord_7127468, baseEnd_7127468] using wordTrace_append hprefix tailTrace_7127468
  have hstable : (prefixWord ++ tailWord_7127468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127468).length < 2 ^ (prefixWord ++ tailWord_7127468).sum := by decide
  have hdescent : baseEnd_7127468 < baseStart_7127468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127555 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 5, 4]
def baseStart_7127555 : Nat := 118140960795 + 7127555 * 2 ^ 59
def prefixEnd_7127555 : Nat := 4983230072969 + 3 ^ 40 * 7127555 * 2
def baseEnd_7127555 : Nat := 1219953868785655380661159

theorem tailTrace_7127555 : CollatzResearch.WordTrace tailWord_7127555 prefixEnd_7127555 1219953868785655380661159 := by
  unfold tailWord_7127555
  simp only [CollatzResearch.WordTrace]
  refine ⟨259963287693092999325744119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173308858462061999550496079 259963287693092999325744119)
  ·
    refine ⟨389944931539639498988616179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259963287693092999325744119 389944931539639498988616179)
    ·
      refine ⟨584917397309459248482924269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389944931539639498988616179 584917397309459248482924269)
      ·
        refine ⟨219344023991047218181096601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584917397309459248482924269 219344023991047218181096601)
        ·
          refine ⟨164508017993285413635822451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219344023991047218181096601 164508017993285413635822451)
          ·
            refine ⟨246762026989928120453733677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164508017993285413635822451 246762026989928120453733677)
            ·
              refine ⟨92535760121223045170150129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246762026989928120453733677 92535760121223045170150129)
              ·
                refine ⟨69401820090917283877612597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92535760121223045170150129 69401820090917283877612597)
                ·
                  refine ⟨6506420633523495363526181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69401820090917283877612597 6506420633523495363526181)
                  ·
                    refine ⟨1219953868785655380661159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506420633523495363526181 1219953868785655380661159)
                    ·
                      rfl

theorem cell23_7127555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 4].length) (baseStart_7127555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127555 prefixEnd_7127555 := by exact prefixLift 7127555
  have htrace : WordTrace (prefixWord ++ tailWord_7127555) baseStart_7127555 baseEnd_7127555 := by
    simpa [prefixWord, tailWord_7127555, baseEnd_7127555] using wordTrace_append hprefix tailTrace_7127555
  have hstable : (prefixWord ++ tailWord_7127555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127555).length < 2 ^ (prefixWord ++ tailWord_7127555).sum := by decide
  have hdescent : baseEnd_7127555 < baseStart_7127555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127562 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_7127562 : Nat := 118140960795 + 7127562 * 2 ^ 59
def prefixEnd_7127562 : Nat := 4983230072969 + 3 ^ 40 * 7127562 * 2
def baseEnd_7127562 : Nat := 3659865200721547614595945

theorem tailTrace_7127562 : CollatzResearch.WordTrace tailWord_7127562 prefixEnd_7127562 3659865200721547614595945 := by
  unfold tailWord_7127562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64990885751016909880312235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173309028669378426347499293 64990885751016909880312235)
  ·
    refine ⟨97486328626525364820468353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64990885751016909880312235 97486328626525364820468353)
    ·
      refine ⟨73114746469894023615351265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97486328626525364820468353 73114746469894023615351265)
      ·
        refine ⟨54836059852420517711513449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73114746469894023615351265 54836059852420517711513449)
        ·
          refine ⟨41127044889315388283635087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54836059852420517711513449 41127044889315388283635087)
          ·
            refine ⟨61690567333973082425452631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41127044889315388283635087 61690567333973082425452631)
            ·
              refine ⟨92535851000959623638178947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61690567333973082425452631 92535851000959623638178947)
              ·
                refine ⟨138803776501439435457268421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92535851000959623638178947 138803776501439435457268421)
                ·
                  refine ⟨26025708094019894148237829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138803776501439435457268421 26025708094019894148237829)
                  ·
                    refine ⟨4879820267628730152794593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26025708094019894148237829 4879820267628730152794593)
                    ·
                      refine ⟨3659865200721547614595945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879820267628730152794593 3659865200721547614595945)
                      ·
                        rfl

theorem cell23_7127562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_7127562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127562 prefixEnd_7127562 := by exact prefixLift 7127562
  have htrace : WordTrace (prefixWord ++ tailWord_7127562) baseStart_7127562 baseEnd_7127562 := by
    simpa [prefixWord, tailWord_7127562, baseEnd_7127562] using wordTrace_append hprefix tailTrace_7127562
  have hstable : (prefixWord ++ tailWord_7127562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127562).length < 2 ^ (prefixWord ++ tailWord_7127562).sum := by decide
  have hdescent : baseEnd_7127562 < baseStart_7127562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127649 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_7127649 : Nat := 118140960795 + 7127649 * 2 ^ 59
def prefixEnd_7127649 : Nat := 4983230072969 + 3 ^ 40 * 7127649 * 2
def baseEnd_7127649 : Nat := 1219969957846162924736015

theorem tailTrace_7127649 : CollatzResearch.WordTrace tailWord_7127649 prefixEnd_7127649 1219969957846162924736015 := by
  unfold tailWord_7127649
  simp only [CollatzResearch.WordTrace]
  refine ⟨259966716154752453379666001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173311144103168302253110667 259966716154752453379666001)
  ·
    refine ⟨194975037116064340034749501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259966716154752453379666001 194975037116064340034749501)
    ·
      refine ⟨73115638918524127513031063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194975037116064340034749501 73115638918524127513031063)
      ·
        refine ⟨109673458377786191269546595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73115638918524127513031063 109673458377786191269546595)
        ·
          refine ⟨164510187566679286904319893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109673458377786191269546595 164510187566679286904319893)
          ·
            refine ⟨7711415042188091573639995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164510187566679286904319893 7711415042188091573639995)
            ·
              refine ⟨11567122563282137360459993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7711415042188091573639995 11567122563282137360459993)
              ·
                refine ⟨8675341922461603020344995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11567122563282137360459993 8675341922461603020344995)
                ·
                  refine ⟨13013012883692404530517493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675341922461603020344995 13013012883692404530517493)
                  ·
                    refine ⟨1219969957846162924736015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013012883692404530517493 1219969957846162924736015)
                    ·
                      rfl

theorem cell23_7127649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_7127649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127649 prefixEnd_7127649 := by exact prefixLift 7127649
  have htrace : WordTrace (prefixWord ++ tailWord_7127649) baseStart_7127649 baseEnd_7127649 := by
    simpa [prefixWord, tailWord_7127649, baseEnd_7127649] using wordTrace_append hprefix tailTrace_7127649
  have hstable : (prefixWord ++ tailWord_7127649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127649).length < 2 ^ (prefixWord ++ tailWord_7127649).sum := by decide
  have hdescent : baseEnd_7127649 < baseStart_7127649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127652 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_7127652 : Nat := 118140960795 + 7127652 * 2 ^ 59
def prefixEnd_7127652 : Nat := 4983230072969 + 3 ^ 40 * 7127652 * 2
def baseEnd_7127652 : Nat := 3659911413980452262470531

theorem tailTrace_7127652 : CollatzResearch.WordTrace tailWord_7127652 prefixEnd_7127652 3659911413980452262470531 := by
  unfold tailWord_7127652
  simp only [CollatzResearch.WordTrace]
  refine ⟨129983412786870792446012605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173311217049161056594683473 129983412786870792446012605)
  ·
    refine ⟨48743779795076547167254727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129983412786870792446012605 48743779795076547167254727)
    ·
      refine ⟨73115669692614820750882091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48743779795076547167254727 73115669692614820750882091)
      ·
        refine ⟨109673504538922231126323137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73115669692614820750882091 109673504538922231126323137)
        ·
          refine ⟨82255128404191673344742353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109673504538922231126323137 82255128404191673344742353)
          ·
            refine ⟨61691346303143755008556765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82255128404191673344742353 61691346303143755008556765)
            ·
              refine ⟨23134254863678908128208787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61691346303143755008556765 23134254863678908128208787)
              ·
                refine ⟨34701382295518362192313181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23134254863678908128208787 34701382295518362192313181)
                ·
                  refine ⟨13013018360819385822117443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34701382295518362192313181 13013018360819385822117443)
                  ·
                    refine ⟨19519527541229078733176165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13013018360819385822117443 19519527541229078733176165)
                    ·
                      refine ⟨3659911413980452262470531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19519527541229078733176165 3659911413980452262470531)
                      ·
                        rfl

theorem cell23_7127652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_7127652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127652 prefixEnd_7127652 := by exact prefixLift 7127652
  have htrace : WordTrace (prefixWord ++ tailWord_7127652) baseStart_7127652 baseEnd_7127652 := by
    simpa [prefixWord, tailWord_7127652, baseEnd_7127652] using wordTrace_append hprefix tailTrace_7127652
  have hstable : (prefixWord ++ tailWord_7127652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127652).length < 2 ^ (prefixWord ++ tailWord_7127652).sum := by decide
  have hdescent : baseEnd_7127652 < baseStart_7127652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127662 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7127662 : Nat := 118140960795 + 7127662 * 2 ^ 59
def prefixEnd_7127662 : Nat := 4983230072969 + 3 ^ 40 * 7127662 * 2
def baseEnd_7127662 : Nat := 1219972182928999074448495

theorem tailTrace_7127662 : CollatzResearch.WordTrace tailWord_7127662 prefixEnd_7127662 1219972182928999074448495 := by
  unfold tailWord_7127662
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495898787963169574986155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173311460202470237733259493 32495898787963169574986155)
  ·
    refine ⟨48743848181944754362479233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32495898787963169574986155 48743848181944754362479233)
    ·
      refine ⟨36557886136458565771859425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48743848181944754362479233 36557886136458565771859425)
      ·
        refine ⟨27418414602343924328894569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36557886136458565771859425 27418414602343924328894569)
        ·
          refine ⟨20563810951757943246670927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27418414602343924328894569 20563810951757943246670927)
          ·
            refine ⟨30845716427636914870006391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20563810951757943246670927 30845716427636914870006391)
            ·
              refine ⟨46268574641455372305009587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30845716427636914870006391 46268574641455372305009587)
              ·
                refine ⟨69402861962183058457514381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46268574641455372305009587 69402861962183058457514381)
                ·
                  refine ⟨26026073235818646921567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69402861962183058457514381 26026073235818646921567893)
                  ·
                    refine ⟨1219972182928999074448495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26026073235818646921567893 1219972182928999074448495)
                    ·
                      rfl

theorem cell23_7127662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7127662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127662 prefixEnd_7127662 := by exact prefixLift 7127662
  have htrace : WordTrace (prefixWord ++ tailWord_7127662) baseStart_7127662 baseEnd_7127662 := by
    simpa [prefixWord, tailWord_7127662, baseEnd_7127662] using wordTrace_append hprefix tailTrace_7127662
  have hstable : (prefixWord ++ tailWord_7127662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127662).length < 2 ^ (prefixWord ++ tailWord_7127662).sum := by decide
  have hdescent : baseEnd_7127662 < baseStart_7127662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127666 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_7127666 : Nat := 118140960795 + 7127666 * 2 ^ 59
def prefixEnd_7127666 : Nat := 4983230072969 + 3 ^ 40 * 7127666 * 2
def baseEnd_7127666 : Nat := 1219972867569871735898489

theorem tailTrace_7127666 : CollatzResearch.WordTrace tailWord_7127666 prefixEnd_7127666 1219972867569871735898489 := by
  unfold tailWord_7127666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64991834048922716320758713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173311557463793910188689901 64991834048922716320758713)
  ·
    refine ⟨48743875536692037240569035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64991834048922716320758713 48743875536692037240569035)
    ·
      refine ⟨73115813305038055860853553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48743875536692037240569035 73115813305038055860853553)
      ·
        refine ⟨54836859978778541895640165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73115813305038055860853553 54836859978778541895640165)
        ·
          refine ⟨10281911246020976605432531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54836859978778541895640165 10281911246020976605432531)
          ·
            refine ⟨15422866869031464908148797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281911246020976605432531 15422866869031464908148797)
            ·
              refine ⟨5783575075886799340555799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15422866869031464908148797 5783575075886799340555799)
              ·
                refine ⟨8675362613830199010833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783575075886799340555799 8675362613830199010833699)
                ·
                  refine ⟨13013043920745298516250549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675362613830199010833699 13013043920745298516250549)
                  ·
                    refine ⟨1219972867569871735898489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013043920745298516250549 1219972867569871735898489)
                    ·
                      rfl

theorem cell23_7127666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_7127666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127666 prefixEnd_7127666 := by exact prefixLift 7127666
  have htrace : WordTrace (prefixWord ++ tailWord_7127666) baseStart_7127666 baseEnd_7127666 := by
    simpa [prefixWord, tailWord_7127666, baseEnd_7127666] using wordTrace_append hprefix tailTrace_7127666
  have hstable : (prefixWord ++ tailWord_7127666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127666).length < 2 ^ (prefixWord ++ tailWord_7127666).sum := by decide
  have hdescent : baseEnd_7127666 < baseStart_7127666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127705 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_7127705 : Nat := 118140960795 + 7127705 * 2 ^ 59
def prefixEnd_7127705 : Nat := 4983230072969 + 3 ^ 40 * 7127705 * 2
def baseEnd_7127705 : Nat := 1219979542818380185035929

theorem tailTrace_7127705 : CollatzResearch.WordTrace tailWord_7127705 prefixEnd_7127705 1219979542818380185035929 := by
  unfold tailWord_7127705
  simp only [CollatzResearch.WordTrace]
  refine ⟨259968758642549574943704569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173312505761699716629136379 259968758642549574943704569)
  ·
    refine ⟨194976568981912181207778427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259968758642549574943704569 194976568981912181207778427)
    ·
      refine ⟨292464853472868271811667641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194976568981912181207778427 292464853472868271811667641)
      ·
        refine ⟨219348640104651203858750731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292464853472868271811667641 219348640104651203858750731)
        ·
          refine ⟨329022960156976805788126097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219348640104651203858750731 329022960156976805788126097)
          ·
            refine ⟨246767220117732604341094573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329022960156976805788126097 246767220117732604341094573)
            ·
              refine ⟨92537707544149726627910465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246767220117732604341094573 92537707544149726627910465)
              ·
                refine ⟨69403280658112294970932849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92537707544149726627910465 69403280658112294970932849)
                ·
                  refine ⟨52052460493584221228199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69403280658112294970932849 52052460493584221228199637)
                  ·
                    refine ⟨1219979542818380185035929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52052460493584221228199637 1219979542818380185035929)
                    ·
                      rfl

theorem cell23_7127705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_7127705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127705 prefixEnd_7127705 := by exact prefixLift 7127705
  have htrace : WordTrace (prefixWord ++ tailWord_7127705) baseStart_7127705 baseEnd_7127705 := by
    simpa [prefixWord, tailWord_7127705, baseEnd_7127705] using wordTrace_append hprefix tailTrace_7127705
  have hstable : (prefixWord ++ tailWord_7127705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127705).length < 2 ^ (prefixWord ++ tailWord_7127705).sum := by decide
  have hdescent : baseEnd_7127705 < baseStart_7127705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127750 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7127750 : Nat := 118140960795 + 7127750 * 2 ^ 59
def prefixEnd_7127750 : Nat := 4983230072969 + 3 ^ 40 * 7127750 * 2
def baseEnd_7127750 : Nat := 3659961735084592879045081

theorem tailTrace_7127750 : CollatzResearch.WordTrace tailWord_7127750 prefixEnd_7127750 3659961735084592879045081 := by
  unfold tailWord_7127750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8124074997730829613409147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173313599951591031752728469 8124074997730829613409147)
  ·
    refine ⟨12186112496596244420113721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8124074997730829613409147 12186112496596244420113721)
    ·
      refine ⟨9139584372447183315085291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12186112496596244420113721 9139584372447183315085291)
      ·
        refine ⟨13709376558670774972627937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139584372447183315085291 13709376558670774972627937)
        ·
          refine ⟨10282032419003081229470953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13709376558670774972627937 10282032419003081229470953)
          ·
            refine ⟨7711524314252310922103215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10282032419003081229470953 7711524314252310922103215)
            ·
              refine ⟨11567286471378466383154823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7711524314252310922103215 11567286471378466383154823)
              ·
                refine ⟨17350929707067699574732235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11567286471378466383154823 17350929707067699574732235)
                ·
                  refine ⟨26026394560601549362098353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17350929707067699574732235 26026394560601549362098353)
                  ·
                    refine ⟨19519795920451162021573765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26026394560601549362098353 19519795920451162021573765)
                    ·
                      refine ⟨3659961735084592879045081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19519795920451162021573765 3659961735084592879045081)
                      ·
                        rfl

theorem cell23_7127750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7127750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127750 prefixEnd_7127750 := by exact prefixLift 7127750
  have htrace : WordTrace (prefixWord ++ tailWord_7127750) baseStart_7127750 baseEnd_7127750 := by
    simpa [prefixWord, tailWord_7127750, baseEnd_7127750] using wordTrace_append hprefix tailTrace_7127750
  have hstable : (prefixWord ++ tailWord_7127750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127750).length < 2 ^ (prefixWord ++ tailWord_7127750).sum := by decide
  have hdescent : baseEnd_7127750 < baseStart_7127750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127752 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7127752 : Nat := 118140960795 + 7127752 * 2 ^ 59
def prefixEnd_7127752 : Nat := 4983230072969 + 3 ^ 40 * 7127752 * 2
def baseEnd_7127752 : Nat := 1219987587348633957073357

theorem tailTrace_7127752 : CollatzResearch.WordTrace tailWord_7127752 prefixEnd_7127752 1219987587348633957073357 := by
  unfold tailWord_7127752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129985236436689650985332755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173313648582252867980443673 129985236436689650985332755)
  ·
    refine ⟨194977854655034476477999133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129985236436689650985332755 194977854655034476477999133)
    ·
      refine ⟨73116695495637928679249675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194977854655034476477999133 73116695495637928679249675)
      ·
        refine ⟨109675043243456893018874513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73116695495637928679249675 109675043243456893018874513)
        ·
          refine ⟨82256282432592669764155885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109675043243456893018874513 82256282432592669764155885)
          ·
            refine ⟨30846105912222251161558457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82256282432592669764155885 30846105912222251161558457)
            ·
              refine ⟨23134579434166688371168843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30846105912222251161558457 23134579434166688371168843)
              ·
                refine ⟨34701869151250032556753265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23134579434166688371168843 34701869151250032556753265)
                ·
                  refine ⟨26026401863437524417564949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34701869151250032556753265 26026401863437524417564949)
                  ·
                    refine ⟨1219987587348633957073357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26026401863437524417564949 1219987587348633957073357)
                    ·
                      rfl

theorem cell23_7127752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7127752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127752 prefixEnd_7127752 := by exact prefixLift 7127752
  have htrace : WordTrace (prefixWord ++ tailWord_7127752) baseStart_7127752 baseEnd_7127752 := by
    simpa [prefixWord, tailWord_7127752, baseEnd_7127752] using wordTrace_append hprefix tailTrace_7127752
  have hstable : (prefixWord ++ tailWord_7127752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127752).length < 2 ^ (prefixWord ++ tailWord_7127752).sum := by decide
  have hdescent : baseEnd_7127752 < baseStart_7127752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127779 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7127779 : Nat := 118140960795 + 7127779 * 2 ^ 59
def prefixEnd_7127779 : Nat := 4983230072969 + 3 ^ 40 * 7127779 * 2
def baseEnd_7127779 : Nat := 3659976626023573265582447

theorem tailTrace_7127779 : CollatzResearch.WordTrace tailWord_7127779 prefixEnd_7127779 3659976626023573265582447 := by
  unfold tailWord_7127779
  simp only [CollatzResearch.WordTrace]
  refine ⟨259971457644281485581898391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173314305096187657054598927 259971457644281485581898391)
  ·
    refine ⟨389957186466422228372847587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259971457644281485581898391 389957186466422228372847587)
    ·
      refine ⟨584935779699633342559271381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389957186466422228372847587 584935779699633342559271381)
      ·
        refine ⟨13709432336710156466232923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 584935779699633342559271381 13709432336710156466232923)
        ·
          refine ⟨20564148505065234699349385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709432336710156466232923 20564148505065234699349385)
          ·
            refine ⟨15423111378798926024512039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20564148505065234699349385 15423111378798926024512039)
            ·
              refine ⟨23134667068198389036768059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15423111378798926024512039 23134667068198389036768059)
              ·
                refine ⟨34702000602297583555152089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23134667068198389036768059 34702000602297583555152089)
                ·
                  refine ⟨26026500451723187666364067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34702000602297583555152089 26026500451723187666364067)
                  ·
                    refine ⟨39039750677584781499546101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26026500451723187666364067 39039750677584781499546101)
                    ·
                      refine ⟨3659976626023573265582447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39039750677584781499546101 3659976626023573265582447)
                      ·
                        rfl

theorem cell23_7127779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7127779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127779 prefixEnd_7127779 := by exact prefixLift 7127779
  have htrace : WordTrace (prefixWord ++ tailWord_7127779) baseStart_7127779 baseEnd_7127779 := by
    simpa [prefixWord, tailWord_7127779, baseEnd_7127779] using wordTrace_append hprefix tailTrace_7127779
  have hstable : (prefixWord ++ tailWord_7127779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127779).length < 2 ^ (prefixWord ++ tailWord_7127779).sum := by decide
  have hdescent : baseEnd_7127779 < baseStart_7127779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127810 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7127810 : Nat := 118140960795 + 7127810 * 2 ^ 59
def prefixEnd_7127810 : Nat := 4983230072969 + 3 ^ 40 * 7127810 * 2
def baseEnd_7127810 : Nat := 3659992543923862644294805

theorem tailTrace_7127810 : CollatzResearch.WordTrace tailWord_7127810 prefixEnd_7127810 3659992543923862644294805 := by
  unfold tailWord_7127810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64993147076792294469069221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173315058871446118584184589 64993147076792294469069221)
  ·
    refine ⟨12186215076898555212950479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64993147076792294469069221 12186215076898555212950479)
    ·
      refine ⟨18279322615347832819425719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12186215076898555212950479 18279322615347832819425719)
      ·
        refine ⟨27418983923021749229138579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18279322615347832819425719 27418983923021749229138579)
        ·
          refine ⟨41128475884532623843707869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27418983923021749229138579 41128475884532623843707869)
          ·
            refine ⟨15423178456699733941390451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41128475884532623843707869 15423178456699733941390451)
            ·
              refine ⟨23134767685049600912085677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15423178456699733941390451 23134767685049600912085677)
              ·
                refine ⟨8675537881893600342032129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23134767685049600912085677 8675537881893600342032129)
                ·
                  refine ⟨6506653411420200256524097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8675537881893600342032129 6506653411420200256524097)
                  ·
                    refine ⟨4879990058565150192393073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6506653411420200256524097 4879990058565150192393073)
                    ·
                      refine ⟨3659992543923862644294805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879990058565150192393073 3659992543923862644294805)
                      ·
                        rfl

theorem cell23_7127810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7127810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127810 prefixEnd_7127810 := by exact prefixLift 7127810
  have htrace : WordTrace (prefixWord ++ tailWord_7127810) baseStart_7127810 baseEnd_7127810 := by
    simpa [prefixWord, tailWord_7127810, baseEnd_7127810] using wordTrace_append hprefix tailTrace_7127810
  have hstable : (prefixWord ++ tailWord_7127810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127810).length < 2 ^ (prefixWord ++ tailWord_7127810).sum := by decide
  have hdescent : baseEnd_7127810 < baseStart_7127810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127822 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7127822 : Nat := 118140960795 + 7127822 * 2 ^ 59
def prefixEnd_7127822 : Nat := 4983230072969 + 3 ^ 40 * 7127822 * 2
def baseEnd_7127822 : Nat := 3659998705691716597344749

theorem tailTrace_7127822 : CollatzResearch.WordTrace tailWord_7127822 prefixEnd_7127822 3659998705691716597344749 := by
  unfold tailWord_7127822
  simp only [CollatzResearch.WordTrace]
  refine ⟨32496628247890712990714215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173315350655417135950475813 32496628247890712990714215)
  ·
    refine ⟨48744942371836069486071323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32496628247890712990714215 48744942371836069486071323)
    ·
      refine ⟨73117413557754104229106985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48744942371836069486071323 73117413557754104229106985)
      ·
        refine ⟨54838060168315578171830239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73117413557754104229106985 54838060168315578171830239)
        ·
          refine ⟨82257090252473367257745359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54838060168315578171830239 82257090252473367257745359)
          ·
            refine ⟨123385635378710050886618039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82257090252473367257745359 123385635378710050886618039)
            ·
              refine ⟨185078453068065076329927059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123385635378710050886618039 185078453068065076329927059)
              ·
                refine ⟨277617679602097614494890589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185078453068065076329927059 277617679602097614494890589)
                ·
                  refine ⟨104106629850786605435583971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277617679602097614494890589 104106629850786605435583971)
                  ·
                    refine ⟨156159944776179908153375957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104106629850786605435583971 156159944776179908153375957)
                    ·
                      refine ⟨3659998705691716597344749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156159944776179908153375957 3659998705691716597344749)
                      ·
                        rfl

theorem cell23_7127822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7127822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127822 prefixEnd_7127822 := by exact prefixLift 7127822
  have htrace : WordTrace (prefixWord ++ tailWord_7127822) baseStart_7127822 baseEnd_7127822 := by
    simpa [prefixWord, tailWord_7127822, baseEnd_7127822] using wordTrace_append hprefix tailTrace_7127822
  have hstable : (prefixWord ++ tailWord_7127822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127822).length < 2 ^ (prefixWord ++ tailWord_7127822).sum := by decide
  have hdescent : baseEnd_7127822 < baseStart_7127822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127829 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_7127829 : Nat := 118140960795 + 7127829 * 2 ^ 59
def prefixEnd_7127829 : Nat := 4983230072969 + 3 ^ 40 * 7127829 * 2
def baseEnd_7127829 : Nat := 1220000766685432689985739

theorem tailTrace_7127829 : CollatzResearch.WordTrace tailWord_7127829 prefixEnd_7127829 1220000766685432689985739 := by
  unfold tailWord_7127829
  simp only [CollatzResearch.WordTrace]
  refine ⟨259973281294100344121218541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173315520862733562747479027 259973281294100344121218541)
  ·
    refine ⟨97489980485287629045456953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259973281294100344121218541 97489980485287629045456953)
    ·
      refine ⟨73117485363965721784092715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97489980485287629045456953 73117485363965721784092715)
      ·
        refine ⟨109676228045948582676139073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73117485363965721784092715 109676228045948582676139073)
        ·
          refine ⟨82257171034461437007104305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109676228045948582676139073 82257171034461437007104305)
          ·
            refine ⟨61692878275846077755328229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82257171034461437007104305 61692878275846077755328229)
            ·
              refine ⟨11567414676721139579124043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61692878275846077755328229 11567414676721139579124043)
              ·
                refine ⟨17351122015081709368686065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11567414676721139579124043 17351122015081709368686065)
                ·
                  refine ⟨13013341511311282026514549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17351122015081709368686065 13013341511311282026514549)
                  ·
                    refine ⟨1220000766685432689985739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13013341511311282026514549 1220000766685432689985739)
                    ·
                      rfl

theorem cell23_7127829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_7127829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127829 prefixEnd_7127829 := by exact prefixLift 7127829
  have htrace : WordTrace (prefixWord ++ tailWord_7127829) baseStart_7127829 baseEnd_7127829 := by
    simpa [prefixWord, tailWord_7127829, baseEnd_7127829] using wordTrace_append hprefix tailTrace_7127829
  have hstable : (prefixWord ++ tailWord_7127829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127829).length < 2 ^ (prefixWord ++ tailWord_7127829).sum := by decide
  have hdescent : baseEnd_7127829 < baseStart_7127829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127849 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 4, 2]
def baseStart_7127849 : Nat := 118140960795 + 7127849 * 2 ^ 59
def prefixEnd_7127849 : Nat := 4983230072969 + 3 ^ 40 * 7127849 * 2
def baseEnd_7127849 : Nat := 3660012569669387991707125

theorem tailTrace_7127849 : CollatzResearch.WordTrace tailWord_7127849 prefixEnd_7127849 3660012569669387991707125 := by
  unfold tailWord_7127849
  simp only [CollatzResearch.WordTrace]
  refine ⟨259974010754027887536946601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173316007169351925024631067 259974010754027887536946601)
  ·
    refine ⟨194980508065520915652709951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259974010754027887536946601 194980508065520915652709951)
    ·
      refine ⟨292470762098281373479064927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194980508065520915652709951 292470762098281373479064927)
      ·
        refine ⟨438706143147422060218597391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292470762098281373479064927 438706143147422060218597391)
        ·
          refine ⟨658059214721133090327896087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438706143147422060218597391 658059214721133090327896087)
          ·
            refine ⟨987088822081699635491844131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658059214721133090327896087 987088822081699635491844131)
            ·
              refine ⟨1480633233122549453237766197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987088822081699635491844131 1480633233122549453237766197)
              ·
                refine ⟨138809365605239011241040581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1480633233122549453237766197 138809365605239011241040581)
                ·
                  refine ⟨26026756050982314607695109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138809365605239011241040581 26026756050982314607695109)
                  ·
                    refine ⟨4880016759559183988942833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26026756050982314607695109 4880016759559183988942833)
                    ·
                      refine ⟨3660012569669387991707125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880016759559183988942833 3660012569669387991707125)
                      ·
                        rfl

theorem cell23_7127849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4, 2].length) (baseStart_7127849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127849 prefixEnd_7127849 := by exact prefixLift 7127849
  have htrace : WordTrace (prefixWord ++ tailWord_7127849) baseStart_7127849 baseEnd_7127849 := by
    simpa [prefixWord, tailWord_7127849, baseEnd_7127849] using wordTrace_append hprefix tailTrace_7127849
  have hstable : (prefixWord ++ tailWord_7127849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127849).length < 2 ^ (prefixWord ++ tailWord_7127849).sum := by decide
  have hdescent : baseEnd_7127849 < baseStart_7127849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127852 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7127852 : Nat := 118140960795 + 7127852 * 2 ^ 59
def prefixEnd_7127852 : Nat := 4983230072969 + 3 ^ 40 * 7127852 * 2
def baseEnd_7127852 : Nat := 3660014110111351479969611

theorem tailTrace_7127852 : CollatzResearch.WordTrace tailWord_7127852 prefixEnd_7127852 3660014110111351479969611 := by
  unfold tailWord_7127852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129987060086508509524652905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173316080115344679366203873 129987060086508509524652905)
  ·
    refine ⟨97490295064881382143489679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129987060086508509524652905 97490295064881382143489679)
    ·
      refine ⟨146235442597322073215234519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97490295064881382143489679 146235442597322073215234519)
      ·
        refine ⟨219353163895983109822851779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146235442597322073215234519 219353163895983109822851779)
        ·
          refine ⟨329029745843974664734277669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219353163895983109822851779 329029745843974664734277669)
          ·
            refine ⟨61693077345745249637677063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329029745843974664734277669 61693077345745249637677063)
            ·
              refine ⟨92539616018617874456515595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61693077345745249637677063 92539616018617874456515595)
              ·
                refine ⟨138809424027926811684773393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92539616018617874456515595 138809424027926811684773393)
                ·
                  refine ⟨104107068020945108763580045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138809424027926811684773393 104107068020945108763580045)
                  ·
                    refine ⟨39040150507854415786342517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104107068020945108763580045 39040150507854415786342517)
                    ·
                      refine ⟨3660014110111351479969611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39040150507854415786342517 3660014110111351479969611)
                      ·
                        rfl

theorem cell23_7127852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7127852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127852 prefixEnd_7127852 := by exact prefixLift 7127852
  have htrace : WordTrace (prefixWord ++ tailWord_7127852) baseStart_7127852 baseEnd_7127852 := by
    simpa [prefixWord, tailWord_7127852, baseEnd_7127852] using wordTrace_append hprefix tailTrace_7127852
  have hstable : (prefixWord ++ tailWord_7127852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127852).length < 2 ^ (prefixWord ++ tailWord_7127852).sum := by decide
  have hdescent : baseEnd_7127852 < baseStart_7127852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127893 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_7127893 : Nat := 118140960795 + 7127893 * 2 ^ 59
def prefixEnd_7127893 : Nat := 4983230072969 + 3 ^ 40 * 7127893 * 2
def baseEnd_7127893 : Nat := 1220011720939395273185641

theorem tailTrace_7127893 : CollatzResearch.WordTrace tailWord_7127893 prefixEnd_7127893 1220011720939395273185641 := by
  unfold tailWord_7127893
  simp only [CollatzResearch.WordTrace]
  refine ⟨259975615565868483051548333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173317077043912322034365555 259975615565868483051548333)
  ·
    refine ⟨97490855837200681144330625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259975615565868483051548333 97490855837200681144330625)
    ·
      refine ⟨73118141877900510858247969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97490855837200681144330625 73118141877900510858247969)
      ·
        refine ⟨54838606408425383143685977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73118141877900510858247969 54838606408425383143685977)
        ·
          refine ⟨41128954806319037357764483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54838606408425383143685977 41128954806319037357764483)
          ·
            refine ⟨61693432209478556036646725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41128954806319037357764483 61693432209478556036646725)
            ·
              refine ⟨11567518539277229256871261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61693432209478556036646725 11567518539277229256871261)
              ·
                refine ⟨4337819452228960971326723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11567518539277229256871261 4337819452228960971326723)
                ·
                  refine ⟨6506729178343441456990085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337819452228960971326723 6506729178343441456990085)
                  ·
                    refine ⟨1220011720939395273185641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6506729178343441456990085 1220011720939395273185641)
                    ·
                      rfl

theorem cell23_7127893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_7127893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127893 prefixEnd_7127893 := by exact prefixLift 7127893
  have htrace : WordTrace (prefixWord ++ tailWord_7127893) baseStart_7127893 baseEnd_7127893 := by
    simpa [prefixWord, tailWord_7127893, baseEnd_7127893] using wordTrace_append hprefix tailTrace_7127893
  have hstable : (prefixWord ++ tailWord_7127893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127893).length < 2 ^ (prefixWord ++ tailWord_7127893).sum := by decide
  have hdescent : baseEnd_7127893 < baseStart_7127893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127906 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7127906 : Nat := 118140960795 + 7127906 * 2 ^ 59
def prefixEnd_7127906 : Nat := 4983230072969 + 3 ^ 40 * 7127906 * 2
def baseEnd_7127906 : Nat := 406671315340743807632707

theorem tailTrace_7127906 : CollatzResearch.WordTrace tailWord_7127906 prefixEnd_7127906 406671315340743807632707 := by
  unfold tailWord_7127906
  simp only [CollatzResearch.WordTrace]
  refine ⟨64994022428705346567942893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173317393143214257514514381 64994022428705346567942893)
  ·
    refine ⟨24372758410764504962978585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64994022428705346567942893 24372758410764504962978585)
    ·
      refine ⟨18279568808073378722233939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24372758410764504962978585 18279568808073378722233939)
      ·
        refine ⟨27419353212110068083350909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18279568808073378722233939 27419353212110068083350909)
        ·
          refine ⟨10282257454541275531256591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27419353212110068083350909 10282257454541275531256591)
          ·
            refine ⟨15423386181811913296884887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282257454541275531256591 15423386181811913296884887)
            ·
              refine ⟨23135079272717869945327331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15423386181811913296884887 23135079272717869945327331)
              ·
                refine ⟨34702618909076804917990997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23135079272717869945327331 34702618909076804917990997)
                ·
                  refine ⟨406671315340743807632707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34702618909076804917990997 406671315340743807632707)
                  ·
                    rfl

theorem cell23_7127906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7127906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127906 prefixEnd_7127906 := by exact prefixLift 7127906
  have htrace : WordTrace (prefixWord ++ tailWord_7127906) baseStart_7127906 baseEnd_7127906 := by
    simpa [prefixWord, tailWord_7127906, baseEnd_7127906] using wordTrace_append hprefix tailTrace_7127906
  have hstable : (prefixWord ++ tailWord_7127906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127906).length < 2 ^ (prefixWord ++ tailWord_7127906).sum := by decide
  have hdescent : baseEnd_7127906 < baseStart_7127906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127967 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7127967 : Nat := 118140960795 + 7127967 * 2 ^ 59
def prefixEnd_7127967 : Nat := 4983230072969 + 3 ^ 40 * 7127967 * 2
def baseEnd_7127967 : Nat := 3660073160386618530031583

theorem tailTrace_7127967 : CollatzResearch.WordTrace tailWord_7127967 prefixEnd_7127967 3660073160386618530031583 := by
  unfold tailWord_7127967
  simp only [CollatzResearch.WordTrace]
  refine ⟨259978314567600393689742155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173318876378400262459828103 259978314567600393689742155)
  ·
    refine ⟨389967471851400590534613233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259978314567600393689742155 389967471851400590534613233)
    ·
      refine ⟨292475603888550442900959925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389967471851400590534613233 292475603888550442900959925)
      ·
        refine ⟨27419587864551604021964993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292475603888550442900959925 27419587864551604021964993)
        ·
          refine ⟨20564690898413703016473745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27419587864551604021964993 20564690898413703016473745)
          ·
            refine ⟨15423518173810277262355309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20564690898413703016473745 15423518173810277262355309)
            ·
              refine ⟨5783819315178853973383241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15423518173810277262355309 5783819315178853973383241)
              ·
                refine ⟨4337864486384140480037431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783819315178853973383241 4337864486384140480037431)
                ·
                  refine ⟨6506796729576210720056147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337864486384140480037431 6506796729576210720056147)
                  ·
                    refine ⟨9760195094364316080084221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6506796729576210720056147 9760195094364316080084221)
                    ·
                      refine ⟨3660073160386618530031583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760195094364316080084221 3660073160386618530031583)
                      ·
                        rfl

theorem cell23_7127967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7127967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127967 prefixEnd_7127967 := by exact prefixLift 7127967
  have htrace : WordTrace (prefixWord ++ tailWord_7127967) baseStart_7127967 baseEnd_7127967 := by
    simpa [prefixWord, tailWord_7127967, baseEnd_7127967] using wordTrace_append hprefix tailTrace_7127967
  have hstable : (prefixWord ++ tailWord_7127967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127967).length < 2 ^ (prefixWord ++ tailWord_7127967).sum := by decide
  have hdescent : baseEnd_7127967 < baseStart_7127967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7127993 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7127993 : Nat := 118140960795 + 7127993 * 2 ^ 59
def prefixEnd_7127993 : Nat := 4983230072969 + 3 ^ 40 * 7127993 * 2
def baseEnd_7127993 : Nat := 3660086510883635428306463

theorem tailTrace_7127993 : CollatzResearch.WordTrace tailWord_7127993 prefixEnd_7127993 3660086510883635428306463 := by
  unfold tailWord_7127993
  simp only [CollatzResearch.WordTrace]
  refine ⟨259979262865506200130188633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173319508577004133420125755 259979262865506200130188633)
  ·
    refine ⟨194984447149129650097641475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259979262865506200130188633 194984447149129650097641475)
    ·
      refine ⟨292476670723694475146462213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194984447149129650097641475 292476670723694475146462213)
      ·
        refine ⟨54839375760692714089961665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292476670723694475146462213 54839375760692714089961665)
        ·
          refine ⟨41129531820519535567471249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54839375760692714089961665 41129531820519535567471249)
          ·
            refine ⟨30847148865389651675603437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41129531820519535567471249 30847148865389651675603437)
            ·
              refine ⟨11567680824521119378351289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30847148865389651675603437 11567680824521119378351289)
              ·
                refine ⟨8675760618390839533763467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11567680824521119378351289 8675760618390839533763467)
                ·
                  refine ⟨13013640927586259300645201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675760618390839533763467 13013640927586259300645201)
                  ·
                    refine ⟨9760230695689694475483901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13013640927586259300645201 9760230695689694475483901)
                    ·
                      refine ⟨3660086510883635428306463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760230695689694475483901 3660086510883635428306463)
                      ·
                        rfl

theorem cell23_7127993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7127993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7127993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7127993 prefixEnd_7127993 := by exact prefixLift 7127993
  have htrace : WordTrace (prefixWord ++ tailWord_7127993) baseStart_7127993 baseEnd_7127993 := by
    simpa [prefixWord, tailWord_7127993, baseEnd_7127993] using wordTrace_append hprefix tailTrace_7127993
  have hstable : (prefixWord ++ tailWord_7127993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7127993).length < 2 ^ (prefixWord ++ tailWord_7127993).sum := by decide
  have hdescent : baseEnd_7127993 < baseStart_7127993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7127993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128013 : List Nat := [1, 6, 3, 1, 12]
def baseStart_7128013 : Nat := 118140960795 + 7128013 * 2 ^ 59
def prefixEnd_7128013 : Nat := 4983230072969 + 3 ^ 40 * 7128013 * 2
def baseEnd_7128013 : Nat := 5020708889570267969899

theorem tailTrace_7128013 : CollatzResearch.WordTrace tailWord_7128013 prefixEnd_7128013 5020708889570267969899 := by
  unfold tailWord_7128013
  simp only [CollatzResearch.WordTrace]
  refine ⟨259979992325433743545916693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173319994883622495697277795 259979992325433743545916693)
  ·
    refine ⟨12186562140254706728714845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259979992325433743545916693 12186562140254706728714845)
    ·
      refine ⟨4569960802595515023268067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12186562140254706728714845 4569960802595515023268067)
      ·
        refine ⟨6854941203893272534902101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569960802595515023268067 6854941203893272534902101)
        ·
          refine ⟨5020708889570267969899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6854941203893272534902101 5020708889570267969899)
          ·
            rfl

theorem cell23_7128013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 12].length) (baseStart_7128013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128013 prefixEnd_7128013 := by exact prefixLift 7128013
  have htrace : WordTrace (prefixWord ++ tailWord_7128013) baseStart_7128013 baseEnd_7128013 := by
    simpa [prefixWord, tailWord_7128013, baseEnd_7128013] using wordTrace_append hprefix tailTrace_7128013
  have hstable : (prefixWord ++ tailWord_7128013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128013).length < 2 ^ (prefixWord ++ tailWord_7128013).sum := by decide
  have hdescent : baseEnd_7128013 < baseStart_7128013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128024 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_7128024 : Nat := 118140960795 + 7128024 * 2 ^ 59
def prefixEnd_7128024 : Nat := 4983230072969 + 3 ^ 40 * 7128024 * 2
def baseEnd_7128024 : Nat := 3660102428783924807018821

theorem tailTrace_7128024 : CollatzResearch.WordTrace tailWord_7128024 prefixEnd_7128024 3660102428783924807018821 := by
  unfold tailWord_7128024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129990196764196946212283563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173320262352262594949711417 129990196764196946212283563)
  ·
    refine ⟨194985295146295419318425345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129990196764196946212283563 194985295146295419318425345)
    ·
      refine ⟨146238971359721564488819009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194985295146295419318425345 146238971359721564488819009)
      ·
        refine ⟨109679228519791173366614257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146238971359721564488819009 109679228519791173366614257)
        ·
          refine ⟨82259421389843380024960693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109679228519791173366614257 82259421389843380024960693)
          ·
            refine ⟨7711820755297816877340065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82259421389843380024960693 7711820755297816877340065)
            ·
              refine ⟨5783865566473362658005049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7711820755297816877340065 5783865566473362658005049)
              ·
                refine ⟨4337899174855021993503787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783865566473362658005049 4337899174855021993503787)
                ·
                  refine ⟨6506848762282532990255681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337899174855021993503787 6506848762282532990255681)
                  ·
                    refine ⟨4880136571711899742691761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6506848762282532990255681 4880136571711899742691761)
                    ·
                      refine ⟨3660102428783924807018821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880136571711899742691761 3660102428783924807018821)
                      ·
                        rfl

theorem cell23_7128024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_7128024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128024 prefixEnd_7128024 := by exact prefixLift 7128024
  have htrace : WordTrace (prefixWord ++ tailWord_7128024) baseStart_7128024 baseEnd_7128024 := by
    simpa [prefixWord, tailWord_7128024, baseEnd_7128024] using wordTrace_append hprefix tailTrace_7128024
  have hstable : (prefixWord ++ tailWord_7128024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128024).length < 2 ^ (prefixWord ++ tailWord_7128024).sum := by decide
  have hdescent : baseEnd_7128024 < baseStart_7128024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128059 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_7128059 : Nat := 118140960795 + 7128059 * 2 ^ 59
def prefixEnd_7128059 : Nat := 4983230072969 + 3 ^ 40 * 7128059 * 2
def baseEnd_7128059 : Nat := 3660120400606832170081159

theorem tailTrace_7128059 : CollatzResearch.WordTrace tailWord_7128059 prefixEnd_7128059 3660120400606832170081159 := by
  unfold tailWord_7128059
  simp only [CollatzResearch.WordTrace]
  refine ⟨259981670083267093402091231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173321113388844728934727487 259981670083267093402091231)
  ·
    refine ⟨389972505124900640103136847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259981670083267093402091231 389972505124900640103136847)
    ·
      refine ⟨584958757687350960154705271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389972505124900640103136847 584958757687350960154705271)
      ·
        refine ⟨877438136531026440232057907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584958757687350960154705271 877438136531026440232057907)
        ·
          refine ⟨1316157204796539660348086861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877438136531026440232057907 1316157204796539660348086861)
          ·
            refine ⟨493558951798702372630532573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1316157204796539660348086861 493558951798702372630532573)
            ·
              refine ⟨185084606924513389736449715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493558951798702372630532573 185084606924513389736449715)
              ·
                refine ⟨277626910386770084604674573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185084606924513389736449715 277626910386770084604674573)
                ·
                  refine ⟨104110091395038781726752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277626910386770084604674573 104110091395038781726752965)
                  ·
                    refine ⟨19520642136569771573766181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104110091395038781726752965 19520642136569771573766181)
                    ·
                      refine ⟨3660120400606832170081159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19520642136569771573766181 3660120400606832170081159)
                      ·
                        rfl

theorem cell23_7128059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_7128059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128059 prefixEnd_7128059 := by exact prefixLift 7128059
  have htrace : WordTrace (prefixWord ++ tailWord_7128059) baseStart_7128059 baseEnd_7128059 := by
    simpa [prefixWord, tailWord_7128059, baseEnd_7128059] using wordTrace_append hprefix tailTrace_7128059
  have hstable : (prefixWord ++ tailWord_7128059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128059).length < 2 ^ (prefixWord ++ tailWord_7128059).sum := by decide
  have hdescent : baseEnd_7128059 < baseStart_7128059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128069 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 9]
def baseStart_7128069 : Nat := 118140960795 + 7128069 * 2 ^ 59
def prefixEnd_7128069 : Nat := 4983230072969 + 3 ^ 40 * 7128069 * 2
def baseEnd_7128069 : Nat := 406680615045930792328457

theorem tailTrace_7128069 : CollatzResearch.WordTrace tailWord_7128069 prefixEnd_7128069 406680615045930792328457 := by
  unfold tailWord_7128069
  simp only [CollatzResearch.WordTrace]
  refine ⟨259982034813230865109955261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173321356542153910073303507 259982034813230865109955261)
  ·
    refine ⟨97493263054961574416233223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259982034813230865109955261 97493263054961574416233223)
    ·
      refine ⟨146239894582442361624349835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97493263054961574416233223 146239894582442361624349835)
      ·
        refine ⟨219359841873663542436524753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146239894582442361624349835 219359841873663542436524753)
        ·
          refine ⟨164519881405247656827393565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219359841873663542436524753 164519881405247656827393565)
          ·
            refine ⟨61694955526967871310272587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164519881405247656827393565 61694955526967871310272587)
            ·
              refine ⟨92542433290451806965408881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61694955526967871310272587 92542433290451806965408881)
              ·
                refine ⟨69406824967838855224056661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92542433290451806965408881 69406824967838855224056661)
                ·
                  refine ⟨406680615045930792328457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69406824967838855224056661 406680615045930792328457)
                  ·
                    rfl

theorem cell23_7128069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_7128069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128069 prefixEnd_7128069 := by exact prefixLift 7128069
  have htrace : WordTrace (prefixWord ++ tailWord_7128069) baseStart_7128069 baseEnd_7128069 := by
    simpa [prefixWord, tailWord_7128069, baseEnd_7128069] using wordTrace_append hprefix tailTrace_7128069
  have hstable : (prefixWord ++ tailWord_7128069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128069).length < 2 ^ (prefixWord ++ tailWord_7128069).sum := by decide
  have hdescent : baseEnd_7128069 < baseStart_7128069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128076 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7128076 : Nat := 118140960795 + 7128076 * 2 ^ 59
def prefixEnd_7128076 : Nat := 4983230072969 + 3 ^ 40 * 7128076 * 2
def baseEnd_7128076 : Nat := 3660129129777958603568581

theorem tailTrace_7128076 : CollatzResearch.WordTrace tailWord_7128076 prefixEnd_7128076 3660129129777958603568581 := by
  unfold tailWord_7128076
  simp only [CollatzResearch.WordTrace]
  refine ⟨129991145062102752652730041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173321526749470336870306721 129991145062102752652730041)
  ·
    refine ⟨97493358796577064489547531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129991145062102752652730041 97493358796577064489547531)
    ·
      refine ⟨146240038194865596734321297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97493358796577064489547531 146240038194865596734321297)
      ·
        refine ⟨109680028646149197550740973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146240038194865596734321297 109680028646149197550740973)
        ·
          refine ⟨41130010742305949081527865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109680028646149197550740973 41130010742305949081527865)
          ·
            refine ⟨30847508056729461811145899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41130010742305949081527865 30847508056729461811145899)
            ·
              refine ⟨46271262085094192716718849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30847508056729461811145899 46271262085094192716718849)
              ·
                refine ⟨34703446563820644537539137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46271262085094192716718849 34703446563820644537539137)
                ·
                  refine ⟨26027584922865483403154353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34703446563820644537539137 26027584922865483403154353)
                  ·
                    refine ⟨19520688692149112552365765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26027584922865483403154353 19520688692149112552365765)
                    ·
                      refine ⟨3660129129777958603568581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19520688692149112552365765 3660129129777958603568581)
                      ·
                        rfl

theorem cell23_7128076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7128076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128076 prefixEnd_7128076 := by exact prefixLift 7128076
  have htrace : WordTrace (prefixWord ++ tailWord_7128076) baseStart_7128076 baseEnd_7128076 := by
    simpa [prefixWord, tailWord_7128076, baseEnd_7128076] using wordTrace_append hprefix tailTrace_7128076
  have hstable : (prefixWord ++ tailWord_7128076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128076).length < 2 ^ (prefixWord ++ tailWord_7128076).sum := by decide
  have hdescent : baseEnd_7128076 < baseStart_7128076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128103 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 7]
def baseStart_7128103 : Nat := 118140960795 + 7128103 * 2 ^ 59
def prefixEnd_7128103 : Nat := 4983230072969 + 3 ^ 40 * 7128103 * 2
def baseEnd_7128103 : Nat := 406682554861736666436773

theorem tailTrace_7128103 : CollatzResearch.WordTrace tailWord_7128103 prefixEnd_7128103 406682554861736666436773 := by
  unfold tailWord_7128103
  simp only [CollatzResearch.WordTrace]
  refine ⟨259983274895107688916692963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173322183263405125944461975 259983274895107688916692963)
  ·
    refine ⟨389974912342661533375039445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259983274895107688916692963 389974912342661533375039445)
    ·
      refine ⟨9140037008031129688477487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 389974912342661533375039445 9140037008031129688477487)
      ·
        refine ⟨13710055512046694532716231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9140037008031129688477487 13710055512046694532716231)
        ·
          refine ⟨20565083268070041799074347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710055512046694532716231 20565083268070041799074347)
          ·
            refine ⟨30847624902105062698611521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565083268070041799074347 30847624902105062698611521)
            ·
              refine ⟨23135718676578797023958641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30847624902105062698611521 23135718676578797023958641)
              ·
                refine ⟨17351789007434097767968981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23135718676578797023958641 17351789007434097767968981)
                ·
                  refine ⟨406682554861736666436773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17351789007434097767968981 406682554861736666436773)
                  ·
                    rfl

theorem cell23_7128103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 7].length) (baseStart_7128103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128103 prefixEnd_7128103 := by exact prefixLift 7128103
  have htrace : WordTrace (prefixWord ++ tailWord_7128103) baseStart_7128103 baseEnd_7128103 := by
    simpa [prefixWord, tailWord_7128103, baseEnd_7128103] using wordTrace_append hprefix tailTrace_7128103
  have hstable : (prefixWord ++ tailWord_7128103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128103).length < 2 ^ (prefixWord ++ tailWord_7128103).sum := by decide
  have hdescent : baseEnd_7128103 < baseStart_7128103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128120 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 5]
def baseStart_7128120 : Nat := 118140960795 + 7128120 * 2 ^ 59
def prefixEnd_7128120 : Nat := 4983230072969 + 3 ^ 40 * 7128120 * 2
def baseEnd_7128120 : Nat := 406683524769639603490931

theorem tailTrace_7128120 : CollatzResearch.WordTrace tailWord_7128120 prefixEnd_7128120 406683524769639603490931 := by
  unfold tailWord_7128120
  simp only [CollatzResearch.WordTrace]
  refine ⟨129991947468023050410030907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173322596624030733880041209 129991947468023050410030907)
  ·
    refine ⟨194987921202034575615046361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129991947468023050410030907 194987921202034575615046361)
    ·
      refine ⟨146240940901525931711284771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194987921202034575615046361 146240940901525931711284771)
      ·
        refine ⟨219361411352288897566927157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146240940901525931711284771 219361411352288897566927157)
        ·
          refine ⟨20565132314277084146899421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219361411352288897566927157 20565132314277084146899421)
          ·
            refine ⟨7711924617853906555087283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20565132314277084146899421 7711924617853906555087283)
            ·
              refine ⟨11567886926780859832630925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7711924617853906555087283 11567886926780859832630925)
              ·
                refine ⟨4337957597542822437236597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11567886926780859832630925 4337957597542822437236597)
                ·
                  refine ⟨406683524769639603490931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4337957597542822437236597 406683524769639603490931)
                  ·
                    rfl

theorem cell23_7128120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 5].length) (baseStart_7128120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128120 prefixEnd_7128120 := by exact prefixLift 7128120
  have htrace : WordTrace (prefixWord ++ tailWord_7128120) baseStart_7128120 baseEnd_7128120 := by
    simpa [prefixWord, tailWord_7128120, baseEnd_7128120] using wordTrace_append hprefix tailTrace_7128120
  have hstable : (prefixWord ++ tailWord_7128120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128120).length < 2 ^ (prefixWord ++ tailWord_7128120).sum := by decide
  have hdescent : baseEnd_7128120 < baseStart_7128120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128170 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7128170 : Nat := 118140960795 + 7128170 * 2 ^ 59
def prefixEnd_7128170 : Nat := 4983230072969 + 3 ^ 40 * 7128170 * 2
def baseEnd_7128170 : Nat := 3660177396959481235793149

theorem tailTrace_7128170 : CollatzResearch.WordTrace tailWord_7128170 prefixEnd_7128170 3660177396959481235793149 := by
  unfold tailWord_7128170
  simp only [CollatzResearch.WordTrace]
  refine ⟨64996429646466239839845491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173323812390576639572921309 64996429646466239839845491)
  ·
    refine ⟨97494644469699359759768237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64996429646466239839845491 97494644469699359759768237)
    ·
      refine ⟨36560491676137259909913089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97494644469699359759768237 36560491676137259909913089)
      ·
        refine ⟨27420368757102944932434817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36560491676137259909913089 27420368757102944932434817)
        ·
          refine ⟨20565276567827208699326113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27420368757102944932434817 20565276567827208699326113)
          ·
            refine ⟨15423957425870406524494585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20565276567827208699326113 15423957425870406524494585)
            ·
              refine ⟨11567968069402804893370939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15423957425870406524494585 11567968069402804893370939)
              ·
                refine ⟨17351952104104207340056409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11567968069402804893370939 17351952104104207340056409)
                ·
                  refine ⟨13013964078078155505042307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17351952104104207340056409 13013964078078155505042307)
                  ·
                    refine ⟨19520946117117233257563461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13013964078078155505042307 19520946117117233257563461)
                    ·
                      refine ⟨3660177396959481235793149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19520946117117233257563461 3660177396959481235793149)
                      ·
                        rfl

theorem cell23_7128170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7128170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128170 prefixEnd_7128170 := by exact prefixLift 7128170
  have htrace : WordTrace (prefixWord ++ tailWord_7128170) baseStart_7128170 baseEnd_7128170 := by
    simpa [prefixWord, tailWord_7128170, baseEnd_7128170] using wordTrace_append hprefix tailTrace_7128170
  have hstable : (prefixWord ++ tailWord_7128170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128170).length < 2 ^ (prefixWord ++ tailWord_7128170).sum := by decide
  have hdescent : baseEnd_7128170 < baseStart_7128170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128193 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 6]
def baseStart_7128193 : Nat := 118140960795 + 7128193 * 2 ^ 59
def prefixEnd_7128193 : Nat := 4983230072969 + 3 ^ 40 * 7128193 * 2
def baseEnd_7128193 : Nat := 406687689668281627311727

theorem tailTrace_7128193 : CollatzResearch.WordTrace tailWord_7128193 prefixEnd_7128193 406687689668281627311727 := by
  unfold tailWord_7128193
  simp only [CollatzResearch.WordTrace]
  refine ⟨259986557464781634287469233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173324371643187756191646155 259986557464781634287469233)
  ·
    refine ⟨194989918098586225715601925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259986557464781634287469233 194989918098586225715601925)
    ·
      refine ⟨36560609643484917321675361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194989918098586225715601925 36560609643484917321675361)
      ·
        refine ⟨27420457232613687991256521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36560609643484917321675361 27420457232613687991256521)
        ·
          refine ⟨20565342924460265993442391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27420457232613687991256521 20565342924460265993442391)
          ·
            refine ⟨30848014386690398990163587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565342924460265993442391 30848014386690398990163587)
            ·
              refine ⟨46272021580035598485245381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30848014386690398990163587 46272021580035598485245381)
              ·
                refine ⟨8676004046256674715983509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46272021580035598485245381 8676004046256674715983509)
                ·
                  refine ⟨406687689668281627311727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8676004046256674715983509 406687689668281627311727)
                  ·
                    rfl

theorem cell23_7128193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_7128193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128193 prefixEnd_7128193 := by exact prefixLift 7128193
  have htrace : WordTrace (prefixWord ++ tailWord_7128193) baseStart_7128193 baseEnd_7128193 := by
    simpa [prefixWord, tailWord_7128193, baseEnd_7128193] using wordTrace_append hprefix tailTrace_7128193
  have hstable : (prefixWord ++ tailWord_7128193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128193).length < 2 ^ (prefixWord ++ tailWord_7128193).sum := by decide
  have hdescent : baseEnd_7128193 < baseStart_7128193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128197 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_7128197 : Nat := 118140960795 + 7128197 * 2 ^ 59
def prefixEnd_7128197 : Nat := 4983230072969 + 3 ^ 40 * 7128197 * 2
def baseEnd_7128197 : Nat := 1220063753645717543385175

theorem tailTrace_7128197 : CollatzResearch.WordTrace tailWord_7128197 prefixEnd_7128197 1220063753645717543385175 := by
  unfold tailWord_7128197
  simp only [CollatzResearch.WordTrace]
  refine ⟨259986703356767142970614845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173324468904511428647076563 259986703356767142970614845)
  ·
    refine ⟨97495013758787678613980567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259986703356767142970614845 97495013758787678613980567)
    ·
      refine ⟨146242520638181517920970851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97495013758787678613980567 146242520638181517920970851)
      ·
        refine ⟨219363780957272276881456277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146242520638181517920970851 219363780957272276881456277)
        ·
          refine ⟨10282677232372137978818263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219363780957272276881456277 10282677232372137978818263)
          ·
            refine ⟨15424015848558206968227395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282677232372137978818263 15424015848558206968227395)
            ·
              refine ⟨23136023772837310452341093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15424015848558206968227395 23136023772837310452341093)
              ·
                refine ⟨4338004457406995709813955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23136023772837310452341093 4338004457406995709813955)
                ·
                  refine ⟨6507006686110493564720933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338004457406995709813955 6507006686110493564720933)
                  ·
                    refine ⟨1220063753645717543385175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507006686110493564720933 1220063753645717543385175)
                    ·
                      rfl

theorem cell23_7128197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_7128197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128197 prefixEnd_7128197 := by exact prefixLift 7128197
  have htrace : WordTrace (prefixWord ++ tailWord_7128197) baseStart_7128197 baseEnd_7128197 := by
    simpa [prefixWord, tailWord_7128197, baseEnd_7128197] using wordTrace_append hprefix tailTrace_7128197
  have hstable : (prefixWord ++ tailWord_7128197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128197).length < 2 ^ (prefixWord ++ tailWord_7128197).sum := by decide
  have hdescent : baseEnd_7128197 < baseStart_7128197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128203 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 3]
def baseStart_7128203 : Nat := 118140960795 + 7128203 * 2 ^ 59
def prefixEnd_7128203 : Nat := 4983230072969 + 3 ^ 40 * 7128203 * 2
def baseEnd_7128203 : Nat := 3660194341821079606680497

theorem tailTrace_7128203 : CollatzResearch.WordTrace tailWord_7128203 prefixEnd_7128203 3660194341821079606680497 := by
  unfold tailWord_7128203
  simp only [CollatzResearch.WordTrace]
  refine ⟨259986922194745405995333263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173324614796496937330222175 259986922194745405995333263)
  ·
    refine ⟨389980383292118108992999895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259986922194745405995333263 389980383292118108992999895)
    ·
      refine ⟨584970574938177163489499843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389980383292118108992999895 584970574938177163489499843)
      ·
        refine ⟨877455862407265745234249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584970574938177163489499843 877455862407265745234249765)
        ·
          refine ⟨164522974201362327231421831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877455862407265745234249765 164522974201362327231421831)
          ·
            refine ⟨246784461302043490847132747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164522974201362327231421831 246784461302043490847132747)
            ·
              refine ⟨370176691953065236270699121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246784461302043490847132747 370176691953065236270699121)
              ·
                refine ⟨277632518964798927203024341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370176691953065236270699121 277632518964798927203024341)
                ·
                  refine ⟨6507012163237474856320883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 277632518964798927203024341 6507012163237474856320883)
                  ·
                    refine ⟨9760518244856212284481325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6507012163237474856320883 9760518244856212284481325)
                    ·
                      refine ⟨3660194341821079606680497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760518244856212284481325 3660194341821079606680497)
                      ·
                        rfl

theorem cell23_7128203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 3].length) (baseStart_7128203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128203 prefixEnd_7128203 := by exact prefixLift 7128203
  have htrace : WordTrace (prefixWord ++ tailWord_7128203) baseStart_7128203 baseEnd_7128203 := by
    simpa [prefixWord, tailWord_7128203, baseEnd_7128203] using wordTrace_append hprefix tailTrace_7128203
  have hstable : (prefixWord ++ tailWord_7128203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128203).length < 2 ^ (prefixWord ++ tailWord_7128203).sum := by decide
  have hdescent : baseEnd_7128203 < baseStart_7128203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128220 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7128220 : Nat := 118140960795 + 7128220 * 2 ^ 59
def prefixEnd_7128220 : Nat := 4983230072969 + 3 ^ 40 * 7128220 * 2
def baseEnd_7128220 : Nat := 3660203070992206040167919

theorem tailTrace_7128220 : CollatzResearch.WordTrace tailWord_7128220 prefixEnd_7128220 3660203070992206040167919 := by
  unfold tailWord_7128220
  simp only [CollatzResearch.WordTrace]
  refine ⟨129993771117841908949351057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173325028157122545265801409 129993771117841908949351057)
  ·
    refine ⟨97495328338381431712013293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129993771117841908949351057 97495328338381431712013293)
    ·
      refine ⟨36560748126893036892004985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97495328338381431712013293 36560748126893036892004985)
      ·
        refine ⟨27420561095169777669003739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36560748126893036892004985 27420561095169777669003739)
        ·
          refine ⟨41130841642754666503505609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27420561095169777669003739 41130841642754666503505609)
          ·
            refine ⟨30848131232065999877629207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41130841642754666503505609 30848131232065999877629207)
            ·
              refine ⟨46272196848098999816443811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30848131232065999877629207 46272196848098999816443811)
              ·
                refine ⟨69408295272148499724665717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46272196848098999816443811 69408295272148499724665717)
                ·
                  refine ⟨6507027681763921849187411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69408295272148499724665717 6507027681763921849187411)
                  ·
                    refine ⟨9760541522645882773781117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6507027681763921849187411 9760541522645882773781117)
                    ·
                      refine ⟨3660203070992206040167919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760541522645882773781117 3660203070992206040167919)
                      ·
                        rfl

theorem cell23_7128220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7128220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128220 prefixEnd_7128220 := by exact prefixLift 7128220
  have htrace : WordTrace (prefixWord ++ tailWord_7128220) baseStart_7128220 baseEnd_7128220 := by
    simpa [prefixWord, tailWord_7128220, baseEnd_7128220] using wordTrace_append hprefix tailTrace_7128220
  have hstable : (prefixWord ++ tailWord_7128220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128220).length < 2 ^ (prefixWord ++ tailWord_7128220).sum := by decide
  have hdescent : baseEnd_7128220 < baseStart_7128220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128236 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_7128236 : Nat := 118140960795 + 7128236 * 2 ^ 59
def prefixEnd_7128236 : Nat := 4983230072969 + 3 ^ 40 * 7128236 * 2
def baseEnd_7128236 : Nat := 1220070428894225992522615

theorem tailTrace_7128236 : CollatzResearch.WordTrace tailWord_7128236 prefixEnd_7128236 1220070428894225992522615 := by
  unfold tailWord_7128236
  simp only [CollatzResearch.WordTrace]
  refine ⟨129994062901812926315642281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173325417202417235087523041 129994062901812926315642281)
  ·
    refine ⟨97495547176359694736731711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129994062901812926315642281 97495547176359694736731711)
    ·
      refine ⟨146243320764539542105097567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97495547176359694736731711 146243320764539542105097567)
      ·
        refine ⟨219364981146809313157646351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146243320764539542105097567 219364981146809313157646351)
        ·
          refine ⟨329047471720213969736469527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219364981146809313157646351 329047471720213969736469527)
          ·
            refine ⟨493571207580320954604704291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329047471720213969736469527 493571207580320954604704291)
            ·
              refine ⟨740356811370481431907056437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493571207580320954604704291 740356811370481431907056437)
              ·
                refine ⟨69408451065982634241286541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740356811370481431907056437 69408451065982634241286541)
                ·
                  refine ⟨26028169149743487840482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69408451065982634241286541 26028169149743487840482453)
                  ·
                    refine ⟨1220070428894225992522615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26028169149743487840482453 1220070428894225992522615)
                    ·
                      rfl

theorem cell23_7128236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_7128236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128236 prefixEnd_7128236 := by exact prefixLift 7128236
  have htrace : WordTrace (prefixWord ++ tailWord_7128236) baseStart_7128236 baseEnd_7128236 := by
    simpa [prefixWord, tailWord_7128236, baseEnd_7128236] using wordTrace_append hprefix tailTrace_7128236
  have hstable : (prefixWord ++ tailWord_7128236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128236).length < 2 ^ (prefixWord ++ tailWord_7128236).sum := by decide
  have hdescent : baseEnd_7128236 < baseStart_7128236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128254 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_7128254 : Nat := 118140960795 + 7128254 * 2 ^ 59
def prefixEnd_7128254 : Nat := 4983230072969 + 3 ^ 40 * 7128254 * 2
def baseEnd_7128254 : Nat := 3660220529334458907142763

theorem tailTrace_7128254 : CollatzResearch.WordTrace tailWord_7128254 prefixEnd_7128254 3660220529334458907142763 := by
  unfold tailWord_7128254
  simp only [CollatzResearch.WordTrace]
  refine ⟨32498597789695080213179977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173325854878373761136959877 32498597789695080213179977)
  ·
    refine ⟨24373948342271310159884983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32498597789695080213179977 24373948342271310159884983)
    ·
      refine ⟨36560922513406965239827475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24373948342271310159884983 36560922513406965239827475)
      ·
        refine ⟨54841383770110447859741213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36560922513406965239827475 54841383770110447859741213)
        ·
          refine ⟨20565518913791417947402955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54841383770110447859741213 20565518913791417947402955)
          ·
            refine ⟨30848278370687126921104433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565518913791417947402955 30848278370687126921104433)
            ·
              refine ⟨23136208778015345190828325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30848278370687126921104433 23136208778015345190828325)
              ·
                refine ⟨4338039145877877223280311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23136208778015345190828325 4338039145877877223280311)
                ·
                  refine ⟨6507058718816815834920467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338039145877877223280311 6507058718816815834920467)
                  ·
                    refine ⟨9760588078225223752380701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6507058718816815834920467 9760588078225223752380701)
                    ·
                      refine ⟨3660220529334458907142763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760588078225223752380701 3660220529334458907142763)
                      ·
                        rfl

theorem cell23_7128254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_7128254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128254 prefixEnd_7128254 := by exact prefixLift 7128254
  have htrace : WordTrace (prefixWord ++ tailWord_7128254) baseStart_7128254 baseEnd_7128254 := by
    simpa [prefixWord, tailWord_7128254, baseEnd_7128254] using wordTrace_append hprefix tailTrace_7128254
  have hstable : (prefixWord ++ tailWord_7128254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128254).length < 2 ^ (prefixWord ++ tailWord_7128254).sum := by decide
  have hdescent : baseEnd_7128254 < baseStart_7128254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128263 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_7128263 : Nat := 118140960795 + 7128263 * 2 ^ 59
def prefixEnd_7128263 : Nat := 4983230072969 + 3 ^ 40 * 7128263 * 2
def baseEnd_7128263 : Nat := 3660225150660349371930221

theorem tailTrace_7128263 : CollatzResearch.WordTrace tailWord_7128263 prefixEnd_7128263 3660225150660349371930221 := by
  unfold tailWord_7128263
  simp only [CollatzResearch.WordTrace]
  refine ⟨259989110574528036242517443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173326073716352024161678295 259989110574528036242517443)
  ·
    refine ⟨389983665861792054363776165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259989110574528036242517443 389983665861792054363776165)
    ·
      refine ⟨73121937349086010193208031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389983665861792054363776165 73121937349086010193208031)
      ·
        refine ⟨109682906023629015289812047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73121937349086010193208031 109682906023629015289812047)
        ·
          refine ⟨164524359035443522934718071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109682906023629015289812047 164524359035443522934718071)
          ·
            refine ⟨246786538553165284402077107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164524359035443522934718071 246786538553165284402077107)
            ·
              refine ⟨370179807829747926603115661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246786538553165284402077107 370179807829747926603115661)
              ·
                refine ⟨138817427936155472476168373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370179807829747926603115661 138817427936155472476168373)
                ·
                  refine ⟨13014133869014575544640785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138817427936155472476168373 13014133869014575544640785)
                  ·
                    refine ⟨9760600401760931658480589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13014133869014575544640785 9760600401760931658480589)
                    ·
                      refine ⟨3660225150660349371930221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760600401760931658480589 3660225150660349371930221)
                      ·
                        rfl

theorem cell23_7128263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_7128263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128263 prefixEnd_7128263 := by exact prefixLift 7128263
  have htrace : WordTrace (prefixWord ++ tailWord_7128263) baseStart_7128263 baseEnd_7128263 := by
    simpa [prefixWord, tailWord_7128263, baseEnd_7128263] using wordTrace_append hprefix tailTrace_7128263
  have hstable : (prefixWord ++ tailWord_7128263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128263).length < 2 ^ (prefixWord ++ tailWord_7128263).sum := by decide
  have hdescent : baseEnd_7128263 < baseStart_7128263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128277 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7128277 : Nat := 118140960795 + 7128277 * 2 ^ 59
def prefixEnd_7128277 : Nat := 4983230072969 + 3 ^ 40 * 7128277 * 2
def baseEnd_7128277 : Nat := 3660232339389512317155157

theorem tailTrace_7128277 : CollatzResearch.WordTrace tailWord_7128277 prefixEnd_7128277 3660232339389512317155157 := by
  unfold tailWord_7128277
  simp only [CollatzResearch.WordTrace]
  refine ⟨259989621196477316633527085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173326414130984877755684723 259989621196477316633527085)
  ·
    refine ⟨97496107948678993737572657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259989621196477316633527085 97496107948678993737572657)
    ·
      refine ⟨73122080961509245303179493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97496107948678993737572657 73122080961509245303179493)
      ·
        refine ⟨13710390180282983494346155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73122080961509245303179493 13710390180282983494346155)
        ·
          refine ⟨20565585270424475241519233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710390180282983494346155 20565585270424475241519233)
          ·
            refine ⟨15424188952818356431139425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20565585270424475241519233 15424188952818356431139425)
            ·
              refine ⟨11568141714613767323354569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15424188952818356431139425 11568141714613767323354569)
              ·
                refine ⟨8676106285960325492515927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11568141714613767323354569 8676106285960325492515927)
                ·
                  refine ⟨13014159428940488238773891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676106285960325492515927 13014159428940488238773891)
                  ·
                    refine ⟨19521239143410732358160837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13014159428940488238773891 19521239143410732358160837)
                    ·
                      refine ⟨3660232339389512317155157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19521239143410732358160837 3660232339389512317155157)
                      ·
                        rfl

theorem cell23_7128277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7128277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128277 prefixEnd_7128277 := by exact prefixLift 7128277
  have htrace : WordTrace (prefixWord ++ tailWord_7128277) baseStart_7128277 baseEnd_7128277 := by
    simpa [prefixWord, tailWord_7128277, baseEnd_7128277] using wordTrace_append hprefix tailTrace_7128277
  have hstable : (prefixWord ++ tailWord_7128277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128277).length < 2 ^ (prefixWord ++ tailWord_7128277).sum := by decide
  have hdescent : baseEnd_7128277 < baseStart_7128277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128320 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2]
def baseStart_7128320 : Nat := 118140960795 + 7128320 * 2 ^ 59
def prefixEnd_7128320 : Nat := 4983230072969 + 3 ^ 40 * 7128320 * 2
def baseEnd_7128320 : Nat := 3660254419057655648917459

theorem tailTrace_7128320 : CollatzResearch.WordTrace tailWord_7128320 prefixEnd_7128320 3660254419057655648917459 := by
  unfold tailWord_7128320
  simp only [CollatzResearch.WordTrace]
  refine ⟨129995594767660767488671207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173327459690214356651561609 129995594767660767488671207)
  ·
    refine ⟨194993392151491151233006811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129995594767660767488671207 194993392151491151233006811)
    ·
      refine ⟨292490088227236726849510217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194993392151491151233006811 292490088227236726849510217)
      ·
        refine ⟨219367566170427545137132663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292490088227236726849510217 219367566170427545137132663)
        ·
          refine ⟨329051349255641317705698995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219367566170427545137132663 329051349255641317705698995)
          ·
            refine ⟨493577023883461976558548493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329051349255641317705698995 493577023883461976558548493)
            ·
              refine ⟨185091383956298241209455685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493577023883461976558548493 185091383956298241209455685)
              ·
                refine ⟨34704634491805920226772941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185091383956298241209455685 34704634491805920226772941)
                ·
                  refine ⟨13014237934427220085039853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34704634491805920226772941 13014237934427220085039853)
                  ·
                    refine ⟨4880339225410207531889945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13014237934427220085039853 4880339225410207531889945)
                    ·
                      refine ⟨3660254419057655648917459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880339225410207531889945 3660254419057655648917459)
                      ·
                        rfl

theorem cell23_7128320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_7128320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128320 prefixEnd_7128320 := by exact prefixLift 7128320
  have htrace : WordTrace (prefixWord ++ tailWord_7128320) baseStart_7128320 baseEnd_7128320 := by
    simpa [prefixWord, tailWord_7128320, baseEnd_7128320] using wordTrace_append hprefix tailTrace_7128320
  have hstable : (prefixWord ++ tailWord_7128320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128320).length < 2 ^ (prefixWord ++ tailWord_7128320).sum := by decide
  have hdescent : baseEnd_7128320 < baseStart_7128320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128370 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_7128370 : Nat := 118140960795 + 7128370 * 2 ^ 59
def prefixEnd_7128370 : Nat := 4983230072969 + 3 ^ 40 * 7128370 * 2
def baseEnd_7128370 : Nat := 3660280093090380453292229

theorem tailTrace_7128370 : CollatzResearch.WordTrace tailWord_7128370 prefixEnd_7128370 3660280093090380453292229 := by
  unfold tailWord_7128370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64998253296285098379165641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173328675456760262344441709 64998253296285098379165641)
  ·
    refine ⟨48748689972213823784374231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64998253296285098379165641 48748689972213823784374231)
    ·
      refine ⟨73123034958320735676561347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48748689972213823784374231 73123034958320735676561347)
      ·
        refine ⟨109684552437481103514842021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73123034958320735676561347 109684552437481103514842021)
        ·
          refine ⟨20565853582027706909032879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109684552437481103514842021 20565853582027706909032879)
          ·
            refine ⟨30848780373041560363549319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20565853582027706909032879 30848780373041560363549319)
            ·
              refine ⟨46273170559562340545323979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30848780373041560363549319 46273170559562340545323979)
              ·
                refine ⟨69409755839343510817985969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46273170559562340545323979 69409755839343510817985969)
                ·
                  refine ⟨52057316879507633113489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69409755839343510817985969 52057316879507633113489477)
                  ·
                    refine ⟨9760746914907681208779277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52057316879507633113489477 9760746914907681208779277)
                    ·
                      refine ⟨3660280093090380453292229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760746914907681208779277 3660280093090380453292229)
                      ·
                        rfl

theorem cell23_7128370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_7128370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128370 prefixEnd_7128370 := by exact prefixLift 7128370
  have htrace : WordTrace (prefixWord ++ tailWord_7128370) baseStart_7128370 baseEnd_7128370 := by
    simpa [prefixWord, tailWord_7128370, baseEnd_7128370] using wordTrace_append hprefix tailTrace_7128370
  have hstable : (prefixWord ++ tailWord_7128370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128370).length < 2 ^ (prefixWord ++ tailWord_7128370).sum := by decide
  have hdescent : baseEnd_7128370 < baseStart_7128370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128380 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_7128380 : Nat := 118140960795 + 7128380 * 2 ^ 59
def prefixEnd_7128380 : Nat := 4983230072969 + 3 ^ 40 * 7128380 * 2
def baseEnd_7128380 : Nat := 3660285227896925414167183

theorem tailTrace_7128380 : CollatzResearch.WordTrace tailWord_7128380 prefixEnd_7128380 3660285227896925414167183 := by
  unfold tailWord_7128380
  simp only [CollatzResearch.WordTrace]
  refine ⟨129996688957552082612263297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173328918610069443483017729 129996688957552082612263297)
  ·
    refine ⟨97497516718164061959197473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129996688957552082612263297 97497516718164061959197473)
    ·
      refine ⟨73123137538623046469398105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97497516718164061959197473 73123137538623046469398105)
      ·
        refine ⟨54842353153967284852048579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73123137538623046469398105 54842353153967284852048579)
        ·
          refine ⟨82263529730950927278072869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54842353153967284852048579 82263529730950927278072869)
          ·
            refine ⟨15424411824553298864638663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82263529730950927278072869 15424411824553298864638663)
            ·
              refine ⟨23136617736829948296957995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15424411824553298864638663 23136617736829948296957995)
              ·
                refine ⟨34704926605244922445436993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23136617736829948296957995 34704926605244922445436993)
                ·
                  refine ⟨26028694953933691834077745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34704926605244922445436993 26028694953933691834077745)
                  ·
                    refine ⟨19521521215450268875558309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26028694953933691834077745 19521521215450268875558309)
                    ·
                      refine ⟨3660285227896925414167183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19521521215450268875558309 3660285227896925414167183)
                      ·
                        rfl

theorem cell23_7128380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_7128380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128380 prefixEnd_7128380 := by exact prefixLift 7128380
  have htrace : WordTrace (prefixWord ++ tailWord_7128380) baseStart_7128380 baseEnd_7128380 := by
    simpa [prefixWord, tailWord_7128380, baseEnd_7128380] using wordTrace_append hprefix tailTrace_7128380
  have hstable : (prefixWord ++ tailWord_7128380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128380).length < 2 ^ (prefixWord ++ tailWord_7128380).sum := by decide
  have hdescent : baseEnd_7128380 < baseStart_7128380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128403 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 7]
def baseStart_7128403 : Nat := 118140960795 + 7128403 * 2 ^ 59
def prefixEnd_7128403 : Nat := 4983230072969 + 3 ^ 40 * 7128403 * 2
def baseEnd_7128403 : Nat := 1220099012650659608059859

theorem tailTrace_7128403 : CollatzResearch.WordTrace tailWord_7128403 prefixEnd_7128403 1220099012650659608059859 := by
  unfold tailWord_7128403
  simp only [CollatzResearch.WordTrace]
  refine ⟨259994216794020840152613863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173329477862680560101742575 259994216794020840152613863)
  ·
    refine ⟨389991325191031260228920795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259994216794020840152613863 389991325191031260228920795)
    ·
      refine ⟨584986987786546890343381193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389991325191031260228920795 584986987786546890343381193)
      ·
        refine ⟨438740240839910167757535895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584986987786546890343381193 438740240839910167757535895)
        ·
          refine ⟨658110361259865251636303843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438740240839910167757535895 658110361259865251636303843)
          ·
            refine ⟨987165541889797877454455765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658110361259865251636303843 987165541889797877454455765)
            ·
              refine ⟨23136692388042137752838807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 987165541889797877454455765 23136692388042137752838807)
              ·
                refine ⟨34705038582063206629258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23136692388042137752838807 34705038582063206629258211)
                ·
                  refine ⟨52057557873094809943887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34705038582063206629258211 52057557873094809943887317)
                  ·
                    refine ⟨1220099012650659608059859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52057557873094809943887317 1220099012650659608059859)
                    ·
                      rfl

theorem cell23_7128403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_7128403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128403 prefixEnd_7128403 := by exact prefixLift 7128403
  have htrace : WordTrace (prefixWord ++ tailWord_7128403) baseStart_7128403 baseEnd_7128403 := by
    simpa [prefixWord, tailWord_7128403, baseEnd_7128403] using wordTrace_append hprefix tailTrace_7128403
  have hstable : (prefixWord ++ tailWord_7128403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128403).length < 2 ^ (prefixWord ++ tailWord_7128403).sum := by decide
  have hdescent : baseEnd_7128403 < baseStart_7128403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128407 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 5]
def baseStart_7128407 : Nat := 118140960795 + 7128407 * 2 ^ 59
def prefixEnd_7128407 : Nat := 4983230072969 + 3 ^ 40 * 7128407 * 2
def baseEnd_7128407 : Nat := 406699899097177423169951

theorem tailTrace_7128407 : CollatzResearch.WordTrace tailWord_7128407 prefixEnd_7128407 406699899097177423169951 := by
  unfold tailWord_7128407
  simp only [CollatzResearch.WordTrace]
  refine ⟨259994362686006348835759475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173329575124004232557172983 259994362686006348835759475)
  ·
    refine ⟨389991544029009523253639213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259994362686006348835759475 389991544029009523253639213)
    ·
      refine ⟨146246829010878571220114705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389991544029009523253639213 146246829010878571220114705)
      ·
        refine ⟨109685121758158928415086029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146246829010878571220114705 109685121758158928415086029)
        ·
          refine ⟨41131920659309598155657261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109685121758158928415086029 41131920659309598155657261)
          ·
            refine ⟨15424470247241099308371473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41131920659309598155657261 15424470247241099308371473)
            ·
              refine ⟨11568352685430824481278605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15424470247241099308371473 11568352685430824481278605)
              ·
                refine ⟨4338132257036559180479477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11568352685430824481278605 4338132257036559180479477)
                ·
                  refine ⟨406699899097177423169951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338132257036559180479477 406699899097177423169951)
                  ·
                    rfl

theorem cell23_7128407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 5].length) (baseStart_7128407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128407 prefixEnd_7128407 := by exact prefixLift 7128407
  have htrace : WordTrace (prefixWord ++ tailWord_7128407) baseStart_7128407 baseEnd_7128407 := by
    simpa [prefixWord, tailWord_7128407, baseEnd_7128407] using wordTrace_append hprefix tailTrace_7128407
  have hstable : (prefixWord ++ tailWord_7128407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128407).length < 2 ^ (prefixWord ++ tailWord_7128407).sum := by decide
  have hdescent : baseEnd_7128407 < baseStart_7128407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128460 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_7128460 : Nat := 118140960795 + 7128460 * 2 ^ 59
def prefixEnd_7128460 : Nat := 4983230072969 + 3 ^ 40 * 7128460 * 2
def baseEnd_7128460 : Nat := 3660326306349285101166815

theorem tailTrace_7128460 : CollatzResearch.WordTrace tailWord_7128460 prefixEnd_7128460 3660326306349285101166815 := by
  unfold tailWord_7128460
  simp only [CollatzResearch.WordTrace]
  refine ⟨129998147877407169443719417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173330863836542892591625889 129998147877407169443719417)
  ·
    refine ⟨97498610908055377082789563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129998147877407169443719417 97498610908055377082789563)
    ·
      refine ⟨146247916362083065624184345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97498610908055377082789563 146247916362083065624184345)
      ·
        refine ⟨109685937271562299218138259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146247916362083065624184345 109685937271562299218138259)
        ·
          refine ⟨164528905907343448827207389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109685937271562299218138259 164528905907343448827207389)
          ·
            refine ⟨61698339715253793310202771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164528905907343448827207389 61698339715253793310202771)
            ·
              refine ⟨92547509572880689965304157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61698339715253793310202771 92547509572880689965304157)
              ·
                refine ⟨34705316089830258736989059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92547509572880689965304157 34705316089830258736989059)
                ·
                  refine ⟨52057974134745388105483589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34705316089830258736989059 52057974134745388105483589)
                  ·
                    refine ⟨9760870150264760269778173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52057974134745388105483589 9760870150264760269778173)
                    ·
                      refine ⟨3660326306349285101166815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760870150264760269778173 3660326306349285101166815)
                      ·
                        rfl

theorem cell23_7128460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_7128460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128460 prefixEnd_7128460 := by exact prefixLift 7128460
  have htrace : WordTrace (prefixWord ++ tailWord_7128460) baseStart_7128460 baseEnd_7128460 := by
    simpa [prefixWord, tailWord_7128460, baseEnd_7128460] using wordTrace_append hprefix tailTrace_7128460
  have hstable : (prefixWord ++ tailWord_7128460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128460).length < 2 ^ (prefixWord ++ tailWord_7128460).sum := by decide
  have hdescent : baseEnd_7128460 < baseStart_7128460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128477 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7128477 : Nat := 118140960795 + 7128477 * 2 ^ 59
def prefixEnd_7128477 : Nat := 4983230072969 + 3 ^ 40 * 7128477 * 2
def baseEnd_7128477 : Nat := 3660335035520411534654237

theorem tailTrace_7128477 : CollatzResearch.WordTrace tailWord_7128477 prefixEnd_7128477 3660335035520411534654237 := by
  unfold tailWord_7128477
  simp only [CollatzResearch.WordTrace]
  refine ⟨259996915795752750790807685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173331277197168500527205123 259996915795752750790807685)
  ·
    refine ⟨48749421711703640773276441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259996915795752750790807685 48749421711703640773276441)
    ·
      refine ⟨36562066283777730579957331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48749421711703640773276441 36562066283777730579957331)
      ·
        refine ⟨54843099425666595869935997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36562066283777730579957331 54843099425666595869935997)
        ·
          refine ⟨20566162284624973451225999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54843099425666595869935997 20566162284624973451225999)
          ·
            refine ⟨30849243426937460176838999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20566162284624973451225999 30849243426937460176838999)
            ·
              refine ⟨46273865140406190265258499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30849243426937460176838999 46273865140406190265258499)
              ·
                refine ⟨69410797710609285397887749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46273865140406190265258499 69410797710609285397887749)
                ·
                  refine ⟨13014524570739241012103953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69410797710609285397887749 13014524570739241012103953)
                  ·
                    refine ⟨9760893428054430759077965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13014524570739241012103953 9760893428054430759077965)
                    ·
                      refine ⟨3660335035520411534654237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9760893428054430759077965 3660335035520411534654237)
                      ·
                        rfl

theorem cell23_7128477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7128477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128477 prefixEnd_7128477 := by exact prefixLift 7128477
  have htrace : WordTrace (prefixWord ++ tailWord_7128477) baseStart_7128477 baseEnd_7128477 := by
    simpa [prefixWord, tailWord_7128477, baseEnd_7128477] using wordTrace_append hprefix tailTrace_7128477
  have hstable : (prefixWord ++ tailWord_7128477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128477).length < 2 ^ (prefixWord ++ tailWord_7128477).sum := by decide
  have hdescent : baseEnd_7128477 < baseStart_7128477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128480 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 6]
def baseStart_7128480 : Nat := 118140960795 + 7128480 * 2 ^ 59
def prefixEnd_7128480 : Nat := 4983230072969 + 3 ^ 40 * 7128480 * 2
def baseEnd_7128480 : Nat := 406704063995819446990747

theorem tailTrace_7128480 : CollatzResearch.WordTrace tailWord_7128480 prefixEnd_7128480 406704063995819446990747 := by
  unfold tailWord_7128480
  simp only [CollatzResearch.WordTrace]
  refine ⟨129998512607370941151583447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173331350143161254868777929 129998512607370941151583447)
  ·
    refine ⟨194997768911056411727375171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129998512607370941151583447 194997768911056411727375171)
    ·
      refine ⟨292496653366584617591062757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194997768911056411727375171 292496653366584617591062757)
      ·
        refine ⟨54843122506234615798324267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292496653366584617591062757 54843122506234615798324267)
        ·
          refine ⟨82264683759351923697486401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54843122506234615798324267 82264683759351923697486401)
          ·
            refine ⟨61698512819513942773114801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82264683759351923697486401 61698512819513942773114801)
            ·
              refine ⟨46273884614635457079836101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61698512819513942773114801 46273884614635457079836101)
              ·
                refine ⟨8676353365244148202469269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46273884614635457079836101 8676353365244148202469269)
                ·
                  refine ⟨406704063995819446990747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8676353365244148202469269 406704063995819446990747)
                  ·
                    rfl

theorem cell23_7128480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_7128480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128480 prefixEnd_7128480 := by exact prefixLift 7128480
  have htrace : WordTrace (prefixWord ++ tailWord_7128480) baseStart_7128480 baseEnd_7128480 := by
    simpa [prefixWord, tailWord_7128480, baseEnd_7128480] using wordTrace_append hprefix tailTrace_7128480
  have hstable : (prefixWord ++ tailWord_7128480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128480).length < 2 ^ (prefixWord ++ tailWord_7128480).sum := by decide
  have hdescent : baseEnd_7128480 < baseStart_7128480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128547 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7128547 : Nat := 118140960795 + 7128547 * 2 ^ 59
def prefixEnd_7128547 : Nat := 4983230072969 + 3 ^ 40 * 7128547 * 2
def baseEnd_7128547 : Nat := 3660370979166226260778915

theorem tailTrace_7128547 : CollatzResearch.WordTrace tailWord_7128547 prefixEnd_7128547 3660370979166226260778915 := by
  unfold tailWord_7128547
  simp only [CollatzResearch.WordTrace]
  refine ⟨259999468905499152745855895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173332979270332768497237263 259999468905499152745855895)
  ·
    refine ⟨389999203358248729118783843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259999468905499152745855895 389999203358248729118783843)
    ·
      refine ⟨584998805037373093678175765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389999203358248729118783843 584998805037373093678175765)
      ·
        refine ⟨27421818986126863766164489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 584998805037373093678175765 27421818986126863766164489)
        ·
          refine ⟨20566364239595147824623367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27421818986126863766164489 20566364239595147824623367)
          ·
            refine ⟨30849546359392721736935051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20566364239595147824623367 30849546359392721736935051)
            ·
              refine ⟨46274319539089082605402577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30849546359392721736935051 46274319539089082605402577)
              ·
                refine ⟨34705739654316811954051933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46274319539089082605402577 34705739654316811954051933)
                ·
                  refine ⟨13014652370368804482769475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34705739654316811954051933 13014652370368804482769475)
                  ·
                    refine ⟨19521978555553206724154213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13014652370368804482769475 19521978555553206724154213)
                    ·
                      refine ⟨3660370979166226260778915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19521978555553206724154213 3660370979166226260778915)
                      ·
                        rfl

theorem cell23_7128547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7128547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128547 prefixEnd_7128547 := by exact prefixLift 7128547
  have htrace : WordTrace (prefixWord ++ tailWord_7128547) baseStart_7128547 baseEnd_7128547 := by
    simpa [prefixWord, tailWord_7128547, baseEnd_7128547] using wordTrace_append hprefix tailTrace_7128547
  have hstable : (prefixWord ++ tailWord_7128547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128547).length < 2 ^ (prefixWord ++ tailWord_7128547).sum := by decide
  have hdescent : baseEnd_7128547 < baseStart_7128547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128578 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7128578 : Nat := 118140960795 + 7128578 * 2 ^ 59
def prefixEnd_7128578 : Nat := 4983230072969 + 3 ^ 40 * 7128578 * 2
def baseEnd_7128578 : Nat := 1220128965688838546497091

theorem tailTrace_7128578 : CollatzResearch.WordTrace tailWord_7128578 prefixEnd_7128578 1220128965688838546497091 := by
  unfold tailWord_7128578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65000149892096711260058597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173333733045591230026822925 65000149892096711260058597)
  ·
    refine ⟨12187528104768133361260987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65000149892096711260058597 12187528104768133361260987)
    ·
      refine ⟨18281292157152200041891481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12187528104768133361260987 18281292157152200041891481)
      ·
        refine ⟨13710969117864150031418611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18281292157152200041891481 13710969117864150031418611)
        ·
          refine ⟨20566453676796225047127917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710969117864150031418611 20566453676796225047127917)
          ·
            refine ⟨7712420128798584392672969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20566453676796225047127917 7712420128798584392672969)
            ·
              refine ⟨5784315096598938294504727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7712420128798584392672969 5784315096598938294504727)
              ·
                refine ⟨8676472644898407441757091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784315096598938294504727 8676472644898407441757091)
                ·
                  refine ⟨13014708967347611162635637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676472644898407441757091 13014708967347611162635637)
                  ·
                    refine ⟨1220128965688838546497091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13014708967347611162635637 1220128965688838546497091)
                    ·
                      rfl

theorem cell23_7128578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7128578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128578 prefixEnd_7128578 := by exact prefixLift 7128578
  have htrace : WordTrace (prefixWord ++ tailWord_7128578) baseStart_7128578 baseEnd_7128578 := by
    simpa [prefixWord, tailWord_7128578, baseEnd_7128578] using wordTrace_append hprefix tailTrace_7128578
  have hstable : (prefixWord ++ tailWord_7128578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128578).length < 2 ^ (prefixWord ++ tailWord_7128578).sum := by decide
  have hdescent : baseEnd_7128578 < baseStart_7128578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128611 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 2, 4]
def baseStart_7128611 : Nat := 118140960795 + 7128611 * 2 ^ 59
def prefixEnd_7128611 : Nat := 4983230072969 + 3 ^ 40 * 7128611 * 2
def baseEnd_7128611 : Nat := 3660403841928114010378621

theorem tailTrace_7128611 : CollatzResearch.WordTrace tailWord_7128611 prefixEnd_7128611 3660403841928114010378621 := by
  unfold tailWord_7128611
  simp only [CollatzResearch.WordTrace]
  refine ⟨260001803177267291676185687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173334535451511527784123791 260001803177267291676185687)
  ·
    refine ⟨390002704765900937514278531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260001803177267291676185687 390002704765900937514278531)
    ·
      refine ⟨585004057148851406271417797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390002704765900937514278531 585004057148851406271417797)
      ·
        refine ⟨109688260715409638675890837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585004057148851406271417797 109688260715409638675890837)
        ·
          refine ⟨5141637221034826812932383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109688260715409638675890837 5141637221034826812932383)
          ·
            refine ⟨7712455831552240219398575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141637221034826812932383 7712455831552240219398575)
            ·
              refine ⟨11568683747328360329097863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712455831552240219398575 11568683747328360329097863)
              ·
                refine ⟨17353025620992540493646795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11568683747328360329097863 17353025620992540493646795)
                ·
                  refine ⟨26029538431488810740470193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17353025620992540493646795 26029538431488810740470193)
                  ·
                    refine ⟨19522153823616608055352645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26029538431488810740470193 19522153823616608055352645)
                    ·
                      refine ⟨3660403841928114010378621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19522153823616608055352645 3660403841928114010378621)
                      ·
                        rfl

theorem cell23_7128611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_7128611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128611 prefixEnd_7128611 := by exact prefixLift 7128611
  have htrace : WordTrace (prefixWord ++ tailWord_7128611) baseStart_7128611 baseEnd_7128611 := by
    simpa [prefixWord, tailWord_7128611, baseEnd_7128611] using wordTrace_append hprefix tailTrace_7128611
  have hstable : (prefixWord ++ tailWord_7128611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128611).length < 2 ^ (prefixWord ++ tailWord_7128611).sum := by decide
  have hdescent : baseEnd_7128611 < baseStart_7128611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128641 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7128641 : Nat := 118140960795 + 7128641 * 2 ^ 59
def prefixEnd_7128641 : Nat := 4983230072969 + 3 ^ 40 * 7128641 * 2
def baseEnd_7128641 : Nat := 3660419246347748893003483

theorem tailTrace_7128641 : CollatzResearch.WordTrace tailWord_7128641 prefixEnd_7128641 3660419246347748893003483 := by
  unfold tailWord_7128641
  simp only [CollatzResearch.WordTrace]
  refine ⟨260002897367158606799777777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173335264911439071199851851 260002897367158606799777777)
  ·
    refine ⟨195002173025368955099833333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260002897367158606799777777 195002173025368955099833333)
    ·
      refine ⟨18281453721128339540609375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195002173025368955099833333 18281453721128339540609375)
      ·
        refine ⟨27422180581692509310914063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18281453721128339540609375 27422180581692509310914063)
        ·
          refine ⟨41133270872538763966371095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27422180581692509310914063 41133270872538763966371095)
          ·
            refine ⟨61699906308808145949556643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41133270872538763966371095 61699906308808145949556643)
            ·
              refine ⟨92549859463212218924334965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61699906308808145949556643 92549859463212218924334965)
              ·
                refine ⟨8676549324676145524156403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92549859463212218924334965 8676549324676145524156403)
                ·
                  refine ⟨13014823987014218286234605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676549324676145524156403 13014823987014218286234605)
                  ·
                    refine ⟨4880558995130331857337977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13014823987014218286234605 4880558995130331857337977)
                    ·
                      refine ⟨3660419246347748893003483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880558995130331857337977 3660419246347748893003483)
                      ·
                        rfl

theorem cell23_7128641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7128641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128641 prefixEnd_7128641 := by exact prefixLift 7128641
  have htrace : WordTrace (prefixWord ++ tailWord_7128641) baseStart_7128641 baseEnd_7128641 := by
    simpa [prefixWord, tailWord_7128641, baseEnd_7128641] using wordTrace_append hprefix tailTrace_7128641
  have hstable : (prefixWord ++ tailWord_7128641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128641).length < 2 ^ (prefixWord ++ tailWord_7128641).sum := by decide
  have hdescent : baseEnd_7128641 < baseStart_7128641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128657 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_7128657 : Nat := 118140960795 + 7128657 * 2 ^ 59
def prefixEnd_7128657 : Nat := 4983230072969 + 3 ^ 40 * 7128657 * 2
def baseEnd_7128657 : Nat := 3660427462038220830403409

theorem tailTrace_7128657 : CollatzResearch.WordTrace tailWord_7128657 prefixEnd_7128657 3660427462038220830403409 := by
  unfold tailWord_7128657
  simp only [CollatzResearch.WordTrace]
  refine ⟨260003480935100641532360225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173335653956733761021573483 260003480935100641532360225)
  ·
    refine ⟨195002610701325481149270169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260003480935100641532360225 195002610701325481149270169)
    ·
      refine ⟨146251958025994110861952627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195002610701325481149270169 146251958025994110861952627)
      ·
        refine ⟨219377937038991166292928941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146251958025994110861952627 219377937038991166292928941)
        ·
          refine ⟨82266726389621687359848353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219377937038991166292928941 82266726389621687359848353)
          ·
            refine ⟨61700044792216265519886265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82266726389621687359848353 61700044792216265519886265)
            ·
              refine ⟨46275033594162199139914699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61700044792216265519886265 46275033594162199139914699)
              ·
                refine ⟨69412550391243298709872049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46275033594162199139914699 69412550391243298709872049)
                ·
                  refine ⟨52059412793432474032404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69412550391243298709872049 52059412793432474032404037)
                  ·
                    refine ⟨9761139898768588881075757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52059412793432474032404037 9761139898768588881075757)
                    ·
                      refine ⟨3660427462038220830403409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9761139898768588881075757 3660427462038220830403409)
                      ·
                        rfl

theorem cell23_7128657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_7128657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128657 prefixEnd_7128657 := by exact prefixLift 7128657
  have htrace : WordTrace (prefixWord ++ tailWord_7128657) baseStart_7128657 baseEnd_7128657 := by
    simpa [prefixWord, tailWord_7128657, baseEnd_7128657] using wordTrace_append hprefix tailTrace_7128657
  have hstable : (prefixWord ++ tailWord_7128657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128657).length < 2 ^ (prefixWord ++ tailWord_7128657).sum := by decide
  have hdescent : baseEnd_7128657 < baseStart_7128657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128687 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_7128687 : Nat := 118140960795 + 7128687 * 2 ^ 59
def prefixEnd_7128687 : Nat := 4983230072969 + 3 ^ 40 * 7128687 * 2
def baseEnd_7128687 : Nat := 3660442866457855713028271

theorem tailTrace_7128687 : CollatzResearch.WordTrace tailWord_7128687 prefixEnd_7128687 3660442866457855713028271 := by
  unfold tailWord_7128687
  simp only [CollatzResearch.WordTrace]
  refine ⟨260004575124991956655952315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173336383416661304437301543 260004575124991956655952315)
  ·
    refine ⟨390006862687487934983928473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260004575124991956655952315 390006862687487934983928473)
    ·
      refine ⟨292505147015615951237946355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390006862687487934983928473 292505147015615951237946355)
      ·
        refine ⟨438757720523423926856919533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292505147015615951237946355 438757720523423926856919533)
        ·
          refine ⟨164534145196283972571344825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438757720523423926856919533 164534145196283972571344825)
          ·
            refine ⟨123400608897212979428508619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164534145196283972571344825 123400608897212979428508619)
            ·
              refine ⟨185100913345819469142762929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123400608897212979428508619 185100913345819469142762929)
              ·
                refine ⟨138825685009364601857072197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185100913345819469142762929 138825685009364601857072197)
                ·
                  refine ⟨26029815939255862848201037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138825685009364601857072197 26029815939255862848201037)
                  ·
                    refine ⟨9761180977220948568075389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26029815939255862848201037 9761180977220948568075389)
                    ·
                      refine ⟨3660442866457855713028271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9761180977220948568075389 3660442866457855713028271)
                      ·
                        rfl

theorem cell23_7128687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_7128687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128687 prefixEnd_7128687 := by exact prefixLift 7128687
  have htrace : WordTrace (prefixWord ++ tailWord_7128687) baseStart_7128687 baseEnd_7128687 := by
    simpa [prefixWord, tailWord_7128687, baseEnd_7128687] using wordTrace_append hprefix tailTrace_7128687
  have hstable : (prefixWord ++ tailWord_7128687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128687).length < 2 ^ (prefixWord ++ tailWord_7128687).sum := by decide
  have hdescent : baseEnd_7128687 < baseStart_7128687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128711 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 5]
def baseStart_7128711 : Nat := 118140960795 + 7128711 * 2 ^ 59
def prefixEnd_7128711 : Nat := 4983230072969 + 3 ^ 40 * 7128711 * 2
def baseEnd_7128711 : Nat := 406717243332618179903129

theorem tailTrace_7128711 : CollatzResearch.WordTrace tailWord_7128711 prefixEnd_7128711 406717243332618179903129 := by
  unfold tailWord_7128711
  simp only [CollatzResearch.WordTrace]
  refine ⟨260005450476905008754825987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173336966984603339169883991 260005450476905008754825987)
  ·
    refine ⟨390008175715357513132238981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260005450476905008754825987 390008175715357513132238981)
    ·
      refine ⟨73126532946629533712294809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390008175715357513132238981 73126532946629533712294809)
      ·
        refine ⟨54844899709972150284221107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73126532946629533712294809 54844899709972150284221107)
        ·
          refine ⟨82267349564958225426331661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54844899709972150284221107 82267349564958225426331661)
          ·
            refine ⟨30850256086859334534874373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82267349564958225426331661 30850256086859334534874373)
            ·
              refine ⟨5784423016286125225288945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30850256086859334534874373 5784423016286125225288945)
              ·
                refine ⟨4338317262214593918966709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5784423016286125225288945 4338317262214593918966709)
                ·
                  refine ⟨406717243332618179903129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338317262214593918966709 406717243332618179903129)
                  ·
                    rfl

theorem cell23_7128711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 5].length) (baseStart_7128711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128711 prefixEnd_7128711 := by exact prefixLift 7128711
  have htrace : WordTrace (prefixWord ++ tailWord_7128711) baseStart_7128711 baseEnd_7128711 := by
    simpa [prefixWord, tailWord_7128711, baseEnd_7128711] using wordTrace_append hprefix tailTrace_7128711
  have hstable : (prefixWord ++ tailWord_7128711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128711).length < 2 ^ (prefixWord ++ tailWord_7128711).sum := by decide
  have hdescent : baseEnd_7128711 < baseStart_7128711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128767 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 8]
def baseStart_7128767 : Nat := 118140960795 + 7128767 * 2 ^ 59
def prefixEnd_7128767 : Nat := 4983230072969 + 3 ^ 40 * 7128767 * 2
def baseEnd_7128767 : Nat := 406720438323357266669767

theorem tailTrace_7128767 : CollatzResearch.WordTrace tailWord_7128767 prefixEnd_7128767 406720438323357266669767 := by
  unfold tailWord_7128767
  simp only [CollatzResearch.WordTrace]
  refine ⟨260007492964702130318864555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173338328643134753545909703 260007492964702130318864555)
  ·
    refine ⟨390011239447053195478296833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260007492964702130318864555 390011239447053195478296833)
    ·
      refine ⟨292508429585289896608722625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390011239447053195478296833 292508429585289896608722625)
      ·
        refine ⟨219381322188967422456541969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292508429585289896608722625 219381322188967422456541969)
        ·
          refine ⟨164535991641725566842406477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219381322188967422456541969 164535991641725566842406477)
          ·
            refine ⟨61700996865647087565902429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164535991641725566842406477 61700996865647087565902429)
            ·
              refine ⟨23137873824617657837213411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61700996865647087565902429 23137873824617657837213411)
              ·
                refine ⟨34706810736926486755820117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23137873824617657837213411 34706810736926486755820117)
                ·
                  refine ⟨406720438323357266669767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34706810736926486755820117 406720438323357266669767)
                  ·
                    rfl

theorem cell23_7128767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 8].length) (baseStart_7128767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128767 prefixEnd_7128767 := by exact prefixLift 7128767
  have htrace : WordTrace (prefixWord ++ tailWord_7128767) baseStart_7128767 baseEnd_7128767 := by
    simpa [prefixWord, tailWord_7128767, baseEnd_7128767] using wordTrace_append hprefix tailTrace_7128767
  have hstable : (prefixWord ++ tailWord_7128767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128767).length < 2 ^ (prefixWord ++ tailWord_7128767).sum := by decide
  have hdescent : baseEnd_7128767 < baseStart_7128767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 6]
def baseStart_7128827 : Nat := 118140960795 + 7128827 * 2 ^ 59
def prefixEnd_7128827 : Nat := 4983230072969 + 3 ^ 40 * 7128827 * 2
def baseEnd_7128827 : Nat := 1220171584583161721759209

theorem tailTrace_7128827 : CollatzResearch.WordTrace tailWord_7128827 prefixEnd_7128827 1220171584583161721759209 := by
  unfold tailWord_7128827
  simp only [CollatzResearch.WordTrace]
  refine ⟨260009681344484760566048735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173339787562989840377365823 260009681344484760566048735)
  ·
    refine ⟨390014522016727140849073103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260009681344484760566048735 390014522016727140849073103)
    ·
      refine ⟨585021783025090711273609655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390014522016727140849073103 585021783025090711273609655)
      ·
        refine ⟨877532674537636066910414483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585021783025090711273609655 877532674537636066910414483)
        ·
          refine ⟨1316299011806454100365621725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877532674537636066910414483 1316299011806454100365621725)
          ·
            refine ⟨493612129427420287637108147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1316299011806454100365621725 493612129427420287637108147)
            ·
              refine ⟨740418194141130431455662221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493612129427420287637108147 740418194141130431455662221)
              ·
                refine ⟨277656822802923911795873333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740418194141130431455662221 277656822802923911795873333)
                ·
                  refine ⟨26030327137774116730863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277656822802923911795873333 26030327137774116730863125)
                  ·
                    refine ⟨1220171584583161721759209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26030327137774116730863125 1220171584583161721759209)
                    ·
                      rfl

theorem cell23_7128827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_7128827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128827 prefixEnd_7128827 := by exact prefixLift 7128827
  have htrace : WordTrace (prefixWord ++ tailWord_7128827) baseStart_7128827 baseEnd_7128827 := by
    simpa [prefixWord, tailWord_7128827, baseEnd_7128827] using wordTrace_append hprefix tailTrace_7128827
  have hstable : (prefixWord ++ tailWord_7128827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128827).length < 2 ^ (prefixWord ++ tailWord_7128827).sum := by decide
  have hdescent : baseEnd_7128827 < baseStart_7128827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128901 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_7128901 : Nat := 118140960795 + 7128901 * 2 ^ 59
def prefixEnd_7128901 : Nat := 4983230072969 + 3 ^ 40 * 7128901 * 2
def baseEnd_7128901 : Nat := 3660552751317917875752287

theorem tailTrace_7128901 : CollatzResearch.WordTrace tailWord_7128901 prefixEnd_7128901 3660552751317917875752287 := by
  unfold tailWord_7128901
  simp only [CollatzResearch.WordTrace]
  refine ⟨260012380346216671204242557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173341586897477780802828371 260012380346216671204242557)
  ·
    refine ⟨97504642629831251701590959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260012380346216671204242557 97504642629831251701590959)
    ·
      refine ⟨146256963944746877552386439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97504642629831251701590959 146256963944746877552386439)
      ·
        refine ⟨219385445917120316328579659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146256963944746877552386439 219385445917120316328579659)
        ·
          refine ⟨329078168875680474492869489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219385445917120316328579659 329078168875680474492869489)
          ·
            refine ⟨246808626656760355869652117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329078168875680474492869489 246808626656760355869652117)
            ·
              refine ⟨11569154374535641681389943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246808626656760355869652117 11569154374535641681389943)
              ·
                refine ⟨17353731561803462522084915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11569154374535641681389943 17353731561803462522084915)
                ·
                  refine ⟨26030597342705193783127373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17353731561803462522084915 26030597342705193783127373)
                  ·
                    refine ⟨9761474003514447668672765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26030597342705193783127373 9761474003514447668672765)
                    ·
                      refine ⟨3660552751317917875752287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9761474003514447668672765 3660552751317917875752287)
                      ·
                        rfl

theorem cell23_7128901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_7128901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128901 prefixEnd_7128901 := by exact prefixLift 7128901
  have htrace : WordTrace (prefixWord ++ tailWord_7128901) baseStart_7128901 baseEnd_7128901 := by
    simpa [prefixWord, tailWord_7128901, baseEnd_7128901] using wordTrace_append hprefix tailTrace_7128901
  have hstable : (prefixWord ++ tailWord_7128901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128901).length < 2 ^ (prefixWord ++ tailWord_7128901).sum := by decide
  have hdescent : baseEnd_7128901 < baseStart_7128901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128902 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7128902 : Nat := 118140960795 + 7128902 * 2 ^ 59
def prefixEnd_7128902 : Nat := 4983230072969 + 3 ^ 40 * 7128902 * 2
def baseEnd_7128902 : Nat := 3660553264798572371839783

theorem tailTrace_7128902 : CollatzResearch.WordTrace tailWord_7128902 prefixEnd_7128902 3660553264798572371839783 := by
  unfold tailWord_7128902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125388025600407761719655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173341611212808698916685973 8125388025600407761719655)
  ·
    refine ⟨12188082038400611642579483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125388025600407761719655 12188082038400611642579483)
    ·
      refine ⟨18282123057600917463869225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188082038400611642579483 18282123057600917463869225)
      ·
        refine ⟨13711592293200688097901919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18282123057600917463869225 13711592293200688097901919)
        ·
          refine ⟨20567388439801032146852879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711592293200688097901919 20567388439801032146852879)
          ·
            refine ⟨30851082659701548220279319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20567388439801032146852879 30851082659701548220279319)
            ·
              refine ⟨46276623989552322330418979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30851082659701548220279319 46276623989552322330418979)
              ·
                refine ⟨69414935984328483495628469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46276623989552322330418979 69414935984328483495628469)
                ·
                  refine ⟨6507650248530795327715169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69414935984328483495628469 6507650248530795327715169)
                  ·
                    refine ⟨4880737686398096495786377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6507650248530795327715169 4880737686398096495786377)
                    ·
                      refine ⟨3660553264798572371839783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880737686398096495786377 3660553264798572371839783)
                      ·
                        rfl

theorem cell23_7128902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7128902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128902 prefixEnd_7128902 := by exact prefixLift 7128902
  have htrace : WordTrace (prefixWord ++ tailWord_7128902) baseStart_7128902 baseEnd_7128902 := by
    simpa [prefixWord, tailWord_7128902, baseEnd_7128902] using wordTrace_append hprefix tailTrace_7128902
  have hstable : (prefixWord ++ tailWord_7128902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128902).length < 2 ^ (prefixWord ++ tailWord_7128902).sum := by decide
  have hdescent : baseEnd_7128902 < baseStart_7128902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128944 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_7128944 : Nat := 118140960795 + 7128944 * 2 ^ 59
def prefixEnd_7128944 : Nat := 4983230072969 + 3 ^ 40 * 7128944 * 2
def baseEnd_7128944 : Nat := 3660574830986061207514589

theorem tailTrace_7128944 : CollatzResearch.WordTrace tailWord_7128944 prefixEnd_7128944 3660574830986061207514589 := by
  unfold tailWord_7128944
  simp only [CollatzResearch.WordTrace]
  refine ⟨130006974342530444774028943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173342632456707259698705257 130006974342530444774028943)
  ·
    refine ⟨195010461513795667161043415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130006974342530444774028943 195010461513795667161043415)
    ·
      refine ⟨292515692270693500741565123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195010461513795667161043415 292515692270693500741565123)
      ·
        refine ⟨438773538406040251112347685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292515692270693500741565123 438773538406040251112347685)
        ·
          refine ⟨82270038451132547083565191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438773538406040251112347685 82270038451132547083565191)
          ·
            refine ⟨123405057676698820625347787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82270038451132547083565191 123405057676698820625347787)
            ·
              refine ⟨185107586515048230938021681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123405057676698820625347787 185107586515048230938021681)
              ·
                refine ⟨138830689886286173203516261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185107586515048230938021681 138830689886286173203516261)
                ·
                  refine ⟨26030754353678657475659299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138830689886286173203516261 26030754353678657475659299)
                  ·
                    refine ⟨39046131530517986213488949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26030754353678657475659299 39046131530517986213488949)
                    ·
                      refine ⟨3660574830986061207514589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39046131530517986213488949 3660574830986061207514589)
                      ·
                        rfl

theorem cell23_7128944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_7128944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128944 prefixEnd_7128944 := by exact prefixLift 7128944
  have htrace : WordTrace (prefixWord ++ tailWord_7128944) baseStart_7128944 baseEnd_7128944 := by
    simpa [prefixWord, tailWord_7128944, baseEnd_7128944] using wordTrace_append hprefix tailTrace_7128944
  have hstable : (prefixWord ++ tailWord_7128944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128944).length < 2 ^ (prefixWord ++ tailWord_7128944).sum := by decide
  have hdescent : baseEnd_7128944 < baseStart_7128944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128978 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7128978 : Nat := 118140960795 + 7128978 * 2 ^ 59
def prefixEnd_7128978 : Nat := 4983230072969 + 3 ^ 40 * 7128978 * 2
def baseEnd_7128978 : Nat := 3660592289328314074489433

theorem tailTrace_7128978 : CollatzResearch.WordTrace tailWord_7128978 prefixEnd_7128978 3660592289328314074489433 := by
  unfold tailWord_7128978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65003797191734428338698897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173343459177958475569863725 65003797191734428338698897)
  ·
    refine ⟨48752847893800821254024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65003797191734428338698897 48752847893800821254024173)
    ·
      refine ⟨18282317960175307970259065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48752847893800821254024173 18282317960175307970259065)
      ·
        refine ⟨13711738470131480977694299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18282317960175307970259065 13711738470131480977694299)
        ·
          refine ⟨20567607705197221466541449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13711738470131480977694299 20567607705197221466541449)
          ·
            refine ⟨15425705778897916099906087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20567607705197221466541449 15425705778897916099906087)
            ·
              refine ⟨23138558668346874149859131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425705778897916099906087 23138558668346874149859131)
              ·
                refine ⟨34707838002520311224788697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23138558668346874149859131 34707838002520311224788697)
                ·
                  refine ⟨26030878501890233418591523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34707838002520311224788697 26030878501890233418591523)
                  ·
                    refine ⟨39046317752835350127887285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26030878501890233418591523 39046317752835350127887285)
                    ·
                      refine ⟨3660592289328314074489433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39046317752835350127887285 3660592289328314074489433)
                      ·
                        rfl

theorem cell23_7128978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7128978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7128978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7128978 prefixEnd_7128978 := by exact prefixLift 7128978
  have htrace : WordTrace (prefixWord ++ tailWord_7128978) baseStart_7128978 baseEnd_7128978 := by
    simpa [prefixWord, tailWord_7128978, baseEnd_7128978] using wordTrace_append hprefix tailTrace_7128978
  have hstable : (prefixWord ++ tailWord_7128978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128978).length < 2 ^ (prefixWord ++ tailWord_7128978).sum := by decide
  have hdescent : baseEnd_7128978 < baseStart_7128978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129009 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7129009 : Nat := 118140960795 + 7129009 * 2 ^ 59
def prefixEnd_7129009 : Nat := 4983230072969 + 3 ^ 40 * 7129009 * 2
def baseEnd_7129009 : Nat := 3660608207228603453201791

theorem tailTrace_7129009 : CollatzResearch.WordTrace tailWord_7129009 prefixEnd_7129009 3660608207228603453201791 := by
  unfold tailWord_7129009
  simp only [CollatzResearch.WordTrace]
  refine ⟨260016319429825405649174081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173344212953216937099449387 260016319429825405649174081)
  ·
    refine ⟨195012239572369054236880561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260016319429825405649174081 195012239572369054236880561)
    ·
      refine ⟨146259179679276790677660421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195012239572369054236880561 146259179679276790677660421)
      ·
        refine ⟨27423596189864398252061329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146259179679276790677660421 27423596189864398252061329)
        ·
          refine ⟨20567697142398298689045997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27423596189864398252061329 20567697142398298689045997)
          ·
            refine ⟨7712886428399362008392249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20567697142398298689045997 7712886428399362008392249)
            ·
              refine ⟨5784664821299521506294187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7712886428399362008392249 5784664821299521506294187)
              ·
                refine ⟨8676997231949282259441281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784664821299521506294187 8676997231949282259441281)
                ·
                  refine ⟨6507747923961961694580961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676997231949282259441281 6507747923961961694580961)
                  ·
                    refine ⟨4880810942971471270935721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6507747923961961694580961 4880810942971471270935721)
                    ·
                      refine ⟨3660608207228603453201791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880810942971471270935721 3660608207228603453201791)
                      ·
                        rfl

theorem cell23_7129009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7129009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129009 prefixEnd_7129009 := by exact prefixLift 7129009
  have htrace : WordTrace (prefixWord ++ tailWord_7129009) baseStart_7129009 baseEnd_7129009 := by
    simpa [prefixWord, tailWord_7129009, baseEnd_7129009] using wordTrace_append hprefix tailTrace_7129009
  have hstable : (prefixWord ++ tailWord_7129009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129009).length < 2 ^ (prefixWord ++ tailWord_7129009).sum := by decide
  have hdescent : baseEnd_7129009 < baseStart_7129009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129041 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_7129041 : Nat := 118140960795 + 7129041 * 2 ^ 59
def prefixEnd_7129041 : Nat := 4983230072969 + 3 ^ 40 * 7129041 * 2
def baseEnd_7129041 : Nat := 1220208212869849109333881

theorem tailTrace_7129041 : CollatzResearch.WordTrace tailWord_7129041 prefixEnd_7129041 1220208212869849109333881 := by
  unfold tailWord_7129041
  simp only [CollatzResearch.WordTrace]
  refine ⟨260017486565709475114338977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173344991043806316742892651 260017486565709475114338977)
  ·
    refine ⟨195013114924282106335754233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260017486565709475114338977 195013114924282106335754233)
    ·
      refine ⟨146259836193211579751815675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195013114924282106335754233 146259836193211579751815675)
      ·
        refine ⟨219389754289817369627723513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146259836193211579751815675 219389754289817369627723513)
        ·
          refine ⟨164542315717363027220792635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219389754289817369627723513 164542315717363027220792635)
          ·
            refine ⟨246813473576044540831188953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164542315717363027220792635 246813473576044540831188953)
            ·
              refine ⟨185110105182033405623391715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246813473576044540831188953 185110105182033405623391715)
              ·
                refine ⟨277665157773050108435087573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185110105182033405623391715 277665157773050108435087573)
                ·
                  refine ⟨6507777135305861916447365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 277665157773050108435087573 6507777135305861916447365)
                  ·
                    refine ⟨1220208212869849109333881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507777135305861916447365 1220208212869849109333881)
                    ·
                      rfl

theorem cell23_7129041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_7129041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129041 prefixEnd_7129041 := by exact prefixLift 7129041
  have htrace : WordTrace (prefixWord ++ tailWord_7129041) baseStart_7129041 baseEnd_7129041 := by
    simpa [prefixWord, tailWord_7129041, baseEnd_7129041] using wordTrace_append hprefix tailTrace_7129041
  have hstable : (prefixWord ++ tailWord_7129041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129041).length < 2 ^ (prefixWord ++ tailWord_7129041).sum := by decide
  have hdescent : baseEnd_7129041 < baseStart_7129041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129048 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_7129048 : Nat := 118140960795 + 7129048 * 2 ^ 59
def prefixEnd_7129048 : Nat := 4983230072969 + 3 ^ 40 * 7129048 * 2
def baseEnd_7129048 : Nat := 3660628232974128800614111

theorem tailTrace_7129048 : CollatzResearch.WordTrace tailWord_7129048 prefixEnd_7129048 3660628232974128800614111 := by
  unfold tailWord_7129048
  simp only [CollatzResearch.WordTrace]
  refine ⟨130008870938342057654921899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173345161251122743539895865 130008870938342057654921899)
  ·
    refine ⟨195013306407513086482382849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130008870938342057654921899 195013306407513086482382849)
    ·
      refine ⟨146259979805634814861787137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195013306407513086482382849 146259979805634814861787137)
      ·
        refine ⟨109694984854226111146340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146259979805634814861787137 109694984854226111146340353)
        ·
          refine ⟨82271238640669583359755265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109694984854226111146340353 82271238640669583359755265)
          ·
            refine ⟨61703428980502187519816449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82271238640669583359755265 61703428980502187519816449)
            ·
              refine ⟨46277571735376640639862337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61703428980502187519816449 46277571735376640639862337)
              ·
                refine ⟨34708178801532480479896753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46277571735376640639862337 34708178801532480479896753)
                ·
                  refine ⟨26031134101149360359922565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34708178801532480479896753 26031134101149360359922565)
                  ·
                    refine ⟨4880837643965505067485481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26031134101149360359922565 4880837643965505067485481)
                    ·
                      refine ⟨3660628232974128800614111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880837643965505067485481 3660628232974128800614111)
                      ·
                        rfl

theorem cell23_7129048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_7129048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129048 prefixEnd_7129048 := by exact prefixLift 7129048
  have htrace : WordTrace (prefixWord ++ tailWord_7129048) baseStart_7129048 baseEnd_7129048 := by
    simpa [prefixWord, tailWord_7129048, baseEnd_7129048] using wordTrace_append hprefix tailTrace_7129048
  have hstable : (prefixWord ++ tailWord_7129048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129048).length < 2 ^ (prefixWord ++ tailWord_7129048).sum := by decide
  have hdescent : baseEnd_7129048 < baseStart_7129048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129071 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 6]
def baseStart_7129071 : Nat := 118140960795 + 7129071 * 2 ^ 59
def prefixEnd_7129071 : Nat := 4983230072969 + 3 ^ 40 * 7129071 * 2
def baseEnd_7129071 : Nat := 406737782558798023402945

theorem tailTrace_7129071 : CollatzResearch.WordTrace tailWord_7129071 prefixEnd_7129071 406737782558798023402945 := by
  unfold tailWord_7129071
  simp only [CollatzResearch.WordTrace]
  refine ⟨260018580755600790237931067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173345720503733860158620711 260018580755600790237931067)
  ·
    refine ⟨390027871133401185356896601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260018580755600790237931067 390027871133401185356896601)
    ·
      refine ⟨292520903350050889017672451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390027871133401185356896601 292520903350050889017672451)
      ·
        refine ⟨438781355025076333526508677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292520903350050889017672451 438781355025076333526508677)
        ·
          refine ⟨82271504067201812536220377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438781355025076333526508677 82271504067201812536220377)
          ·
            refine ⟨61703628050401359402165283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82271504067201812536220377 61703628050401359402165283)
            ·
              refine ⟨92555442075602039103247925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61703628050401359402165283 92555442075602039103247925)
              ·
                refine ⟨8677072694587691165929493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92555442075602039103247925 8677072694587691165929493)
                ·
                  refine ⟨406737782558798023402945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8677072694587691165929493 406737782558798023402945)
                  ·
                    rfl

theorem cell23_7129071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 6].length) (baseStart_7129071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129071 prefixEnd_7129071 := by exact prefixLift 7129071
  have htrace : WordTrace (prefixWord ++ tailWord_7129071) baseStart_7129071 baseEnd_7129071 := by
    simpa [prefixWord, tailWord_7129071, baseEnd_7129071] using wordTrace_append hprefix tailTrace_7129071
  have hstable : (prefixWord ++ tailWord_7129071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129071).length < 2 ^ (prefixWord ++ tailWord_7129071).sum := by decide
  have hdescent : baseEnd_7129071 < baseStart_7129071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129131 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 6]
def baseStart_7129131 : Nat := 118140960795 + 7129131 * 2 ^ 59
def prefixEnd_7129131 : Nat := 4983230072969 + 3 ^ 40 * 7129131 * 2
def baseEnd_7129131 : Nat := 1220223617289483991958743

theorem tailTrace_7129131 : CollatzResearch.WordTrace tailWord_7129131 prefixEnd_7129131 1220223617289483991958743 := by
  unfold tailWord_7129131
  simp only [CollatzResearch.WordTrace]
  refine ⟨260020769135383420485115247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173347179423588946990076831 260020769135383420485115247)
  ·
    refine ⟨390031153703075130727672871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260020769135383420485115247 390031153703075130727672871)
    ·
      refine ⟨585046730554612696091509307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390031153703075130727672871 585046730554612696091509307)
      ·
        refine ⟨877570095831919044137263961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585046730554612696091509307 877570095831919044137263961)
        ·
          refine ⟨658177571873939283102947971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877570095831919044137263961 658177571873939283102947971)
          ·
            refine ⟨987266357810908924654421957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658177571873939283102947971 987266357810908924654421957)
            ·
              refine ⟨185112442089545423372704117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 987266357810908924654421957 185112442089545423372704117)
              ·
                refine ⟨17354291445894883441191011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185112442089545423372704117 17354291445894883441191011)
                ·
                  refine ⟨26031437168842325161786517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17354291445894883441191011 26031437168842325161786517)
                  ·
                    refine ⟨1220223617289483991958743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26031437168842325161786517 1220223617289483991958743)
                    ·
                      rfl

theorem cell23_7129131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_7129131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129131 prefixEnd_7129131 := by exact prefixLift 7129131
  have htrace : WordTrace (prefixWord ++ tailWord_7129131) baseStart_7129131 baseEnd_7129131 := by
    simpa [prefixWord, tailWord_7129131, baseEnd_7129131] using wordTrace_append hprefix tailTrace_7129131
  have hstable : (prefixWord ++ tailWord_7129131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129131).length < 2 ^ (prefixWord ++ tailWord_7129131).sum := by decide
  have hdescent : baseEnd_7129131 < baseStart_7129131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129142 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7129142 : Nat := 118140960795 + 7129142 * 2 ^ 59
def prefixEnd_7129142 : Nat := 4983230072969 + 3 ^ 40 * 7129142 * 2
def baseEnd_7129142 : Nat := 3660676500155651432838679

theorem tailTrace_7129142 : CollatzResearch.WordTrace tailWord_7129142 prefixEnd_7129142 3660676500155651432838679 := by
  unfold tailWord_7129142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251323146146473085235355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173347446892229046242510453 16251323146146473085235355)
  ·
    refine ⟨24376984719219709627853033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16251323146146473085235355 24376984719219709627853033)
    ·
      refine ⟨18282738539414782220889775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24376984719219709627853033 18282738539414782220889775)
      ·
        refine ⟨27424107809122173331334663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18282738539414782220889775 27424107809122173331334663)
        ·
          refine ⟨41136161713683259997001995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27424107809122173331334663 41136161713683259997001995)
          ·
            refine ⟨61704242570524889995502993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41136161713683259997001995 61704242570524889995502993)
            ·
              refine ⟨46278181927893667496627245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61704242570524889995502993 46278181927893667496627245)
              ·
                refine ⟨17354318222960125311235217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46278181927893667496627245 17354318222960125311235217)
                ·
                  refine ⟨13015738667220093983426413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17354318222960125311235217 13015738667220093983426413)
                  ·
                    refine ⟨4880902000207535243784905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13015738667220093983426413 4880902000207535243784905)
                    ·
                      refine ⟨3660676500155651432838679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4880902000207535243784905 3660676500155651432838679)
                      ·
                        rfl

theorem cell23_7129142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7129142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129142 prefixEnd_7129142 := by exact prefixLift 7129142
  have htrace : WordTrace (prefixWord ++ tailWord_7129142) baseStart_7129142 baseEnd_7129142 := by
    simpa [prefixWord, tailWord_7129142, baseEnd_7129142] using wordTrace_append hprefix tailTrace_7129142
  have hstable : (prefixWord ++ tailWord_7129142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129142).length < 2 ^ (prefixWord ++ tailWord_7129142).sum := by decide
  have hdescent : baseEnd_7129142 < baseStart_7129142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129148 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_7129148 : Nat := 118140960795 + 7129148 * 2 ^ 59
def prefixEnd_7129148 : Nat := 4983230072969 + 3 ^ 40 * 7129148 * 2
def baseEnd_7129148 : Nat := 1220226527013192803121217

theorem tailTrace_7129148 : CollatzResearch.WordTrace tailWord_7129148 prefixEnd_7129148 1220226527013192803121217 := by
  unfold tailWord_7129148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130010694588160916194242049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173347592784214554925656065 130010694588160916194242049)
  ·
    refine ⟨97508020941120687145681537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130010694588160916194242049 97508020941120687145681537)
    ·
      refine ⟨73131015705840515359261153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97508020941120687145681537 73131015705840515359261153)
      ·
        refine ⟨54848261779380386519445865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73131015705840515359261153 54848261779380386519445865)
        ·
          refine ⟨41136196334535289889584399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54848261779380386519445865 41136196334535289889584399)
          ·
            refine ⟨61704294501802934834376599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41136196334535289889584399 61704294501802934834376599)
            ·
              refine ⟨92556441752704402251564899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61704294501802934834376599 92556441752704402251564899)
              ·
                refine ⟨138834662629056603377347349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92556441752704402251564899 138834662629056603377347349)
                ·
                  refine ⟨6507874810737028283313157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138834662629056603377347349 6507874810737028283313157)
                  ·
                    refine ⟨1220226527013192803121217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507874810737028283313157 1220226527013192803121217)
                    ·
                      rfl

theorem cell23_7129148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_7129148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129148 prefixEnd_7129148 := by exact prefixLift 7129148
  have htrace : WordTrace (prefixWord ++ tailWord_7129148) baseStart_7129148 baseEnd_7129148 := by
    simpa [prefixWord, tailWord_7129148, baseEnd_7129148] using wordTrace_append hprefix tailTrace_7129148
  have hstable : (prefixWord ++ tailWord_7129148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129148).length < 2 ^ (prefixWord ++ tailWord_7129148).sum := by decide
  have hdescent : baseEnd_7129148 < baseStart_7129148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129165 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7129165 : Nat := 118140960795 + 7129165 * 2 ^ 59
def prefixEnd_7129165 : Nat := 4983230072969 + 3 ^ 40 * 7129165 * 2
def baseEnd_7129165 : Nat := 1220229436736901614283691

theorem tailTrace_7129165 : CollatzResearch.WordTrace tailWord_7129165 prefixEnd_7129165 1220229436736901614283691 := by
  unfold tailWord_7129165
  simp only [CollatzResearch.WordTrace]
  refine ⟨260022009217260244291852949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173348006144840162861235299 260022009217260244291852949)
  ·
    refine ⟨12188531682059073951180607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260022009217260244291852949 12188531682059073951180607)
    ·
      refine ⟨18282797523088610926770911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188531682059073951180607 18282797523088610926770911)
      ·
        refine ⟨27424196284632916390156367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18282797523088610926770911 27424196284632916390156367)
        ·
          refine ⟨41136294426949374585234551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27424196284632916390156367 41136294426949374585234551)
          ·
            refine ⟨61704441640424061877851827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41136294426949374585234551 61704441640424061877851827)
            ·
              refine ⟨92556662460636092816777741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61704441640424061877851827 92556662460636092816777741)
              ·
                refine ⟨34708748422738534806291653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92556662460636092816777741 34708748422738534806291653)
                ·
                  refine ⟨6507890329263475276179685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34708748422738534806291653 6507890329263475276179685)
                  ·
                    refine ⟨1220229436736901614283691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6507890329263475276179685 1220229436736901614283691)
                    ·
                      rfl

theorem cell23_7129165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7129165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129165 prefixEnd_7129165 := by exact prefixLift 7129165
  have htrace : WordTrace (prefixWord ++ tailWord_7129165) baseStart_7129165 baseEnd_7129165 := by
    simpa [prefixWord, tailWord_7129165, baseEnd_7129165] using wordTrace_append hprefix tailTrace_7129165
  have hstable : (prefixWord ++ tailWord_7129165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129165).length < 2 ^ (prefixWord ++ tailWord_7129165).sum := by decide
  have hdescent : baseEnd_7129165 < baseStart_7129165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129285 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 5]
def baseStart_7129285 : Nat := 118140960795 + 7129285 * 2 ^ 59
def prefixEnd_7129285 : Nat := 4983230072969 + 3 ^ 40 * 7129285 * 2
def baseEnd_7129285 : Nat := 406749991987693819261169

theorem tailTrace_7129285 : CollatzResearch.WordTrace tailWord_7129285 prefixEnd_7129285 406749991987693819261169 := by
  unfold tailWord_7129285
  simp only [CollatzResearch.WordTrace]
  refine ⟨260026385976825504786221309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173350923984550336524147539 260026385976825504786221309)
  ·
    refine ⟨97509894741309564294832991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260026385976825504786221309 97509894741309564294832991)
    ·
      refine ⟨146264842111964346442249487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97509894741309564294832991 146264842111964346442249487)
      ·
        refine ⟨219397263167946519663374231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146264842111964346442249487 219397263167946519663374231)
        ·
          refine ⟨329095894751919779495061347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219397263167946519663374231 329095894751919779495061347)
          ·
            refine ⟨493643842127879669242592021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329095894751919779495061347 493643842127879669242592021)
            ·
              refine ⟨23139555099744359495746501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 493643842127879669242592021 23139555099744359495746501)
              ·
                refine ⟨4338666581202067405452469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23139555099744359495746501 4338666581202067405452469)
                ·
                  refine ⟨406749991987693819261169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338666581202067405452469 406749991987693819261169)
                  ·
                    rfl

theorem cell23_7129285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_7129285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129285 prefixEnd_7129285 := by exact prefixLift 7129285
  have htrace : WordTrace (prefixWord ++ tailWord_7129285) baseStart_7129285 baseEnd_7129285 := by
    simpa [prefixWord, tailWord_7129285, baseEnd_7129285] using wordTrace_append hprefix tailTrace_7129285
  have hstable : (prefixWord ++ tailWord_7129285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129285).length < 2 ^ (prefixWord ++ tailWord_7129285).sum := by decide
  have hdescent : baseEnd_7129285 < baseStart_7129285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129302 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_7129302 : Nat := 118140960795 + 7129302 * 2 ^ 59
def prefixEnd_7129302 : Nat := 4983230072969 + 3 ^ 40 * 7129302 * 2
def baseEnd_7129302 : Nat := 406750961895596756315327

theorem tailTrace_7129302 : CollatzResearch.WordTrace tailWord_7129302 prefixEnd_7129302 406750961895596756315327 := by
  unfold tailWord_7129302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251687876110244793099385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173351337345175944459726773 16251687876110244793099385)
  ·
    refine ⟨12188765907082683594824539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16251687876110244793099385 12188765907082683594824539)
    ·
      refine ⟨18283148860624025392236809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188765907082683594824539 18283148860624025392236809)
      ·
        refine ⟨13712361645468019044177607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18283148860624025392236809 13712361645468019044177607)
        ·
          refine ⟨20568542468202028566266411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712361645468019044177607 20568542468202028566266411)
          ·
            refine ⟨30852813702303042849399617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20568542468202028566266411 30852813702303042849399617)
            ·
              refine ⟨23139610276727282137049713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30852813702303042849399617 23139610276727282137049713)
              ·
                refine ⟨17354707707545461602787285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23139610276727282137049713 17354707707545461602787285)
                ·
                  refine ⟨406750961895596756315327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17354707707545461602787285 406750961895596756315327)
                  ·
                    rfl

theorem cell23_7129302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_7129302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129302 prefixEnd_7129302 := by exact prefixLift 7129302
  have htrace : WordTrace (prefixWord ++ tailWord_7129302) baseStart_7129302 baseEnd_7129302 := by
    simpa [prefixWord, tailWord_7129302, baseEnd_7129302] using wordTrace_append hprefix tailTrace_7129302
  have hstable : (prefixWord ++ tailWord_7129302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129302).length < 2 ^ (prefixWord ++ tailWord_7129302).sum := by decide
  have hdescent : baseEnd_7129302 < baseStart_7129302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129305 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 5, 2]
def baseStart_7129305 : Nat := 118140960795 + 7129305 * 2 ^ 59
def prefixEnd_7129305 : Nat := 4983230072969 + 3 ^ 40 * 7129305 * 2
def baseEnd_7129305 : Nat := 3660760197502334295100429

theorem tailTrace_7129305 : CollatzResearch.WordTrace tailWord_7129305 prefixEnd_7129305 3660760197502334295100429 := by
  unfold tailWord_7129305
  simp only [CollatzResearch.WordTrace]
  refine ⟨260027115436753048201949369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173351410291168698801299579 260027115436753048201949369)
  ·
    refine ⟨195020336577564786151462027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260027115436753048201949369 195020336577564786151462027)
    ·
      refine ⟨292530504866347179227193041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195020336577564786151462027 292530504866347179227193041)
      ·
        refine ⟨219397878649760384420394781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292530504866347179227193041 219397878649760384420394781)
        ·
          refine ⟨82274204493660144157648043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219397878649760384420394781 82274204493660144157648043)
          ·
            refine ⟨123411306740490216236472065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82274204493660144157648043 123411306740490216236472065)
            ·
              refine ⟨92558480055367662177354049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123411306740490216236472065 92558480055367662177354049)
              ·
                refine ⟨69418860041525746633015537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92558480055367662177354049 69418860041525746633015537)
                ·
                  refine ⟨52064145031144309974761653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69418860041525746633015537 52064145031144309974761653)
                  ·
                    refine ⟨4881013596669779060133905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52064145031144309974761653 4881013596669779060133905)
                    ·
                      refine ⟨3660760197502334295100429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881013596669779060133905 3660760197502334295100429)
                      ·
                        rfl

theorem cell23_7129305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_7129305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129305 prefixEnd_7129305 := by exact prefixLift 7129305
  have htrace : WordTrace (prefixWord ++ tailWord_7129305) baseStart_7129305 baseEnd_7129305 := by
    simpa [prefixWord, tailWord_7129305, baseEnd_7129305] using wordTrace_append hprefix tailTrace_7129305
  have hstable : (prefixWord ++ tailWord_7129305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129305).length < 2 ^ (prefixWord ++ tailWord_7129305).sum := by decide
  have hdescent : baseEnd_7129305 < baseStart_7129305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129319 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 5]
def baseStart_7129319 : Nat := 118140960795 + 7129319 * 2 ^ 59
def prefixEnd_7129319 : Nat := 4983230072969 + 3 ^ 40 * 7129319 * 2
def baseEnd_7129319 : Nat := 406751931803499693369485

theorem tailTrace_7129319 : CollatzResearch.WordTrace tailWord_7129319 prefixEnd_7129319 406751931803499693369485 := by
  unfold tailWord_7129319
  simp only [CollatzResearch.WordTrace]
  refine ⟨260027626058702328592959011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173351750705801552395306007 260027626058702328592959011)
  ·
    refine ⟨390041439088053492889438517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260027626058702328592959011 390041439088053492889438517)
    ·
      refine ⟨36566384914505014958384861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 390041439088053492889438517 36566384914505014958384861)
      ·
        refine ⟨13712394342939380609394323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36566384914505014958384861 13712394342939380609394323)
        ·
          refine ⟨20568591514409070914091485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13712394342939380609394323 20568591514409070914091485)
          ·
            refine ⟨7713221817903401592784307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20568591514409070914091485 7713221817903401592784307)
            ·
              refine ⟨11569832726855102389176461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713221817903401592784307 11569832726855102389176461)
              ·
                refine ⟨4338687272570663395941173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11569832726855102389176461 4338687272570663395941173)
                ·
                  refine ⟨406751931803499693369485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4338687272570663395941173 406751931803499693369485)
                  ·
                    rfl

theorem cell23_7129319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 5].length) (baseStart_7129319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129319 prefixEnd_7129319 := by exact prefixLift 7129319
  have htrace : WordTrace (prefixWord ++ tailWord_7129319) baseStart_7129319 baseEnd_7129319 := by
    simpa [prefixWord, tailWord_7129319, baseEnd_7129319] using wordTrace_append hprefix tailTrace_7129319
  have hstable : (prefixWord ++ tailWord_7129319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129319).length < 2 ^ (prefixWord ++ tailWord_7129319).sum := by decide
  have hdescent : baseEnd_7129319 < baseStart_7129319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129355 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3]
def baseStart_7129355 : Nat := 118140960795 + 7129355 * 2 ^ 59
def prefixEnd_7129355 : Nat := 4983230072969 + 3 ^ 40 * 7129355 * 2
def baseEnd_7129355 : Nat := 3660785871535059099475199

theorem tailTrace_7129355 : CollatzResearch.WordTrace tailWord_7129355 prefixEnd_7129355 3660785871535059099475199 := by
  unfold tailWord_7129355
  simp only [CollatzResearch.WordTrace]
  refine ⟨260028939086571906741269519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173352626057714604494179679 260028939086571906741269519)
  ·
    refine ⟨390043408629857860111904279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260028939086571906741269519 390043408629857860111904279)
    ·
      refine ⟨585065112944786790167856419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390043408629857860111904279 585065112944786790167856419)
      ·
        refine ⟨877597669417180185251784629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585065112944786790167856419 877597669417180185251784629)
        ·
          refine ⟨82274781507860642367354809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 877597669417180185251784629 82274781507860642367354809)
          ·
            refine ⟨61706086130895481775516107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82274781507860642367354809 61706086130895481775516107)
            ·
              refine ⟨92559129196343222663274161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61706086130895481775516107 92559129196343222663274161)
              ·
                refine ⟨69419346897257416997455621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92559129196343222663274161 69419346897257416997455621)
                ·
                  refine ⟨13016127543235765687022929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69419346897257416997455621 13016127543235765687022929)
                  ·
                    refine ⟨9762095657426824265267197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13016127543235765687022929 9762095657426824265267197)
                    ·
                      refine ⟨3660785871535059099475199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9762095657426824265267197 3660785871535059099475199)
                      ·
                        rfl

theorem cell23_7129355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].length) (baseStart_7129355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129355 prefixEnd_7129355 := by exact prefixLift 7129355
  have htrace : WordTrace (prefixWord ++ tailWord_7129355) baseStart_7129355 baseEnd_7129355 := by
    simpa [prefixWord, tailWord_7129355, baseEnd_7129355] using wordTrace_append hprefix tailTrace_7129355
  have hstable : (prefixWord ++ tailWord_7129355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129355).length < 2 ^ (prefixWord ++ tailWord_7129355).sum := by decide
  have hdescent : baseEnd_7129355 < baseStart_7129355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129396 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_7129396 : Nat := 118140960795 + 7129396 * 2 ^ 59
def prefixEnd_7129396 : Nat := 4983230072969 + 3 ^ 40 * 7129396 * 2
def baseEnd_7129396 : Nat := 1220268974747297813020837

theorem tailTrace_7129396 : CollatzResearch.WordTrace tailWord_7129396 prefixEnd_7129396 1220268974747297813020837 := by
  unfold tailWord_7129396
  simp only [CollatzResearch.WordTrace]
  refine ⟨130015217239711685371756021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173353622986282247162341361 130015217239711685371756021)
  ·
    refine ⟨12188926616222970503602127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130015217239711685371756021 12188926616222970503602127)
    ·
      refine ⟨18283389924334455755403191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12188926616222970503602127 18283389924334455755403191)
      ·
        refine ⟨27425084886501683633104787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283389924334455755403191 27425084886501683633104787)
        ·
          refine ⟨41137627329752525449657181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27425084886501683633104787 41137627329752525449657181)
          ·
            refine ⟨15426610248657197043621443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41137627329752525449657181 15426610248657197043621443)
            ·
              refine ⟨23139915372985795565432165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426610248657197043621443 23139915372985795565432165)
              ·
                refine ⟨4338734132434836668518531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23139915372985795565432165 4338734132434836668518531)
                ·
                  refine ⟨6508101198652255002777797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4338734132434836668518531 6508101198652255002777797)
                  ·
                    refine ⟨1220268974747297813020837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508101198652255002777797 1220268974747297813020837)
                    ·
                      rfl

theorem cell23_7129396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_7129396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129396 prefixEnd_7129396 := by exact prefixLift 7129396
  have htrace : WordTrace (prefixWord ++ tailWord_7129396) baseStart_7129396 baseEnd_7129396 := by
    simpa [prefixWord, tailWord_7129396, baseEnd_7129396] using wordTrace_append hprefix tailTrace_7129396
  have hstable : (prefixWord ++ tailWord_7129396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129396).length < 2 ^ (prefixWord ++ tailWord_7129396).sum := by decide
  have hdescent : baseEnd_7129396 < baseStart_7129396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129429 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7129429 : Nat := 118140960795 + 7129429 * 2 ^ 59
def prefixEnd_7129429 : Nat := 4983230072969 + 3 ^ 40 * 7129429 * 2
def baseEnd_7129429 : Nat := 3660823869103491809949859

theorem tailTrace_7129429 : CollatzResearch.WordTrace tailWord_7129429 prefixEnd_7129429 3660823869103491809949859 := by
  unfold tailWord_7129429
  simp only [CollatzResearch.WordTrace]
  refine ⟨260031638088303817379463341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173354425392202544919642227 260031638088303817379463341)
  ·
    refine ⟨97511864283113931517298753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260031638088303817379463341 97511864283113931517298753)
    ·
      refine ⟨73133898212335448637974065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97511864283113931517298753 73133898212335448637974065)
      ·
        refine ⟨54850423659251586478480549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73133898212335448637974065 54850423659251586478480549)
        ·
          refine ⟨10284454436109672464715103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54850423659251586478480549 10284454436109672464715103)
          ·
            refine ⟨15426681654164508697072655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284454436109672464715103 15426681654164508697072655)
            ·
              refine ⟨23140022481246763045608983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426681654164508697072655 23140022481246763045608983)
              ·
                refine ⟨34710033721870144568413475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23140022481246763045608983 34710033721870144568413475)
                ·
                  refine ⟨52065050582805216852620213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34710033721870144568413475 52065050582805216852620213)
                  ·
                    refine ⟨4881098492137989079933145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52065050582805216852620213 4881098492137989079933145)
                    ·
                      refine ⟨3660823869103491809949859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881098492137989079933145 3660823869103491809949859)
                      ·
                        rfl

theorem cell23_7129429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7129429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129429 prefixEnd_7129429 := by exact prefixLift 7129429
  have htrace : WordTrace (prefixWord ++ tailWord_7129429) baseStart_7129429 baseEnd_7129429 := by
    simpa [prefixWord, tailWord_7129429, baseEnd_7129429] using wordTrace_append hprefix tailTrace_7129429
  have hstable : (prefixWord ++ tailWord_7129429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129429).length < 2 ^ (prefixWord ++ tailWord_7129429).sum := by decide
  have hdescent : baseEnd_7129429 < baseStart_7129429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129479 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_7129479 : Nat := 118140960795 + 7129479 * 2 ^ 59
def prefixEnd_7129479 : Nat := 4983230072969 + 3 ^ 40 * 7129479 * 2
def baseEnd_7129479 : Nat := 3660849543136216614324629

theorem tailTrace_7129479 : CollatzResearch.WordTrace tailWord_7129479 prefixEnd_7129479 3660849543136216614324629 := by
  unfold tailWord_7129479
  simp only [CollatzResearch.WordTrace]
  refine ⟨260033461738122675918783491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173355641158748450612522327 260033461738122675918783491)
  ·
    refine ⟨390050192607184013878175237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260033461738122675918783491 390050192607184013878175237)
    ·
      refine ⟨73134411113847002602157857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390050192607184013878175237 73134411113847002602157857)
      ·
        refine ⟨54850808335385251951618393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73134411113847002602157857 54850808335385251951618393)
        ·
          refine ⟨41138106251538938963713795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54850808335385251951618393 41138106251538938963713795)
          ·
            refine ⟨61707159377308408445570693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41138106251538938963713795 61707159377308408445570693)
            ·
              refine ⟨11570092383245326583544505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61707159377308408445570693 11570092383245326583544505)
              ·
                refine ⟨8677569287433994937658379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11570092383245326583544505 8677569287433994937658379)
                ·
                  refine ⟨13016353931150992406487569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677569287433994937658379 13016353931150992406487569)
                  ·
                    refine ⟨9762265448363244304865677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13016353931150992406487569 9762265448363244304865677)
                    ·
                      refine ⟨3660849543136216614324629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9762265448363244304865677 3660849543136216614324629)
                      ·
                        rfl

theorem cell23_7129479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_7129479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129479 prefixEnd_7129479 := by exact prefixLift 7129479
  have htrace : WordTrace (prefixWord ++ tailWord_7129479) baseStart_7129479 baseEnd_7129479 := by
    simpa [prefixWord, tailWord_7129479, baseEnd_7129479] using wordTrace_append hprefix tailTrace_7129479
  have hstable : (prefixWord ++ tailWord_7129479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129479).length < 2 ^ (prefixWord ++ tailWord_7129479).sum := by decide
  have hdescent : baseEnd_7129479 < baseStart_7129479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129509 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_7129509 : Nat := 118140960795 + 7129509 * 2 ^ 59
def prefixEnd_7129509 : Nat := 4983230072969 + 3 ^ 40 * 7129509 * 2
def baseEnd_7129509 : Nat := 3660864947555851496949491

theorem tailTrace_7129509 : CollatzResearch.WordTrace tailWord_7129509 prefixEnd_7129509 3660864947555851496949491 := by
  unfold tailWord_7129509
  simp only [CollatzResearch.WordTrace]
  refine ⟨260034555928013991042375581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173356370618675994028250387 260034555928013991042375581)
  ·
    refine ⟨97512958473005246640890843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260034555928013991042375581 97512958473005246640890843)
    ·
      refine ⟨146269437709507869961336265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97512958473005246640890843 146269437709507869961336265)
      ·
        refine ⟨109702078282130902471002199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146269437709507869961336265 109702078282130902471002199)
        ·
          refine ⟨164553117423196353706503299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109702078282130902471002199 164553117423196353706503299)
          ·
            refine ⟨246829676134794530559754949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164553117423196353706503299 246829676134794530559754949)
            ·
              refine ⟨46280564275273974479954053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246829676134794530559754949 46280564275273974479954053)
              ·
                refine ⟨8677605801613870214991385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46280564275273974479954053 8677605801613870214991385)
                ·
                  refine ⟨6508204351210402661243539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8677605801613870214991385 6508204351210402661243539)
                  ·
                    refine ⟨9762306526815603991865309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6508204351210402661243539 9762306526815603991865309)
                    ·
                      refine ⟨3660864947555851496949491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9762306526815603991865309 3660864947555851496949491)
                      ·
                        rfl

theorem cell23_7129509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_7129509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129509 prefixEnd_7129509 := by exact prefixLift 7129509
  have htrace : WordTrace (prefixWord ++ tailWord_7129509) baseStart_7129509 baseEnd_7129509 := by
    simpa [prefixWord, tailWord_7129509, baseEnd_7129509] using wordTrace_append hprefix tailTrace_7129509
  have hstable : (prefixWord ++ tailWord_7129509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129509).length < 2 ^ (prefixWord ++ tailWord_7129509).sum := by decide
  have hdescent : baseEnd_7129509 < baseStart_7129509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129562 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_7129562 : Nat := 118140960795 + 7129562 * 2 ^ 59
def prefixEnd_7129562 : Nat := 4983230072969 + 3 ^ 40 * 7129562 * 2
def baseEnd_7129562 : Nat := 3660892162030539789586747

theorem tailTrace_7129562 : CollatzResearch.WordTrace tailWord_7129562 prefixEnd_7129562 3660892162030539789586747 := by
  unfold tailWord_7129562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65009122249205495273513735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173357659331214654062703293 65009122249205495273513735)
  ·
    refine ⟨97513683373808242910270603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65009122249205495273513735 97513683373808242910270603)
    ·
      refine ⟨146270525060712364365405905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97513683373808242910270603 146270525060712364365405905)
      ·
        refine ⟨109702893795534273274054429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146270525060712364365405905 109702893795534273274054429)
        ·
          refine ⟨41138585173325352477770411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109702893795534273274054429 41138585173325352477770411)
          ·
            refine ⟨61707877759988028716655617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41138585173325352477770411 61707877759988028716655617)
            ·
              refine ⟨46280908319991021537491713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61707877759988028716655617 46280908319991021537491713)
              ·
                refine ⟨34710681239993266153118785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46280908319991021537491713 34710681239993266153118785)
                ·
                  refine ⟨26033010929994949614839089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34710681239993266153118785 26033010929994949614839089)
                  ·
                    refine ⟨19524758197496212211129317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26033010929994949614839089 19524758197496212211129317)
                    ·
                      refine ⟨3660892162030539789586747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19524758197496212211129317 3660892162030539789586747)
                      ·
                        rfl

theorem cell23_7129562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_7129562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129562 prefixEnd_7129562 := by exact prefixLift 7129562
  have htrace : WordTrace (prefixWord ++ tailWord_7129562) baseStart_7129562 baseEnd_7129562 := by
    simpa [prefixWord, tailWord_7129562, baseEnd_7129562] using wordTrace_append hprefix tailTrace_7129562
  have hstable : (prefixWord ++ tailWord_7129562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129562).length < 2 ^ (prefixWord ++ tailWord_7129562).sum := by decide
  have hdescent : baseEnd_7129562 < baseStart_7129562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129649 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_7129649 : Nat := 118140960795 + 7129649 * 2 ^ 59
def prefixEnd_7129649 : Nat := 4983230072969 + 3 ^ 40 * 7129649 * 2
def baseEnd_7129649 : Nat := 1220312278282493649732949

theorem tailTrace_7129649 : CollatzResearch.WordTrace tailWord_7129649 prefixEnd_7129649 1220312278282493649732949 := by
  unfold tailWord_7129649
  simp only [CollatzResearch.WordTrace]
  refine ⟨260039662147506794952472001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173359774765004529968314667 260039662147506794952472001)
  ·
    refine ⟨195029746610630096214354001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260039662147506794952472001 195029746610630096214354001)
    ·
      refine ⟨146272309957972572160765501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195029746610630096214354001 146272309957972572160765501)
      ·
        refine ⟨54852116234239714560287063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146272309957972572160765501 54852116234239714560287063)
        ·
          refine ⟨82278174351359571840430595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54852116234239714560287063 82278174351359571840430595)
          ·
            refine ⟨123417261527039357760645893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82278174351359571840430595 123417261527039357760645893)
            ·
              refine ⟨23140736536319879580121105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123417261527039357760645893 23140736536319879580121105)
              ·
                refine ⟨17355552402239909685090829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23140736536319879580121105 17355552402239909685090829)
                ·
                  refine ⟨6508332150839966131909061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17355552402239909685090829 6508332150839966131909061)
                  ·
                    refine ⟨1220312278282493649732949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508332150839966131909061 1220312278282493649732949)
                    ·
                      rfl

theorem cell23_7129649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_7129649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129649 prefixEnd_7129649 := by exact prefixLift 7129649
  have htrace : WordTrace (prefixWord ++ tailWord_7129649) baseStart_7129649 baseEnd_7129649 := by
    simpa [prefixWord, tailWord_7129649, baseEnd_7129649] using wordTrace_append hprefix tailTrace_7129649
  have hstable : (prefixWord ++ tailWord_7129649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129649).length < 2 ^ (prefixWord ++ tailWord_7129649).sum := by decide
  have hdescent : baseEnd_7129649 < baseStart_7129649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129706 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7129706 : Nat := 118140960795 + 7129706 * 2 ^ 59
def prefixEnd_7129706 : Nat := 4983230072969 + 3 ^ 40 * 7129706 * 2
def baseEnd_7129706 : Nat := 3660966103244787226186085

theorem tailTrace_7129706 : CollatzResearch.WordTrace tailWord_7129706 prefixEnd_7129706 3660966103244787226186085 := by
  unfold tailWord_7129706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010435277075073421824243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173361160738866862458197981 65010435277075073421824243)
  ·
    refine ⟨97515652915612610132736365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65010435277075073421824243 97515652915612610132736365)
    ·
      refine ⟨36568369843354728799776137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97515652915612610132736365 36568369843354728799776137)
      ·
        refine ⟨27426277382516046599832103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36568369843354728799776137 27426277382516046599832103)
        ·
          refine ⟨41139416073774069899748155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27426277382516046599832103 41139416073774069899748155)
          ·
            refine ⟨61709124110661104849622233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41139416073774069899748155 61709124110661104849622233)
            ·
              refine ⟨46281843082995828637216675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61709124110661104849622233 46281843082995828637216675)
              ·
                refine ⟨69422764624493742955825013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46281843082995828637216675 69422764624493742955825013)
                ·
                  refine ⟨6508384183546288402108595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69422764624493742955825013 6508384183546288402108595)
                  ·
                    refine ⟨9762576275319432603162893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6508384183546288402108595 9762576275319432603162893)
                    ·
                      refine ⟨3660966103244787226186085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9762576275319432603162893 3660966103244787226186085)
                      ·
                        rfl

theorem cell23_7129706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7129706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129706 prefixEnd_7129706 := by exact prefixLift 7129706
  have htrace : WordTrace (prefixWord ++ tailWord_7129706) baseStart_7129706 baseEnd_7129706 := by
    simpa [prefixWord, tailWord_7129706, baseEnd_7129706] using wordTrace_append hprefix tailTrace_7129706
  have hstable : (prefixWord ++ tailWord_7129706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129706).length < 2 ^ (prefixWord ++ tailWord_7129706).sum := by decide
  have hdescent : baseEnd_7129706 < baseStart_7129706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129746 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7129746 : Nat := 118140960795 + 7129746 * 2 ^ 59
def prefixEnd_7129746 : Nat := 4983230072969 + 3 ^ 40 * 7129746 * 2
def baseEnd_7129746 : Nat := 3660986642470967069685901

theorem tailTrace_7129746 : CollatzResearch.WordTrace tailWord_7129746 prefixEnd_7129746 3660986642470967069685901 := by
  unfold tailWord_7129746
  simp only [CollatzResearch.WordTrace]
  refine ⟨65010800007038845129688273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173362133352103587012502061 65010800007038845129688273)
  ·
    refine ⟨48758100005279133847266205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65010800007038845129688273 48758100005279133847266205)
    ·
      refine ⟨18284287501979675192724827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48758100005279133847266205 18284287501979675192724827)
      ·
        refine ⟨27426431252969512789087241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18284287501979675192724827 27426431252969512789087241)
        ·
          refine ⟨20569823439727134591815431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27426431252969512789087241 20569823439727134591815431)
          ·
            refine ⟨30854735159590701887723147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20569823439727134591815431 30854735159590701887723147)
            ·
              refine ⟨46282102739386052831584721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30854735159590701887723147 46282102739386052831584721)
              ·
                refine ⟨34711577054539539623688541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46282102739386052831584721 34711577054539539623688541)
                ·
                  refine ⟨13016841395452327358883203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34711577054539539623688541 13016841395452327358883203)
                  ·
                    refine ⟨19525262093178491038324805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13016841395452327358883203 19525262093178491038324805)
                    ·
                      refine ⟨3660986642470967069685901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19525262093178491038324805 3660986642470967069685901)
                      ·
                        rfl

theorem cell23_7129746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7129746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129746 prefixEnd_7129746 := by exact prefixLift 7129746
  have htrace : WordTrace (prefixWord ++ tailWord_7129746) baseStart_7129746 baseEnd_7129746 := by
    simpa [prefixWord, tailWord_7129746, baseEnd_7129746] using wordTrace_append hprefix tailTrace_7129746
  have hstable : (prefixWord ++ tailWord_7129746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129746).length < 2 ^ (prefixWord ++ tailWord_7129746).sum := by decide
  have hdescent : baseEnd_7129746 < baseStart_7129746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129756 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_7129756 : Nat := 118140960795 + 7129756 * 2 ^ 59
def prefixEnd_7129756 : Nat := 4983230072969 + 3 ^ 40 * 7129756 * 2
def baseEnd_7129756 : Nat := 1220330592425837343520285

theorem tailTrace_7129756 : CollatzResearch.WordTrace tailWord_7129756 prefixEnd_7129756 1220330592425837343520285 := by
  unfold tailWord_7129756
  simp only [CollatzResearch.WordTrace]
  refine ⟨130021782379059576113308561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173362376505412768151078081 130021782379059576113308561)
  ·
    refine ⟨97516336784294682084981421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130021782379059576113308561 97516336784294682084981421)
    ·
      refine ⟨36568626294110505781868033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97516336784294682084981421 36568626294110505781868033)
      ·
        refine ⟨27426469720582879336401025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36568626294110505781868033 27426469720582879336401025)
        ·
          refine ⟨20569852290437159502300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27426469720582879336401025 20569852290437159502300769)
          ·
            refine ⟨15427389217827869626725577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20569852290437159502300769 15427389217827869626725577)
            ·
              refine ⟨11570541913370902220044183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15427389217827869626725577 11570541913370902220044183)
              ·
                refine ⟨17355812870056353330066275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570541913370902220044183 17355812870056353330066275)
                ·
                  refine ⟨26033719305084529995099413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17355812870056353330066275 26033719305084529995099413)
                  ·
                    refine ⟨1220330592425837343520285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26033719305084529995099413 1220330592425837343520285)
                    ·
                      rfl

theorem cell23_7129756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_7129756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129756 prefixEnd_7129756 := by exact prefixLift 7129756
  have htrace : WordTrace (prefixWord ++ tailWord_7129756) baseStart_7129756 baseEnd_7129756 := by
    simpa [prefixWord, tailWord_7129756, baseEnd_7129756] using wordTrace_append hprefix tailTrace_7129756
  have hstable : (prefixWord ++ tailWord_7129756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129756).length < 2 ^ (prefixWord ++ tailWord_7129756).sum := by decide
  have hdescent : baseEnd_7129756 < baseStart_7129756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129767 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7129767 : Nat := 118140960795 + 7129767 * 2 ^ 59
def prefixEnd_7129767 : Nat := 4983230072969 + 3 ^ 40 * 7129767 * 2
def baseEnd_7129767 : Nat := 3660997425564711487523305

theorem tailTrace_7129767 : CollatzResearch.WordTrace tailWord_7129767 prefixEnd_7129767 3660997425564711487523305 := by
  unfold tailWord_7129767
  simp only [CollatzResearch.WordTrace]
  refine ⟨260043965961079301105267555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173362643974052867403511703 260043965961079301105267555)
  ·
    refine ⟨390065948941618951657901333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260043965961079301105267555 390065948941618951657901333)
    ·
      refine ⟨18284341356638388358964125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390065948941618951657901333 18284341356638388358964125)
      ·
        refine ⟨6856628008739395634611547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18284341356638388358964125 6856628008739395634611547)
        ·
          refine ⟨10284942013109093451917321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856628008739395634611547 10284942013109093451917321)
          ·
            refine ⟨7713706509831820088937991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284942013109093451917321 7713706509831820088937991)
            ·
              refine ⟨11570559764747730133406987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713706509831820088937991 11570559764747730133406987)
              ·
                refine ⟨17355839647121595200110481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570559764747730133406987 17355839647121595200110481)
                ·
                  refine ⟨13016879735341196400082861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17355839647121595200110481 13016879735341196400082861)
                  ·
                    refine ⟨4881329900752948650031073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13016879735341196400082861 4881329900752948650031073)
                    ·
                      refine ⟨3660997425564711487523305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881329900752948650031073 3660997425564711487523305)
                      ·
                        rfl

theorem cell23_7129767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7129767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129767 prefixEnd_7129767 := by exact prefixLift 7129767
  have htrace : WordTrace (prefixWord ++ tailWord_7129767) baseStart_7129767 baseEnd_7129767 := by
    simpa [prefixWord, tailWord_7129767, baseEnd_7129767] using wordTrace_append hprefix tailTrace_7129767
  have hstable : (prefixWord ++ tailWord_7129767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129767).length < 2 ^ (prefixWord ++ tailWord_7129767).sum := by decide
  have hdescent : baseEnd_7129767 < baseStart_7129767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129777 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_7129777 : Nat := 118140960795 + 7129777 * 2 ^ 59
def prefixEnd_7129777 : Nat := 4983230072969 + 3 ^ 40 * 7129777 * 2
def baseEnd_7129777 : Nat := 1220334186790418816132753

theorem tailTrace_7129777 : CollatzResearch.WordTrace tailWord_7129777 prefixEnd_7129777 1220334186790418816132753 := by
  unfold tailWord_7129777
  simp only [CollatzResearch.WordTrace]
  refine ⟨260044330691043072813131585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173362887127362048542087723 260044330691043072813131585)
  ·
    refine ⟨195033248018282304609848689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260044330691043072813131585 195033248018282304609848689)
    ·
      refine ⟨146274936013711728457386517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195033248018282304609848689 146274936013711728457386517)
      ·
        refine ⟨6856637625642737271439993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146274936013711728457386517 6856637625642737271439993)
        ·
          refine ⟨5142478219232052953579995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6856637625642737271439993 5142478219232052953579995)
          ·
            refine ⟨7713717328848079430369993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142478219232052953579995 7713717328848079430369993)
            ·
              refine ⟨5785287996636059572777495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7713717328848079430369993 5785287996636059572777495)
              ·
                refine ⟨8677931994954089359166243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785287996636059572777495 8677931994954089359166243)
                ·
                  refine ⟨13016897992431134038749365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677931994954089359166243 13016897992431134038749365)
                  ·
                    refine ⟨1220334186790418816132753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13016897992431134038749365 1220334186790418816132753)
                    ·
                      rfl

theorem cell23_7129777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_7129777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129777 prefixEnd_7129777 := by exact prefixLift 7129777
  have htrace : WordTrace (prefixWord ++ tailWord_7129777) baseStart_7129777 baseEnd_7129777 := by
    simpa [prefixWord, tailWord_7129777, baseEnd_7129777] using wordTrace_append hprefix tailTrace_7129777
  have hstable : (prefixWord ++ tailWord_7129777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129777).length < 2 ^ (prefixWord ++ tailWord_7129777).sum := by decide
  have hdescent : baseEnd_7129777 < baseStart_7129777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129783 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_7129783 : Nat := 118140960795 + 7129783 * 2 ^ 59
def prefixEnd_7129783 : Nat := 4983230072969 + 3 ^ 40 * 7129783 * 2
def baseEnd_7129783 : Nat := 3661005641255183424923231

theorem tailTrace_7129783 : CollatzResearch.WordTrace tailWord_7129783 prefixEnd_7129783 3661005641255183424923231 := by
  unfold tailWord_7129783
  simp only [CollatzResearch.WordTrace]
  refine ⟨260044549529021335837850003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173363033019347557225233335 260044549529021335837850003)
  ·
    refine ⟨390066824293532003756775005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260044549529021335837850003 390066824293532003756775005)
    ·
      refine ⟨146275059110074501408790627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390066824293532003756775005 146275059110074501408790627)
      ·
        refine ⟨219412588665111752113185941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146275059110074501408790627 219412588665111752113185941)
        ·
          refine ⟨10284965093677113380305591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219412588665111752113185941 10284965093677113380305591)
          ·
            refine ⟨15427447640515670070458387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284965093677113380305591 15427447640515670070458387)
            ·
              refine ⟨23141171460773505105687581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15427447640515670070458387 23141171460773505105687581)
              ·
                refine ⟨8677939297790064414632843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23141171460773505105687581 8677939297790064414632843)
                ·
                  refine ⟨13016908946685096621949265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677939297790064414632843 13016908946685096621949265)
                  ·
                    refine ⟨9762681710013822466461949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13016908946685096621949265 9762681710013822466461949)
                    ·
                      refine ⟨3661005641255183424923231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9762681710013822466461949 3661005641255183424923231)
                      ·
                        rfl

theorem cell23_7129783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_7129783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129783 prefixEnd_7129783 := by exact prefixLift 7129783
  have htrace : WordTrace (prefixWord ++ tailWord_7129783) baseStart_7129783 baseEnd_7129783 := by
    simpa [prefixWord, tailWord_7129783, baseEnd_7129783] using wordTrace_append hprefix tailTrace_7129783
  have hstable : (prefixWord ++ tailWord_7129783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129783).length < 2 ^ (prefixWord ++ tailWord_7129783).sum := by decide
  have hdescent : baseEnd_7129783 < baseStart_7129783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129810 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7129810 : Nat := 118140960795 + 7129810 * 2 ^ 59
def prefixEnd_7129810 : Nat := 4983230072969 + 3 ^ 40 * 7129810 * 2
def baseEnd_7129810 : Nat := 3661019505232854819285607

theorem tailTrace_7129810 : CollatzResearch.WordTrace tailWord_7129810 prefixEnd_7129810 3661019505232854819285607 := by
  unfold tailWord_7129810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65011383574980879862270721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173363689533282346299388589 65011383574980879862270721)
  ·
    refine ⟨48758537681235659896703041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65011383574980879862270721 48758537681235659896703041)
    ·
      refine ⟨36568903260926744922527281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48758537681235659896703041 36568903260926744922527281)
      ·
        refine ⟨27426677445695058691895461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36568903260926744922527281 27426677445695058691895461)
        ·
          refine ⟨5142502021067823504730399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27426677445695058691895461 5142502021067823504730399)
          ·
            refine ⟨7713753031601735257095599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142502021067823504730399 7713753031601735257095599)
            ·
              refine ⟨11570629547402602885643399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713753031601735257095599 11570629547402602885643399)
              ·
                refine ⟨17355944321103904328465099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570629547402602885643399 17355944321103904328465099)
                ·
                  refine ⟨26033916481655856492697649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17355944321103904328465099 26033916481655856492697649)
                  ·
                    refine ⟨19525437361241892369523237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26033916481655856492697649 19525437361241892369523237)
                    ·
                      refine ⟨3661019505232854819285607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19525437361241892369523237 3661019505232854819285607)
                      ·
                        rfl

theorem cell23_7129810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7129810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129810 prefixEnd_7129810 := by exact prefixLift 7129810
  have htrace : WordTrace (prefixWord ++ tailWord_7129810) baseStart_7129810 baseEnd_7129810 := by
    simpa [prefixWord, tailWord_7129810, baseEnd_7129810] using wordTrace_append hprefix tailTrace_7129810
  have hstable : (prefixWord ++ tailWord_7129810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129810).length < 2 ^ (prefixWord ++ tailWord_7129810).sum := by decide
  have hdescent : baseEnd_7129810 < baseStart_7129810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129823 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 1, 3, 2]
def baseStart_7129823 : Nat := 118140960795 + 7129823 * 2 ^ 59
def prefixEnd_7129823 : Nat := 4983230072969 + 3 ^ 40 * 7129823 * 2
def baseEnd_7129823 : Nat := 3661026180481363268423047

theorem tailTrace_7129823 : CollatzResearch.WordTrace tailWord_7129823 prefixEnd_7129823 3661026180481363268423047 := by
  unfold tailWord_7129823
  simp only [CollatzResearch.WordTrace]
  refine ⟨260046008448876422669306123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173364005632584281779537415 260046008448876422669306123)
  ·
    refine ⟨390069012673314634003959185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260046008448876422669306123 390069012673314634003959185)
    ·
      refine ⟨292551759504985975502969389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390069012673314634003959185 292551759504985975502969389)
      ·
        refine ⟨109706909814369740813613521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292551759504985975502969389 109706909814369740813613521)
        ·
          refine ⟨82280182360777305610210141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109706909814369740813613521 82280182360777305610210141)
          ·
            refine ⟨30855068385291489603828803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82280182360777305610210141 30855068385291489603828803)
            ·
              refine ⟨46282602577937234405743205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30855068385291489603828803 46282602577937234405743205)
              ·
                refine ⟨8677987983363231451076851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46282602577937234405743205 8677987983363231451076851)
                ·
                  refine ⟨13016981975044847176615277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8677987983363231451076851 13016981975044847176615277)
                  ·
                    refine ⟨4881368240641817691230729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13016981975044847176615277 4881368240641817691230729)
                    ·
                      refine ⟨3661026180481363268423047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881368240641817691230729 3661026180481363268423047)
                      ·
                        rfl

theorem cell23_7129823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_7129823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129823 prefixEnd_7129823 := by exact prefixLift 7129823
  have htrace : WordTrace (prefixWord ++ tailWord_7129823) baseStart_7129823 baseEnd_7129823 := by
    simpa [prefixWord, tailWord_7129823, baseEnd_7129823] using wordTrace_append hprefix tailTrace_7129823
  have hstable : (prefixWord ++ tailWord_7129823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129823).length < 2 ^ (prefixWord ++ tailWord_7129823).sum := by decide
  have hdescent : baseEnd_7129823 < baseStart_7129823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129836 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_7129836 : Nat := 118140960795 + 7129836 * 2 ^ 59
def prefixEnd_7129836 : Nat := 4983230072969 + 3 ^ 40 * 7129836 * 2
def baseEnd_7129836 : Nat := 3661032855729871717560487

theorem tailTrace_7129836 : CollatzResearch.WordTrace tailWord_7129836 prefixEnd_7129836 3661032855729871717560487 := by
  unfold tailWord_7129836
  simp only [CollatzResearch.WordTrace]
  refine ⟨130023241298914662944764681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173364321731886217259686241 130023241298914662944764681)
  ·
    refine ⟨97517430974185997208573511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130023241298914662944764681 97517430974185997208573511)
    ·
      refine ⟨146276146461278995812860267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97517430974185997208573511 146276146461278995812860267)
      ·
        refine ⟨219414219691918493719290401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146276146461278995812860267 219414219691918493719290401)
        ·
          refine ⟨164560664768938870289467801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219414219691918493719290401 164560664768938870289467801)
          ·
            refine ⟨123420498576704152717100851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164560664768938870289467801 123420498576704152717100851)
            ·
              refine ⟨185130747865056229075651277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123420498576704152717100851 185130747865056229075651277)
              ·
                refine ⟨69424030449396085903369229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185130747865056229075651277 69424030449396085903369229)
                ·
                  refine ⟨26034011418523532213763461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69424030449396085903369229 26034011418523532213763461)
                  ·
                    refine ⟨4881377140973162290080649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26034011418523532213763461 4881377140973162290080649)
                    ·
                      refine ⟨3661032855729871717560487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881377140973162290080649 3661032855729871717560487)
                      ·
                        rfl

theorem cell23_7129836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_7129836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129836 prefixEnd_7129836 := by exact prefixLift 7129836
  have htrace : WordTrace (prefixWord ++ tailWord_7129836) baseStart_7129836 baseEnd_7129836 := by
    simpa [prefixWord, tailWord_7129836, baseEnd_7129836] using wordTrace_append hprefix tailTrace_7129836
  have hstable : (prefixWord ++ tailWord_7129836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129836).length < 2 ^ (prefixWord ++ tailWord_7129836).sum := by decide
  have hdescent : baseEnd_7129836 < baseStart_7129836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129839 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_7129839 : Nat := 118140960795 + 7129839 * 2 ^ 59
def prefixEnd_7129839 : Nat := 4983230072969 + 3 ^ 40 * 7129839 * 2
def baseEnd_7129839 : Nat := 3661034396171835205822973

theorem tailTrace_7129839 : CollatzResearch.WordTrace tailWord_7129839 prefixEnd_7129839 3661034396171835205822973 := by
  unfold tailWord_7129839
  simp only [CollatzResearch.WordTrace]
  refine ⟨260046592016818457401888571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173364394677878971601259047 260046592016818457401888571)
  ·
    refine ⟨390069888025227686102832857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260046592016818457401888571 390069888025227686102832857)
    ·
      refine ⟨292552416018920764577124643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390069888025227686102832857 292552416018920764577124643)
      ·
        refine ⟨438828624028381146865686965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292552416018920764577124643 438828624028381146865686965)
        ·
          refine ⟨41140183502660732518658153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 438828624028381146865686965 41140183502660732518658153)
          ·
            refine ⟨30855137626995549388993615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41140183502660732518658153 30855137626995549388993615)
            ·
              refine ⟨46282706440493324083490423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30855137626995549388993615 46282706440493324083490423)
              ·
                refine ⟨69424059660739986125235635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46282706440493324083490423 69424059660739986125235635)
                ·
                  refine ⟨104136089491109979187853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69424059660739986125235635 104136089491109979187853453)
                  ·
                    refine ⟨39051033559166242195445045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104136089491109979187853453 39051033559166242195445045)
                    ·
                      refine ⟨3661034396171835205822973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39051033559166242195445045 3661034396171835205822973)
                      ·
                        rfl

theorem cell23_7129839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_7129839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129839 prefixEnd_7129839 := by exact prefixLift 7129839
  have htrace : WordTrace (prefixWord ++ tailWord_7129839) baseStart_7129839 baseEnd_7129839 := by
    simpa [prefixWord, tailWord_7129839, baseEnd_7129839] using wordTrace_append hprefix tailTrace_7129839
  have hstable : (prefixWord ++ tailWord_7129839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129839).length < 2 ^ (prefixWord ++ tailWord_7129839).sum := by decide
  have hdescent : baseEnd_7129839 < baseStart_7129839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129849 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7129849 : Nat := 118140960795 + 7129849 * 2 ^ 59
def prefixEnd_7129849 : Nat := 4983230072969 + 3 ^ 40 * 7129849 * 2
def baseEnd_7129849 : Nat := 3661039530978380166697927

theorem tailTrace_7129849 : CollatzResearch.WordTrace tailWord_7129849 prefixEnd_7129849 3661039530978380166697927 := by
  unfold tailWord_7129849
  simp only [CollatzResearch.WordTrace]
  refine ⟨260046956746782229109752601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173364637831188152739835067 260046956746782229109752601)
  ·
    refine ⟨195035217560086671832314451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260046956746782229109752601 195035217560086671832314451)
    ·
      refine ⟨292552826340130007748471677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195035217560086671832314451 292552826340130007748471677)
      ·
        refine ⟨109707309877548752905676879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292552826340130007748471677 109707309877548752905676879)
        ·
          refine ⟨164560964816323129358515319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109707309877548752905676879 164560964816323129358515319)
          ·
            refine ⟨246841447224484694037772979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164560964816323129358515319 246841447224484694037772979)
            ·
              refine ⟨370262170836727041056659469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246841447224484694037772979 370262170836727041056659469)
              ·
                refine ⟨138848314063772640396247301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370262170836727041056659469 138848314063772640396247301)
                ·
                  refine ⟨26034058886957370074296369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138848314063772640396247301 26034058886957370074296369)
                  ·
                    refine ⟨19525544165218027555722277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26034058886957370074296369 19525544165218027555722277)
                    ·
                      refine ⟨3661039530978380166697927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19525544165218027555722277 3661039530978380166697927)
                      ·
                        rfl

theorem cell23_7129849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7129849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129849 prefixEnd_7129849 := by exact prefixLift 7129849
  have htrace : WordTrace (prefixWord ++ tailWord_7129849) baseStart_7129849 baseEnd_7129849 := by
    simpa [prefixWord, tailWord_7129849, baseEnd_7129849] using wordTrace_append hprefix tailTrace_7129849
  have hstable : (prefixWord ++ tailWord_7129849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129849).length < 2 ^ (prefixWord ++ tailWord_7129849).sum := by decide
  have hdescent : baseEnd_7129849 < baseStart_7129849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129853 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_7129853 : Nat := 118140960795 + 7129853 * 2 ^ 59
def prefixEnd_7129853 : Nat := 4983230072969 + 3 ^ 40 * 7129853 * 2
def baseEnd_7129853 : Nat := 3661041584900998151047909

theorem tailTrace_7129853 : CollatzResearch.WordTrace tailWord_7129853 prefixEnd_7129853 3661041584900998151047909 := by
  unfold tailWord_7129853
  simp only [CollatzResearch.WordTrace]
  refine ⟨260047102638767737792898213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173364735092511825195265475 260047102638767737792898213)
  ·
    refine ⟨48758831744768950836168415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260047102638767737792898213 48758831744768950836168415)
    ·
      refine ⟨73138247617153426254252623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48758831744768950836168415 73138247617153426254252623)
      ·
        refine ⟨109707371425730139381378935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73138247617153426254252623 109707371425730139381378935)
        ·
          refine ⟨164561057138595209072068403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109707371425730139381378935 164561057138595209072068403)
          ·
            refine ⟨246841585707892813608102605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164561057138595209072068403 246841585707892813608102605)
            ·
              refine ⟨92565594640459805103038477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246841585707892813608102605 92565594640459805103038477)
              ·
                refine ⟨34712097990172426913639429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92565594640459805103038477 34712097990172426913639429)
                ·
                  refine ⟨6508518373157330046307393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34712097990172426913639429 6508518373157330046307393)
                  ·
                    refine ⟨4881388779867997534730545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6508518373157330046307393 4881388779867997534730545)
                    ·
                      refine ⟨3661041584900998151047909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881388779867997534730545 3661041584900998151047909)
                      ·
                        rfl

theorem cell23_7129853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_7129853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129853 prefixEnd_7129853 := by exact prefixLift 7129853
  have htrace : WordTrace (prefixWord ++ tailWord_7129853) baseStart_7129853 baseEnd_7129853 := by
    simpa [prefixWord, tailWord_7129853, baseEnd_7129853] using wordTrace_append hprefix tailTrace_7129853
  have hstable : (prefixWord ++ tailWord_7129853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129853).length < 2 ^ (prefixWord ++ tailWord_7129853).sum := by decide
  have hdescent : baseEnd_7129853 < baseStart_7129853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129874 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7129874 : Nat := 118140960795 + 7129874 * 2 ^ 59
def prefixEnd_7129874 : Nat := 4983230072969 + 3 ^ 40 * 7129874 * 2
def baseEnd_7129874 : Nat := 3661052367994742568885313

theorem tailTrace_7129874 : CollatzResearch.WordTrace tailWord_7129874 prefixEnd_7129874 3661052367994742568885313 := by
  unfold tailWord_7129874
  simp only [CollatzResearch.WordTrace]
  refine ⟨65011967142922914594853169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173365245714461105586275117 65011967142922914594853169)
  ·
    refine ⟨48758975357192185946139877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65011967142922914594853169 48758975357192185946139877)
    ·
      refine ⟨9142307879473534864901227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48758975357192185946139877 9142307879473534864901227)
      ·
        refine ⟨13713461819210302297351841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142307879473534864901227 13713461819210302297351841)
        ·
          refine ⟨10285096364407726723013881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13713461819210302297351841 10285096364407726723013881)
          ·
            refine ⟨7713822273305795042260411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10285096364407726723013881 7713822273305795042260411)
            ·
              refine ⟨11570733409958692563390617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713822273305795042260411 11570733409958692563390617)
              ·
                refine ⟨8678050057469019422542963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11570733409958692563390617 8678050057469019422542963)
                ·
                  refine ⟨13017075086203529133814445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8678050057469019422542963 13017075086203529133814445)
                  ·
                    refine ⟨4881403157326323425180417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13017075086203529133814445 4881403157326323425180417)
                    ·
                      refine ⟨3661052367994742568885313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881403157326323425180417 3661052367994742568885313)
                      ·
                        rfl

theorem cell23_7129874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7129874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129874 prefixEnd_7129874 := by exact prefixLift 7129874
  have htrace : WordTrace (prefixWord ++ tailWord_7129874) baseStart_7129874 baseEnd_7129874 := by
    simpa [prefixWord, tailWord_7129874, baseEnd_7129874] using wordTrace_append hprefix tailTrace_7129874
  have hstable : (prefixWord ++ tailWord_7129874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129874).length < 2 ^ (prefixWord ++ tailWord_7129874).sum := by decide
  have hdescent : baseEnd_7129874 < baseStart_7129874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129899 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_7129899 : Nat := 118140960795 + 7129899 * 2 ^ 59
def prefixEnd_7129899 : Nat := 4983230072969 + 3 ^ 40 * 7129899 * 2
def baseEnd_7129899 : Nat := 3661065205011104971072697

theorem tailTrace_7129899 : CollatzResearch.WordTrace tailWord_7129899 prefixEnd_7129899 3661065205011104971072697 := by
  unfold tailWord_7129899
  simp only [CollatzResearch.WordTrace]
  refine ⟨260048780396601087649072751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173365853597734058432715167 260048780396601087649072751)
  ·
    refine ⟨390073170594901631473609127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260048780396601087649072751 390073170594901631473609127)
    ·
      refine ⟨585109755892352447210413691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390073170594901631473609127 585109755892352447210413691)
      ·
        refine ⟨877664633838528670815620537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585109755892352447210413691 877664633838528670815620537)
        ·
          refine ⟨658248475378896503111715403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877664633838528670815620537 658248475378896503111715403)
          ·
            refine ⟨987372713068344754667573105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658248475378896503111715403 987372713068344754667573105)
            ·
              refine ⟨740529534801258566000679829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987372713068344754667573105 740529534801258566000679829)
              ·
                refine ⟨34712321943808995281281867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 740529534801258566000679829 34712321943808995281281867)
                ·
                  refine ⟨52068482915713492921922801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34712321943808995281281867 52068482915713492921922801)
                  ·
                    refine ⟨39051362186785119691442101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52068482915713492921922801 39051362186785119691442101)
                    ·
                      refine ⟨3661065205011104971072697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39051362186785119691442101 3661065205011104971072697)
                      ·
                        rfl

theorem cell23_7129899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_7129899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129899 prefixEnd_7129899 := by exact prefixLift 7129899
  have htrace : WordTrace (prefixWord ++ tailWord_7129899) baseStart_7129899 baseEnd_7129899 := by
    simpa [prefixWord, tailWord_7129899, baseEnd_7129899] using wordTrace_append hprefix tailTrace_7129899
  have hstable : (prefixWord ++ tailWord_7129899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129899).length < 2 ^ (prefixWord ++ tailWord_7129899).sum := by decide
  have hdescent : baseEnd_7129899 < baseStart_7129899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129906 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_7129906 : Nat := 118140960795 + 7129906 * 2 ^ 59
def prefixEnd_7129906 : Nat := 4983230072969 + 3 ^ 40 * 7129906 * 2
def baseEnd_7129906 : Nat := 1220356266458562147895055

theorem tailTrace_7129906 : CollatzResearch.WordTrace tailWord_7129906 prefixEnd_7129906 1220356266458562147895055 := by
  unfold tailWord_7129906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65012258926893931961144393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173366023805050485229718381 65012258926893931961144393)
  ·
    refine ⟨48759194195170448970858295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65012258926893931961144393 48759194195170448970858295)
    ·
      refine ⟨73138791292755673456287443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759194195170448970858295 73138791292755673456287443)
      ·
        refine ⟨109708186939133510184431165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73138791292755673456287443 109708186939133510184431165)
        ·
          refine ⟨41140570102175066319161687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109708186939133510184431165 41140570102175066319161687)
          ·
            refine ⟨61710855153262599478742531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41140570102175066319161687 61710855153262599478742531)
            ·
              refine ⟨92566282729893899218113797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61710855153262599478742531 92566282729893899218113797)
              ·
                refine ⟨17356178011855106103396337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92566282729893899218113797 17356178011855106103396337)
                ·
                  refine ⟨13017133508891329577547253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356178011855106103396337 13017133508891329577547253)
                  ·
                    refine ⟨1220356266458562147895055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017133508891329577547253 1220356266458562147895055)
                    ·
                      rfl

theorem cell23_7129906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_7129906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129906 prefixEnd_7129906 := by exact prefixLift 7129906
  have htrace : WordTrace (prefixWord ++ tailWord_7129906) baseStart_7129906 baseEnd_7129906 := by
    simpa [prefixWord, tailWord_7129906, baseEnd_7129906] using wordTrace_append hprefix tailTrace_7129906
  have hstable : (prefixWord ++ tailWord_7129906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129906).length < 2 ^ (prefixWord ++ tailWord_7129906).sum := by decide
  have hdescent : baseEnd_7129906 < baseStart_7129906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129936 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_7129936 : Nat := 118140960795 + 7129936 * 2 ^ 59
def prefixEnd_7129936 : Nat := 4983230072969 + 3 ^ 40 * 7129936 * 2
def baseEnd_7129936 : Nat := 1220361401265107108770009

theorem tailTrace_7129936 : CollatzResearch.WordTrace tailWord_7129936 prefixEnd_7129936 1220361401265107108770009 := by
  unfold tailWord_7129936
  simp only [CollatzResearch.WordTrace]
  refine ⟨130025064948733521484084831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173366753264978028645446441 130025064948733521484084831)
  ·
    refine ⟨195037597423100282226127247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130025064948733521484084831 195037597423100282226127247)
    ·
      refine ⟨292556396134650423339190871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195037597423100282226127247 292556396134650423339190871)
      ·
        refine ⟨438834594201975635008786307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292556396134650423339190871 438834594201975635008786307)
        ·
          refine ⟨658251891302963452513179461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438834594201975635008786307 658251891302963452513179461)
          ·
            refine ⟨123422229619305647346221149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 658251891302963452513179461 123422229619305647346221149)
            ·
              refine ⟨46283336107239617754832931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123422229619305647346221149 46283336107239617754832931)
              ·
                refine ⟨69425004160859426632249397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46283336107239617754832931 69425004160859426632249397)
                ·
                  refine ⟨6508594140080571246773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69425004160859426632249397 6508594140080571246773381)
                  ·
                    refine ⟨1220361401265107108770009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508594140080571246773381 1220361401265107108770009)
                    ·
                      rfl

theorem cell23_7129936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_7129936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129936 prefixEnd_7129936 := by exact prefixLift 7129936
  have htrace : WordTrace (prefixWord ++ tailWord_7129936) baseStart_7129936 baseEnd_7129936 := by
    simpa [prefixWord, tailWord_7129936, baseEnd_7129936] using wordTrace_append hprefix tailTrace_7129936
  have hstable : (prefixWord ++ tailWord_7129936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129936).length < 2 ^ (prefixWord ++ tailWord_7129936).sum := by decide
  have hdescent : baseEnd_7129936 < baseStart_7129936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129939 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_7129939 : Nat := 118140960795 + 7129939 * 2 ^ 59
def prefixEnd_7129939 : Nat := 4983230072969 + 3 ^ 40 * 7129939 * 2
def baseEnd_7129939 : Nat := 3661085744237284814572513

theorem tailTrace_7129939 : CollatzResearch.WordTrace tailWord_7129939 prefixEnd_7129939 3661085744237284814572513 := by
  unfold tailWord_7129939
  simp only [CollatzResearch.WordTrace]
  refine ⟨260050239316456174480528871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173366826210970782987019247 260050239316456174480528871)
  ·
    refine ⟨390075358974684261720793307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260050239316456174480528871 390075358974684261720793307)
    ·
      refine ⟨585113038462026392581189961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390075358974684261720793307 585113038462026392581189961)
      ·
        refine ⟨438834778846519794435892471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585113038462026392581189961 438834778846519794435892471)
        ·
          refine ⟨658252168269779691653838707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438834778846519794435892471 658252168269779691653838707)
          ·
            refine ⟨987378252404669537480758061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658252168269779691653838707 987378252404669537480758061)
            ·
              refine ⟨370266844651751076555284273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987378252404669537480758061 370266844651751076555284273)
              ·
                refine ⟨277700133488813307416463205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370266844651751076555284273 277700133488813307416463205)
                ·
                  refine ⟨52068775029152495140586851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277700133488813307416463205 52068775029152495140586851)
                  ·
                    refine ⟨78103162543728742710880277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52068775029152495140586851 78103162543728742710880277)
                    ·
                      refine ⟨3661085744237284814572513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78103162543728742710880277 3661085744237284814572513)
                      ·
                        rfl

theorem cell23_7129939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_7129939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129939 prefixEnd_7129939 := by exact prefixLift 7129939
  have htrace : WordTrace (prefixWord ++ tailWord_7129939) baseStart_7129939 baseEnd_7129939 := by
    simpa [prefixWord, tailWord_7129939, baseEnd_7129939] using wordTrace_append hprefix tailTrace_7129939
  have hstable : (prefixWord ++ tailWord_7129939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129939).length < 2 ^ (prefixWord ++ tailWord_7129939).sum := by decide
  have hdescent : baseEnd_7129939 < baseStart_7129939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129940 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_7129940 : Nat := 118140960795 + 7129940 * 2 ^ 59
def prefixEnd_7129940 : Nat := 4983230072969 + 3 ^ 40 * 7129940 * 2
def baseEnd_7129940 : Nat := 1220362085905979770220003

theorem tailTrace_7129940 : CollatzResearch.WordTrace tailWord_7129940 prefixEnd_7129940 1220362085905979770220003 := by
  unfold tailWord_7129940
  simp only [CollatzResearch.WordTrace]
  refine ⟨130025137894726275825657637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173366850526301701100876849 130025137894726275825657637)
  ·
    refine ⟨24379713355261176717310807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130025137894726275825657637 24379713355261176717310807)
    ·
      refine ⟨36569570032891765075966211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24379713355261176717310807 36569570032891765075966211)
      ·
        refine ⟨54854355049337647613949317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36569570032891765075966211 54854355049337647613949317)
        ·
          refine ⟨10285191571750808927615497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54854355049337647613949317 10285191571750808927615497)
          ·
            refine ⟨7713893678813106695711623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10285191571750808927615497 7713893678813106695711623)
            ·
              refine ⟨11570840518219660043567435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713893678813106695711623 11570840518219660043567435)
              ·
                refine ⟨17356260777329490065351153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570840518219660043567435 17356260777329490065351153)
                ·
                  refine ⟨13017195582997117549013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356260777329490065351153 13017195582997117549013365)
                  ·
                    refine ⟨1220362085905979770220003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017195582997117549013365 1220362085905979770220003)
                    ·
                      rfl

theorem cell23_7129940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_7129940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129940 prefixEnd_7129940 := by exact prefixLift 7129940
  have htrace : WordTrace (prefixWord ++ tailWord_7129940) baseStart_7129940 baseEnd_7129940 := by
    simpa [prefixWord, tailWord_7129940, baseEnd_7129940] using wordTrace_append hprefix tailTrace_7129940
  have hstable : (prefixWord ++ tailWord_7129940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129940).length < 2 ^ (prefixWord ++ tailWord_7129940).sum := by decide
  have hdescent : baseEnd_7129940 < baseStart_7129940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129943 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_7129943 : Nat := 118140960795 + 7129943 * 2 ^ 59
def prefixEnd_7129943 : Nat := 4983230072969 + 3 ^ 40 * 7129943 * 2
def baseEnd_7129943 : Nat := 3661087798159902798922495

theorem tailTrace_7129943 : CollatzResearch.WordTrace tailWord_7129943 prefixEnd_7129943 3661087798159902798922495 := by
  unfold tailWord_7129943
  simp only [CollatzResearch.WordTrace]
  refine ⟨260050385208441683163674483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173366923472294455442449655 260050385208441683163674483)
  ·
    refine ⟨390075577812662524745511725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260050385208441683163674483 390075577812662524745511725)
    ·
      refine ⟨146278341679748446779566897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390075577812662524745511725 146278341679748446779566897)
      ·
        refine ⟨109708756259811335084675173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146278341679748446779566897 109708756259811335084675173)
        ·
          refine ⟨20570391798714625328376595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109708756259811335084675173 20570391798714625328376595)
          ·
            refine ⟨30855587698071937992564893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20570391798714625328376595 30855587698071937992564893)
            ·
              refine ⟨11570845386776976747211835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30855587698071937992564893 11570845386776976747211835)
              ·
                refine ⟨17356268080165465120817753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570845386776976747211835 17356268080165465120817753)
                ·
                  refine ⟨13017201060124098840613315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356268080165465120817753 13017201060124098840613315)
                  ·
                    refine ⟨19525801590186148260919973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13017201060124098840613315 19525801590186148260919973)
                    ·
                      refine ⟨3661087798159902798922495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19525801590186148260919973 3661087798159902798922495)
                      ·
                        rfl

theorem cell23_7129943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_7129943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129943 prefixEnd_7129943 := by exact prefixLift 7129943
  have htrace : WordTrace (prefixWord ++ tailWord_7129943) baseStart_7129943 baseEnd_7129943 := by
    simpa [prefixWord, tailWord_7129943, baseEnd_7129943] using wordTrace_append hprefix tailTrace_7129943
  have hstable : (prefixWord ++ tailWord_7129943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129943).length < 2 ^ (prefixWord ++ tailWord_7129943).sum := by decide
  have hdescent : baseEnd_7129943 < baseStart_7129943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129956 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_7129956 : Nat := 118140960795 + 7129956 * 2 ^ 59
def prefixEnd_7129956 : Nat := 4983230072969 + 3 ^ 40 * 7129956 * 2
def baseEnd_7129956 : Nat := 3661094473408411248059935

theorem tailTrace_7129956 : CollatzResearch.WordTrace tailWord_7129956 prefixEnd_7129956 3661094473408411248059935 := by
  unfold tailWord_7129956
  simp only [CollatzResearch.WordTrace]
  refine ⟨130025429678697293191948861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173367239571596390922598481 130025429678697293191948861)
  ·
    refine ⟨48759536129511484946980823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130025429678697293191948861 48759536129511484946980823)
    ·
      refine ⟨73139304194267227420471235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759536129511484946980823 73139304194267227420471235)
      ·
        refine ⟨109708956291400841130706853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73139304194267227420471235 109708956291400841130706853)
        ·
          refine ⟨20570429304637657712007535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109708956291400841130706853 20570429304637657712007535)
          ·
            refine ⟨30855643956956486568011303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20570429304637657712007535 30855643956956486568011303)
            ·
              refine ⟨46283465935434729852016955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30855643956956486568011303 46283465935434729852016955)
              ·
                refine ⟨69425198903152094778025433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46283465935434729852016955 69425198903152094778025433)
                ·
                  refine ⟨52068899177364071083519075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69425198903152094778025433 52068899177364071083519075)
                  ·
                    refine ⟨78103348766046106625278613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52068899177364071083519075 78103348766046106625278613)
                    ·
                      refine ⟨3661094473408411248059935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78103348766046106625278613 3661094473408411248059935)
                      ·
                        rfl

theorem cell23_7129956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_7129956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129956 prefixEnd_7129956 := by exact prefixLift 7129956
  have htrace : WordTrace (prefixWord ++ tailWord_7129956) baseStart_7129956 baseEnd_7129956 := by
    simpa [prefixWord, tailWord_7129956, baseEnd_7129956] using wordTrace_append hprefix tailTrace_7129956
  have hstable : (prefixWord ++ tailWord_7129956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129956).length < 2 ^ (prefixWord ++ tailWord_7129956).sum := by decide
  have hdescent : baseEnd_7129956 < baseStart_7129956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129970 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_7129970 : Nat := 118140960795 + 7129970 * 2 ^ 59
def prefixEnd_7129970 : Nat := 4983230072969 + 3 ^ 40 * 7129970 * 2
def baseEnd_7129970 : Nat := 1220367220712524731094957

theorem tailTrace_7129970 : CollatzResearch.WordTrace tailWord_7129970 prefixEnd_7129970 1220367220712524731094957 := by
  unfold tailWord_7129970
  simp only [CollatzResearch.WordTrace]
  refine ⟨65012842494835966693726841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173367579986229244516604909 65012842494835966693726841)
  ·
    refine ⟨48759631871126975020295131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65012842494835966693726841 48759631871126975020295131)
    ·
      refine ⟨73139447806690462530442697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759631871126975020295131 73139447806690462530442697)
      ·
        refine ⟨54854585855017846897832023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73139447806690462530442697 54854585855017846897832023)
        ·
          refine ⟨82281878782526770346748035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54854585855017846897832023 82281878782526770346748035)
          ·
            refine ⟨123422818173790155520122053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82281878782526770346748035 123422818173790155520122053)
            ·
              refine ⟨23141778407585654160022885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123422818173790155520122053 23141778407585654160022885)
              ·
                refine ⟨4339083451422310155004291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23141778407585654160022885 4339083451422310155004291)
                ·
                  refine ⟨6508625177133465232506437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339083451422310155004291 6508625177133465232506437)
                  ·
                    refine ⟨1220367220712524731094957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508625177133465232506437 1220367220712524731094957)
                    ·
                      rfl

theorem cell23_7129970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_7129970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129970 prefixEnd_7129970 := by exact prefixLift 7129970
  have htrace : WordTrace (prefixWord ++ tailWord_7129970) baseStart_7129970 baseEnd_7129970 := by
    simpa [prefixWord, tailWord_7129970, baseEnd_7129970] using wordTrace_append hprefix tailTrace_7129970
  have hstable : (prefixWord ++ tailWord_7129970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129970).length < 2 ^ (prefixWord ++ tailWord_7129970).sum := by decide
  have hdescent : baseEnd_7129970 < baseStart_7129970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7129996 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_7129996 : Nat := 118140960795 + 7129996 * 2 ^ 59
def prefixEnd_7129996 : Nat := 4983230072969 + 3 ^ 40 * 7129996 * 2
def baseEnd_7129996 : Nat := 1220371670878197030519917

theorem tailTrace_7129996 : CollatzResearch.WordTrace tailWord_7129996 prefixEnd_7129996 1220371670878197030519917 := by
  unfold tailWord_7129996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130026159138624836607676921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173368212184833115476902561 130026159138624836607676921)
  ·
    refine ⟨97519619353968627455757691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130026159138624836607676921 97519619353968627455757691)
    ·
      refine ⟨146279429030952941183636537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97519619353968627455757691 146279429030952941183636537)
      ·
        refine ⟨109709571773214705887727403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146279429030952941183636537 109709571773214705887727403)
        ·
          refine ⟨164564357659822058831591105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109709571773214705887727403 164564357659822058831591105)
          ·
            refine ⟨123423268244866544123693329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164564357659822058831591105 123423268244866544123693329)
            ·
              refine ⟨92567451183649908092769997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123423268244866544123693329 92567451183649908092769997)
              ·
                refine ⟨34712794193868715534788749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92567451183649908092769997 34712794193868715534788749)
                ·
                  refine ⟨13017297822700768325545781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34712794193868715534788749 13017297822700768325545781)
                  ·
                    refine ⟨1220371670878197030519917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017297822700768325545781 1220371670878197030519917)
                    ·
                      rfl

theorem cell23_7129996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_7129996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7129996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7129996 prefixEnd_7129996 := by exact prefixLift 7129996
  have htrace : WordTrace (prefixWord ++ tailWord_7129996) baseStart_7129996 baseEnd_7129996 := by
    simpa [prefixWord, tailWord_7129996, baseEnd_7129996] using wordTrace_append hprefix tailTrace_7129996
  have hstable : (prefixWord ++ tailWord_7129996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7129996).length < 2 ^ (prefixWord ++ tailWord_7129996).sum := by decide
  have hdescent : baseEnd_7129996 < baseStart_7129996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7129996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130013 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7130013 : Nat := 118140960795 + 7130013 * 2 ^ 59
def prefixEnd_7130013 : Nat := 4983230072969 + 3 ^ 40 * 7130013 * 2
def baseEnd_7130013 : Nat := 1220374580601905841682391

theorem tailTrace_7130013 : CollatzResearch.WordTrace tailWord_7130013 prefixEnd_7130013 1220374580601905841682391 := by
  unfold tailWord_7130013
  simp only [CollatzResearch.WordTrace]
  refine ⟨260052938318188085118722693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173368625545458723412481795 260052938318188085118722693)
  ·
    refine ⟨48759925934660265959760505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260052938318188085118722693 48759925934660265959760505)
    ·
      refine ⟨36569944450995199469820379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48759925934660265959760505 36569944450995199469820379)
      ·
        refine ⟨54854916676492799204730569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36569944450995199469820379 54854916676492799204730569)
        ·
          refine ⟨41141187507369599403547927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54854916676492799204730569 41141187507369599403547927)
          ·
            refine ⟨61711781261054399105321891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41141187507369599403547927 61711781261054399105321891)
            ·
              refine ⟨92567671891581598657982837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61711781261054399105321891 92567671891581598657982837)
              ·
                refine ⟨8678219239835774874185891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92567671891581598657982837 8678219239835774874185891)
                ·
                  refine ⟨13017328859753662311278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8678219239835774874185891 13017328859753662311278837)
                  ·
                    refine ⟨1220374580601905841682391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017328859753662311278837 1220374580601905841682391)
                    ·
                      rfl

theorem cell23_7130013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7130013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130013 prefixEnd_7130013 := by exact prefixLift 7130013
  have htrace : WordTrace (prefixWord ++ tailWord_7130013) baseStart_7130013 baseEnd_7130013 := by
    simpa [prefixWord, tailWord_7130013, baseEnd_7130013] using wordTrace_append hprefix tailTrace_7130013
  have hstable : (prefixWord ++ tailWord_7130013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130013).length < 2 ^ (prefixWord ++ tailWord_7130013).sum := by decide
  have hdescent : baseEnd_7130013 < baseStart_7130013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130020 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_7130020 : Nat := 118140960795 + 7130020 * 2 ^ 59
def prefixEnd_7130020 : Nat := 4983230072969 + 3 ^ 40 * 7130020 * 2
def baseEnd_7130020 : Nat := 3661127336170298997659641

theorem tailTrace_7130020 : CollatzResearch.WordTrace tailWord_7130020 prefixEnd_7130020 3661127336170298997659641 := by
  unfold tailWord_7130020
  simp only [CollatzResearch.WordTrace]
  refine ⟨130026596814581362657113757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173368795752775150209485009 130026596814581362657113757)
  ·
    refine ⟨48759973805468010996417659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130026596814581362657113757 48759973805468010996417659)
    ·
      refine ⟨73139960708202016494626489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759973805468010996417659 73139960708202016494626489)
      ·
        refine ⟨54854970531151512370969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73139960708202016494626489 54854970531151512370969867)
        ·
          refine ⟨82282455796727268556454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54854970531151512370969867 82282455796727268556454801)
          ·
            refine ⟨61711841847545451417341101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82282455796727268556454801 61711841847545451417341101)
            ·
              refine ⟨23141940692829544281502913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61711841847545451417341101 23141940692829544281502913)
              ·
                refine ⟨17356455519622158211127185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23141940692829544281502913 17356455519622158211127185)
                ·
                  refine ⟨13017341639716618658345389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17356455519622158211127185 13017341639716618658345389)
                  ·
                    refine ⟨4881503114893731996879521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13017341639716618658345389 4881503114893731996879521)
                    ·
                      refine ⟨3661127336170298997659641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881503114893731996879521 3661127336170298997659641)
                      ·
                        rfl

theorem cell23_7130020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_7130020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130020 prefixEnd_7130020 := by exact prefixLift 7130020
  have htrace : WordTrace (prefixWord ++ tailWord_7130020) baseStart_7130020 baseEnd_7130020 := by
    simpa [prefixWord, tailWord_7130020, baseEnd_7130020] using wordTrace_append hprefix tailTrace_7130020
  have hstable : (prefixWord ++ tailWord_7130020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130020).length < 2 ^ (prefixWord ++ tailWord_7130020).sum := by decide
  have hdescent : baseEnd_7130020 < baseStart_7130020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130063 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_7130063 : Nat := 118140960795 + 7130063 * 2 ^ 59
def prefixEnd_7130063 : Nat := 4983230072969 + 3 ^ 40 * 7130063 * 2
def baseEnd_7130063 : Nat := 3661149415838442329421943

theorem tailTrace_7130063 : CollatzResearch.WordTrace tailWord_7130063 prefixEnd_7130063 3661149415838442329421943 := by
  unfold tailWord_7130063
  simp only [CollatzResearch.WordTrace]
  refine ⟨260054761968006943658042843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173369841312004629105361895 260054761968006943658042843)
  ·
    refine ⟨390082142952010415487064265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260054761968006943658042843 390082142952010415487064265)
    ·
      refine ⟨292561607214007811615298199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390082142952010415487064265 292561607214007811615298199)
      ·
        refine ⟨438842410821011717422947299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292561607214007811615298199 438842410821011717422947299)
        ·
          refine ⟨658263616231517576134420949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438842410821011717422947299 658263616231517576134420949)
          ·
            refine ⟨15428053505426193190650491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 658263616231517576134420949 15428053505426193190650491)
            ·
              refine ⟨23142080258139289785975737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15428053505426193190650491 23142080258139289785975737)
              ·
                refine ⟨17356560193604467339481803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23142080258139289785975737 17356560193604467339481803)
                ·
                  refine ⟨26034840290406701009222705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17356560193604467339481803 26034840290406701009222705)
                  ·
                    refine ⟨19526130217805025756917029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26034840290406701009222705 19526130217805025756917029)
                    ·
                      refine ⟨3661149415838442329421943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19526130217805025756917029 3661149415838442329421943)
                      ·
                        rfl

theorem cell23_7130063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_7130063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130063 prefixEnd_7130063 := by exact prefixLift 7130063
  have htrace : WordTrace (prefixWord ++ tailWord_7130063) baseStart_7130063 baseEnd_7130063 := by
    simpa [prefixWord, tailWord_7130063, baseEnd_7130063] using wordTrace_append hprefix tailTrace_7130063
  have hstable : (prefixWord ++ tailWord_7130063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130063).length < 2 ^ (prefixWord ++ tailWord_7130063).sum := by decide
  have hdescent : baseEnd_7130063 < baseStart_7130063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130077 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7130077 : Nat := 118140960795 + 7130077 * 2 ^ 59
def prefixEnd_7130077 : Nat := 4983230072969 + 3 ^ 40 * 7130077 * 2
def baseEnd_7130077 : Nat := 1220385534855868424882293

theorem tailTrace_7130077 : CollatzResearch.WordTrace tailWord_7130077 prefixEnd_7130077 1220385534855868424882293 := by
  unfold tailWord_7130077
  simp only [CollatzResearch.WordTrace]
  refine ⟨260055272589956224049052485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173370181726637482699368323 260055272589956224049052485)
  ·
    refine ⟨48760363610616792009197341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260055272589956224049052485 48760363610616792009197341)
    ·
      refine ⟨18285136353981297003449003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48760363610616792009197341 18285136353981297003449003)
      ·
        refine ⟨27427704530971945505173505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18285136353981297003449003 27427704530971945505173505)
        ·
          refine ⟨20570778398228959128880129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27427704530971945505173505 20570778398228959128880129)
          ·
            refine ⟨15428083798671719346660097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20570778398228959128880129 15428083798671719346660097)
            ·
              refine ⟨11571062849003789509995073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15428083798671719346660097 11571062849003789509995073)
              ·
                refine ⟨8678297136752842132496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11571062849003789509995073 8678297136752842132496305)
                ·
                  refine ⟨6508722852564631599372229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678297136752842132496305 6508722852564631599372229)
                  ·
                    refine ⟨1220385534855868424882293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508722852564631599372229 1220385534855868424882293)
                    ·
                      rfl

theorem cell23_7130077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7130077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130077 prefixEnd_7130077 := by exact prefixLift 7130077
  have htrace : WordTrace (prefixWord ++ tailWord_7130077) baseStart_7130077 baseEnd_7130077 := by
    simpa [prefixWord, tailWord_7130077, baseEnd_7130077] using wordTrace_append hprefix tailTrace_7130077
  have hstable : (prefixWord ++ tailWord_7130077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130077).length < 2 ^ (prefixWord ++ tailWord_7130077).sum := by decide
  have hdescent : baseEnd_7130077 < baseStart_7130077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130083 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7130083 : Nat := 118140960795 + 7130083 * 2 ^ 59
def prefixEnd_7130083 : Nat := 4983230072969 + 3 ^ 40 * 7130083 * 2
def baseEnd_7130083 : Nat := 3661159685451532251171851

theorem tailTrace_7130083 : CollatzResearch.WordTrace tailWord_7130083 prefixEnd_7130083 3661159685451532251171851 := by
  unfold tailWord_7130083
  simp only [CollatzResearch.WordTrace]
  refine ⟨260055491427934487073770903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173370327618622991382513935 260055491427934487073770903)
  ·
    refine ⟨390083237141901730610656355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260055491427934487073770903 390083237141901730610656355)
    ·
      refine ⟨585124855712852595915984533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390083237141901730610656355 585124855712852595915984533)
      ·
        refine ⟨27427727611539965433561775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 585124855712852595915984533 27427727611539965433561775)
        ·
          refine ⟨41141591417309948150342663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27427727611539965433561775 41141591417309948150342663)
          ·
            refine ⟨61712387125964922225513995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41141591417309948150342663 61712387125964922225513995)
            ·
              refine ⟨92568580688947383338270993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61712387125964922225513995 92568580688947383338270993)
              ·
                refine ⟨69426435516710537503703245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92568580688947383338270993 69426435516710537503703245)
                ·
                  refine ⟨26034913318766451563888717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69426435516710537503703245 26034913318766451563888717)
                  ·
                    refine ⟨9763092494537419336458269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26034913318766451563888717 9763092494537419336458269)
                    ·
                      refine ⟨3661159685451532251171851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763092494537419336458269 3661159685451532251171851)
                      ·
                        rfl

theorem cell23_7130083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7130083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130083 prefixEnd_7130083 := by exact prefixLift 7130083
  have htrace : WordTrace (prefixWord ++ tailWord_7130083) baseStart_7130083 baseEnd_7130083 := by
    simpa [prefixWord, tailWord_7130083, baseEnd_7130083] using wordTrace_append hprefix tailTrace_7130083
  have hstable : (prefixWord ++ tailWord_7130083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130083).length < 2 ^ (prefixWord ++ tailWord_7130083).sum := by decide
  have hdescent : baseEnd_7130083 < baseStart_7130083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130096 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_7130096 : Nat := 118140960795 + 7130096 * 2 ^ 59
def prefixEnd_7130096 : Nat := 4983230072969 + 3 ^ 40 * 7130096 * 2
def baseEnd_7130096 : Nat := 3661166360700040700309291

theorem tailTrace_7130096 : CollatzResearch.WordTrace tailWord_7130096 prefixEnd_7130096 3661166360700040700309291 := by
  unfold tailWord_7130096
  simp only [CollatzResearch.WordTrace]
  refine ⟨130027982788443695146997071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173370643717924926862662761 130027982788443695146997071)
  ·
    refine ⟨195041974182665542720495607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130027982788443695146997071 195041974182665542720495607)
    ·
      refine ⟨292562961273998314080743411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195041974182665542720495607 292562961273998314080743411)
      ·
        refine ⟨438844441910997471121115117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292562961273998314080743411 438844441910997471121115117)
        ·
          refine ⟨164566665716624051670418169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438844441910997471121115117 164566665716624051670418169)
          ·
            refine ⟨123424999287468038752813627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164566665716624051670418169 123424999287468038752813627)
            ·
              refine ⟨185137498931202058129220441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123424999287468038752813627 185137498931202058129220441)
              ·
                refine ⟨138853124198401543596915331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185137498931202058129220441 138853124198401543596915331)
                ·
                  refine ⟨208279686297602315395372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138853124198401543596915331 208279686297602315395372997)
                  ·
                    refine ⟨39052441180800434136632437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208279686297602315395372997 39052441180800434136632437)
                    ·
                      refine ⟨3661166360700040700309291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39052441180800434136632437 3661166360700040700309291)
                      ·
                        rfl

theorem cell23_7130096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_7130096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130096 prefixEnd_7130096 := by exact prefixLift 7130096
  have htrace : WordTrace (prefixWord ++ tailWord_7130096) baseStart_7130096 baseEnd_7130096 := by
    simpa [prefixWord, tailWord_7130096, baseEnd_7130096] using wordTrace_append hprefix tailTrace_7130096
  have hstable : (prefixWord ++ tailWord_7130096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130096).length < 2 ^ (prefixWord ++ tailWord_7130096).sum := by decide
  have hdescent : baseEnd_7130096 < baseStart_7130096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130101 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7130101 : Nat := 118140960795 + 7130101 * 2 ^ 59
def prefixEnd_7130101 : Nat := 4983230072969 + 3 ^ 40 * 7130101 * 2
def baseEnd_7130101 : Nat := 3661168928103313180746769

theorem tailTrace_7130101 : CollatzResearch.WordTrace tailWord_7130101 prefixEnd_7130101 3661168928103313180746769 := by
  unfold tailWord_7130101
  simp only [CollatzResearch.WordTrace]
  refine ⟨260056147941869276147926157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173370765294579517431950771 260056147941869276147926157)
  ·
    refine ⟨97521055478200978555472309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260056147941869276147926157 97521055478200978555472309)
    ·
      refine ⟨9142598951081341739575529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97521055478200978555472309 9142598951081341739575529)
      ·
        refine ⟨6856949213311006304681647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9142598951081341739575529 6856949213311006304681647)
        ·
          refine ⟨10285423819966509457022471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856949213311006304681647 10285423819966509457022471)
          ·
            refine ⟨15428135729949764185533707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10285423819966509457022471 15428135729949764185533707)
            ·
              refine ⟨23142203594924646278300561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15428135729949764185533707 23142203594924646278300561)
              ·
                refine ⟨17356652696193484708725421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23142203594924646278300561 17356652696193484708725421)
                ·
                  refine ⟨6508744761072556765772033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17356652696193484708725421 6508744761072556765772033)
                  ·
                    refine ⟨4881558570804417574329025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6508744761072556765772033 4881558570804417574329025)
                    ·
                      refine ⟨3661168928103313180746769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881558570804417574329025 3661168928103313180746769)
                      ·
                        rfl

theorem cell23_7130101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7130101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130101 prefixEnd_7130101 := by exact prefixLift 7130101
  have htrace : WordTrace (prefixWord ++ tailWord_7130101) baseStart_7130101 baseEnd_7130101 := by
    simpa [prefixWord, tailWord_7130101, baseEnd_7130101] using wordTrace_append hprefix tailTrace_7130101
  have hstable : (prefixWord ++ tailWord_7130101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130101).length < 2 ^ (prefixWord ++ tailWord_7130101).sum := by decide
  have hdescent : baseEnd_7130101 < baseStart_7130101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130133 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_7130133 : Nat := 118140960795 + 7130133 * 2 ^ 59
def prefixEnd_7130133 : Nat := 4983230072969 + 3 ^ 40 * 7130133 * 2
def baseEnd_7130133 : Nat := 1220395119828085685182207

theorem tailTrace_7130133 : CollatzResearch.WordTrace tailWord_7130133 prefixEnd_7130133 1220395119828085685182207 := by
  unfold tailWord_7130133
  simp only [CollatzResearch.WordTrace]
  refine ⟨260057315077753345613091053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173371543385168897075394035 260057315077753345613091053)
  ·
    refine ⟨97521493154157504604909145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260057315077753345613091053 97521493154157504604909145)
    ·
      refine ⟨73141119865618128453681859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97521493154157504604909145 73141119865618128453681859)
      ·
        refine ⟨109711679798427192680522789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73141119865618128453681859 109711679798427192680522789)
        ·
          refine ⟨20570939962205098627598023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109711679798427192680522789 20570939962205098627598023)
          ·
            refine ⟨30856409943307647941397035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20570939962205098627598023 30856409943307647941397035)
            ·
              refine ⟨46284614914961471912095553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30856409943307647941397035 46284614914961471912095553)
              ·
                refine ⟨34713461186221103934071665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46284614914961471912095553 34713461186221103934071665)
                ·
                  refine ⟨26035095889665827950553749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34713461186221103934071665 26035095889665827950553749)
                  ·
                    refine ⟨1220395119828085685182207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26035095889665827950553749 1220395119828085685182207)
                    ·
                      rfl

theorem cell23_7130133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_7130133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130133 prefixEnd_7130133 := by exact prefixLift 7130133
  have htrace : WordTrace (prefixWord ++ tailWord_7130133) baseStart_7130133 baseEnd_7130133 := by
    simpa [prefixWord, tailWord_7130133, baseEnd_7130133] using wordTrace_append hprefix tailTrace_7130133
  have hstable : (prefixWord ++ tailWord_7130133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130133).length < 2 ^ (prefixWord ++ tailWord_7130133).sum := by decide
  have hdescent : baseEnd_7130133 < baseStart_7130133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130151 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7130151 : Nat := 118140960795 + 7130151 * 2 ^ 59
def prefixEnd_7130151 : Nat := 4983230072969 + 3 ^ 40 * 7130151 * 2
def baseEnd_7130151 : Nat := 3661194602136037985121539

theorem tailTrace_7130151 : CollatzResearch.WordTrace tailWord_7130151 prefixEnd_7130151 3661194602136037985121539 := by
  unfold tailWord_7130151
  simp only [CollatzResearch.WordTrace]
  refine ⟨260057971591688134687246307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173371981061125423124830871 260057971591688134687246307)
  ·
    refine ⟨390086957387532202030869461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260057971591688134687246307 390086957387532202030869461)
    ·
      refine ⟨9142663063770285985098503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 390086957387532202030869461 9142663063770285985098503)
      ·
        refine ⟨13713994595655428977647755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9142663063770285985098503 13713994595655428977647755)
        ·
          refine ⟨20570991893483143466471633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13713994595655428977647755 20570991893483143466471633)
          ·
            refine ⟨15428243920112357599853725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20570991893483143466471633 15428243920112357599853725)
            ·
              refine ⟨5785591470042134099945147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15428243920112357599853725 5785591470042134099945147)
              ·
                refine ⟨8678387205063201149917721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5785591470042134099945147 8678387205063201149917721)
                ·
                  refine ⟨6508790403797400862438291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678387205063201149917721 6508790403797400862438291)
                  ·
                    refine ⟨9763185605696101293657437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6508790403797400862438291 9763185605696101293657437)
                    ·
                      refine ⟨3661194602136037985121539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763185605696101293657437 3661194602136037985121539)
                      ·
                        rfl

theorem cell23_7130151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7130151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130151 prefixEnd_7130151 := by exact prefixLift 7130151
  have htrace : WordTrace (prefixWord ++ tailWord_7130151) baseStart_7130151 baseEnd_7130151 := by
    simpa [prefixWord, tailWord_7130151, baseEnd_7130151] using wordTrace_append hprefix tailTrace_7130151
  have hstable : (prefixWord ++ tailWord_7130151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130151).length < 2 ^ (prefixWord ++ tailWord_7130151).sum := by decide
  have hdescent : baseEnd_7130151 < baseStart_7130151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130174 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7130174 : Nat := 118140960795 + 7130174 * 2 ^ 59
def prefixEnd_7130174 : Nat := 4983230072969 + 3 ^ 40 * 7130174 * 2
def baseEnd_7130174 : Nat := 3661206412191091395133933

theorem tailTrace_7130174 : CollatzResearch.WordTrace tailWord_7130174 prefixEnd_7130174 3661206412191091395133933 := by
  unfold tailWord_7130174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32507351308825601201916697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173372540313736539743555717 32507351308825601201916697)
  ·
    refine ⟨24380513481619200901437523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32507351308825601201916697 24380513481619200901437523)
    ·
      refine ⟨36570770222428801352156285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24380513481619200901437523 36570770222428801352156285)
      ·
        refine ⟨13714038833410800507058607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36570770222428801352156285 13714038833410800507058607)
        ·
          refine ⟨20571058250116200760587911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13714038833410800507058607 20571058250116200760587911)
          ·
            refine ⟨30856587375174301140881867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20571058250116200760587911 30856587375174301140881867)
            ·
              refine ⟨46284881062761451711322801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30856587375174301140881867 46284881062761451711322801)
              ·
                refine ⟨34713660797071088783492101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46284881062761451711322801 34713660797071088783492101)
                ·
                  refine ⟨6508811399450829146904769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34713660797071088783492101 6508811399450829146904769)
                  ·
                    refine ⟨4881608549588121860178577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6508811399450829146904769 4881608549588121860178577)
                    ·
                      refine ⟨3661206412191091395133933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881608549588121860178577 3661206412191091395133933)
                      ·
                        rfl

theorem cell23_7130174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7130174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130174 prefixEnd_7130174 := by exact prefixLift 7130174
  have htrace : WordTrace (prefixWord ++ tailWord_7130174) baseStart_7130174 baseEnd_7130174 := by
    simpa [prefixWord, tailWord_7130174, baseEnd_7130174] using wordTrace_append hprefix tailTrace_7130174
  have hstable : (prefixWord ++ tailWord_7130174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130174).length < 2 ^ (prefixWord ++ tailWord_7130174).sum := by decide
  have hdescent : baseEnd_7130174 < baseStart_7130174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130193 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_7130193 : Nat := 118140960795 + 7130193 * 2 ^ 59
def prefixEnd_7130193 : Nat := 4983230072969 + 3 ^ 40 * 7130193 * 2
def baseEnd_7130193 : Nat := 1220405389441175606932115

theorem tailTrace_7130193 : CollatzResearch.WordTrace tailWord_7130193 prefixEnd_7130193 1220405389441175606932115 := by
  unfold tailWord_7130193
  simp only [CollatzResearch.WordTrace]
  refine ⟨260059503457535975860275233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173373002305023983906850155 260059503457535975860275233)
  ·
    refine ⟨195044627593151981895206425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260059503457535975860275233 195044627593151981895206425)
    ·
      refine ⟨146283470694863986421404819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195044627593151981895206425 146283470694863986421404819)
      ·
        refine ⟨219425206042295979632107229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146283470694863986421404819 219425206042295979632107229)
        ·
          refine ⟨82284452265860992362040211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219425206042295979632107229 82284452265860992362040211)
          ·
            refine ⟨123426678398791488543060317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82284452265860992362040211 123426678398791488543060317)
            ·
              refine ⟨46285004399546808203647619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123426678398791488543060317 46285004399546808203647619)
              ·
                refine ⟨69427506599320212305471429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46285004399546808203647619 69427506599320212305471429)
                ·
                  refine ⟨13017657487372539807275893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69427506599320212305471429 13017657487372539807275893)
                  ·
                    refine ⟨1220405389441175606932115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13017657487372539807275893 1220405389441175606932115)
                    ·
                      rfl

theorem cell23_7130193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_7130193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130193 prefixEnd_7130193 := by exact prefixLift 7130193
  have htrace : WordTrace (prefixWord ++ tailWord_7130193) baseStart_7130193 baseEnd_7130193 := by
    simpa [prefixWord, tailWord_7130193, baseEnd_7130193] using wordTrace_append hprefix tailTrace_7130193
  have hstable : (prefixWord ++ tailWord_7130193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130193).length < 2 ^ (prefixWord ++ tailWord_7130193).sum := by decide
  have hdescent : baseEnd_7130193 < baseStart_7130193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130197 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 5]
def baseStart_7130197 : Nat := 118140960795 + 7130197 * 2 ^ 59
def prefixEnd_7130197 : Nat := 4983230072969 + 3 ^ 40 * 7130197 * 2
def baseEnd_7130197 : Nat := 406802024694016089460703

theorem tailTrace_7130197 : CollatzResearch.WordTrace tailWord_7130197 prefixEnd_7130197 406802024694016089460703 := by
  unfold tailWord_7130197
  simp only [CollatzResearch.WordTrace]
  refine ⟨260059649349521484543420845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173373099566347656362280563 260059649349521484543420845)
  ·
    refine ⟨97522368506070556703782817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260059649349521484543420845 97522368506070556703782817)
    ·
      refine ⟨73141776379552917527837113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97522368506070556703782817 73141776379552917527837113)
      ·
        refine ⟨54856332284664688145877835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73141776379552917527837113 54856332284664688145877835)
        ·
          refine ⟨82284498426997032218816753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54856332284664688145877835 82284498426997032218816753)
          ·
            refine ⟨61713373820247774164112565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82284498426997032218816753 61713373820247774164112565)
            ·
              refine ⟨5785628795648228827885553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61713373820247774164112565 5785628795648228827885553)
              ·
                refine ⟨4339221596736171620914165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5785628795648228827885553 4339221596736171620914165)
                ·
                  refine ⟨406802024694016089460703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4339221596736171620914165 406802024694016089460703)
                  ·
                    rfl

theorem cell23_7130197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_7130197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130197 prefixEnd_7130197 := by exact prefixLift 7130197
  have htrace : WordTrace (prefixWord ++ tailWord_7130197) baseStart_7130197 baseEnd_7130197 := by
    simpa [prefixWord, tailWord_7130197, baseEnd_7130197] using wordTrace_append hprefix tailTrace_7130197
  have hstable : (prefixWord ++ tailWord_7130197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130197).length < 2 ^ (prefixWord ++ tailWord_7130197).sum := by decide
  have hdescent : baseEnd_7130197 < baseStart_7130197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130200 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7130200 : Nat := 118140960795 + 7130200 * 2 ^ 59
def prefixEnd_7130200 : Nat := 4983230072969 + 3 ^ 40 * 7130200 * 2
def baseEnd_7130200 : Nat := 3661219762688108293408813

theorem tailTrace_7130200 : CollatzResearch.WordTrace tailWord_7130200 prefixEnd_7130200 3661219762688108293408813 := by
  unfold tailWord_7130200
  simp only [CollatzResearch.WordTrace]
  refine ⟨130029879384255308027890027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173373172512340410703853369 130029879384255308027890027)
  ·
    refine ⟨195044819076382962041835041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130029879384255308027890027 195044819076382962041835041)
    ·
      refine ⟨146283614307287221531376281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195044819076382962041835041 146283614307287221531376281)
      ·
        refine ⟨109712710730465416148532211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146283614307287221531376281 109712710730465416148532211)
        ·
          refine ⟨164569066095698124222798317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109712710730465416148532211 164569066095698124222798317)
          ·
            refine ⟨61713399785886796583549369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164569066095698124222798317 61713399785886796583549369)
            ·
              refine ⟨46285049839415097437662027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61713399785886796583549369 46285049839415097437662027)
              ·
                refine ⟨69427574759122646156493041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46285049839415097437662027 69427574759122646156493041)
                ·
                  refine ⟨52070681069341984617369781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69427574759122646156493041 52070681069341984617369781)
                  ·
                    refine ⟨4881626350250811057878417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52070681069341984617369781 4881626350250811057878417)
                    ·
                      refine ⟨3661219762688108293408813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881626350250811057878417 3661219762688108293408813)
                      ·
                        rfl

theorem cell23_7130200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7130200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130200 prefixEnd_7130200 := by exact prefixLift 7130200
  have htrace : WordTrace (prefixWord ++ tailWord_7130200) baseStart_7130200 baseEnd_7130200 := by
    simpa [prefixWord, tailWord_7130200, baseEnd_7130200] using wordTrace_append hprefix tailTrace_7130200
  have hstable : (prefixWord ++ tailWord_7130200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130200).length < 2 ^ (prefixWord ++ tailWord_7130200).sum := by decide
  have hdescent : baseEnd_7130200 < baseStart_7130200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130243 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_7130243 : Nat := 118140960795 + 7130243 * 2 ^ 59
def prefixEnd_7130243 : Nat := 4983230072969 + 3 ^ 40 * 7130243 * 2
def baseEnd_7130243 : Nat := 3661241842356251625171115

theorem tailTrace_7130243 : CollatzResearch.WordTrace tailWord_7130243 prefixEnd_7130243 3661241842356251625171115 := by
  unfold tailWord_7130243
  simp only [CollatzResearch.WordTrace]
  refine ⟨260061327107354834399595383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173374218071569889599730255 260061327107354834399595383)
  ·
    refine ⟨390091990661032251599393075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260061327107354834399595383 390091990661032251599393075)
    ·
      refine ⟨585137985991548377399089613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390091990661032251599393075 585137985991548377399089613)
      ·
        refine ⟨219426744746830641524658605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585137985991548377399089613 219426744746830641524658605)
        ·
          refine ⟨82285029280061490571746977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219426744746830641524658605 82285029280061490571746977)
          ·
            refine ⟨61713771960046117928810233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82285029280061490571746977 61713771960046117928810233)
            ·
              refine ⟨46285328970034588446607675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61713771960046117928810233 46285328970034588446607675)
              ·
                refine ⟨69427993455051882669911513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46285328970034588446607675 69427993455051882669911513)
                ·
                  refine ⟨52070995091288912002433635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69427993455051882669911513 52070995091288912002433635)
                  ·
                    refine ⟨78106492636933368003650453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52070995091288912002433635 78106492636933368003650453)
                    ·
                      refine ⟨3661241842356251625171115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78106492636933368003650453 3661241842356251625171115)
                      ·
                        rfl

theorem cell23_7130243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_7130243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130243 prefixEnd_7130243 := by exact prefixLift 7130243
  have htrace : WordTrace (prefixWord ++ tailWord_7130243) baseStart_7130243 baseEnd_7130243 := by
    simpa [prefixWord, tailWord_7130243, baseEnd_7130243] using wordTrace_append hprefix tailTrace_7130243
  have hstable : (prefixWord ++ tailWord_7130243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130243).length < 2 ^ (prefixWord ++ tailWord_7130243).sum := by decide
  have hdescent : baseEnd_7130243 < baseStart_7130243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130274 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7130274 : Nat := 118140960795 + 7130274 * 2 ^ 59
def prefixEnd_7130274 : Nat := 4983230072969 + 3 ^ 40 * 7130274 * 2
def baseEnd_7130274 : Nat := 1220419253418847001294491

theorem tailTrace_7130274 : CollatzResearch.WordTrace tailWord_7130274 prefixEnd_7130274 1220419253418847001294491 := by
  unfold tailWord_7130274
  simp only [CollatzResearch.WordTrace]
  refine ⟨65015614442560631673493469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173374971846828351129315917 65015614442560631673493469)
  ·
    refine ⟨24380855415960236877560051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65015614442560631673493469 24380855415960236877560051)
    ·
      refine ⟨36571283123940355316340077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24380855415960236877560051 36571283123940355316340077)
      ·
        refine ⟨13714231171477633243627529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36571283123940355316340077 13714231171477633243627529)
        ·
          refine ⟨10285673378608224932720647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13714231171477633243627529 10285673378608224932720647)
          ·
            refine ⟨15428510067912337399080971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10285673378608224932720647 15428510067912337399080971)
            ·
              refine ⟨23142765101868506098621457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15428510067912337399080971 23142765101868506098621457)
              ·
                refine ⟨17357073826401379573966093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23142765101868506098621457 17357073826401379573966093)
                ·
                  refine ⟨6508902684900517340237285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17357073826401379573966093 6508902684900517340237285)
                  ·
                    refine ⟨1220419253418847001294491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6508902684900517340237285 1220419253418847001294491)
                    ·
                      rfl

theorem cell23_7130274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7130274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130274 prefixEnd_7130274 := by exact prefixLift 7130274
  have htrace : WordTrace (prefixWord ++ tailWord_7130274) baseStart_7130274 baseEnd_7130274 := by
    simpa [prefixWord, tailWord_7130274, baseEnd_7130274] using wordTrace_append hprefix tailTrace_7130274
  have hstable : (prefixWord ++ tailWord_7130274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130274).length < 2 ^ (prefixWord ++ tailWord_7130274).sum := by decide
  have hdescent : baseEnd_7130274 < baseStart_7130274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130304 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 6]
def baseStart_7130304 : Nat := 118140960795 + 7130304 * 2 ^ 59
def prefixEnd_7130304 : Nat := 4983230072969 + 3 ^ 40 * 7130304 * 2
def baseEnd_7130304 : Nat := 406808129408463987389815

theorem tailTrace_7130304 : CollatzResearch.WordTrace tailWord_7130304 prefixEnd_7130304 406808129408463987389815 := by
  unfold tailWord_7130304
  simp only [CollatzResearch.WordTrace]
  refine ⟨130031775980066920908782983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173375701306755894545043977 130031775980066920908782983)
  ·
    refine ⟨195047663970100381363174475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130031775980066920908782983 195047663970100381363174475)
    ·
      refine ⟨292571495955150572044761713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195047663970100381363174475 292571495955150572044761713)
      ·
        refine ⟨219428621966362929033571285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292571495955150572044761713 219428621966362929033571285)
        ·
          refine ⟨5142858327336631149224327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 219428621966362929033571285 5142858327336631149224327)
          ·
            refine ⟨7714287491004946723836491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142858327336631149224327 7714287491004946723836491)
            ·
              refine ⟨11571431236507420085754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714287491004946723836491 11571431236507420085754737)
              ·
                refine ⟨8678573427380565064316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11571431236507420085754737 8678573427380565064316053)
                ·
                  refine ⟨406808129408463987389815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8678573427380565064316053 406808129408463987389815)
                  ·
                    rfl

theorem cell23_7130304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_7130304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130304 prefixEnd_7130304 := by exact prefixLift 7130304
  have htrace : WordTrace (prefixWord ++ tailWord_7130304) baseStart_7130304 baseEnd_7130304 := by
    simpa [prefixWord, tailWord_7130304, baseEnd_7130304] using wordTrace_append hprefix tailTrace_7130304
  have hstable : (prefixWord ++ tailWord_7130304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130304).length < 2 ^ (prefixWord ++ tailWord_7130304).sum := by decide
  have hdescent : baseEnd_7130304 < baseStart_7130304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130314 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_7130314 : Nat := 118140960795 + 7130314 * 2 ^ 59
def prefixEnd_7130314 : Nat := 4983230072969 + 3 ^ 40 * 7130314 * 2
def baseEnd_7130314 : Nat := 3661278299482720847383289

theorem tailTrace_7130314 : CollatzResearch.WordTrace tailWord_7130314 prefixEnd_7130314 3661278299482720847383289 := by
  unfold tailWord_7130314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65015979172524403381357499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173375944460065075683619997 65015979172524403381357499)
  ·
    refine ⟨97523968758786605072036249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65015979172524403381357499 97523968758786605072036249)
    ·
      refine ⟨73142976569089953804027187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97523968758786605072036249 73142976569089953804027187)
      ·
        refine ⟨109714464853634930706040781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73142976569089953804027187 109714464853634930706040781)
        ·
          refine ⟨41142924320113099014765293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109714464853634930706040781 41142924320113099014765293)
          ·
            refine ⟨15428596620042412130536985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41142924320113099014765293 15428596620042412130536985)
            ·
              refine ⟨11571447465031809097902739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15428596620042412130536985 11571447465031809097902739)
              ·
                refine ⟨17357171197547713646854109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571447465031809097902739 17357171197547713646854109)
                ·
                  refine ⟨6508939199080392617570291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17357171197547713646854109 6508939199080392617570291)
                  ·
                    refine ⟨9763408798620588926355437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6508939199080392617570291 9763408798620588926355437)
                    ·
                      refine ⟨3661278299482720847383289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763408798620588926355437 3661278299482720847383289)
                      ·
                        rfl

theorem cell23_7130314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_7130314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130314 prefixEnd_7130314 := by exact prefixLift 7130314
  have htrace : WordTrace (prefixWord ++ tailWord_7130314) baseStart_7130314 baseEnd_7130314 := by
    simpa [prefixWord, tailWord_7130314, baseEnd_7130314] using wordTrace_append hprefix tailTrace_7130314
  have hstable : (prefixWord ++ tailWord_7130314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130314).length < 2 ^ (prefixWord ++ tailWord_7130314).sum := by decide
  have hdescent : baseEnd_7130314 < baseStart_7130314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130337 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_7130337 : Nat := 118140960795 + 7130337 * 2 ^ 59
def prefixEnd_7130337 : Nat := 4983230072969 + 3 ^ 40 * 7130337 * 2
def baseEnd_7130337 : Nat := 3661290109537774257395683

theorem tailTrace_7130337 : CollatzResearch.WordTrace tailWord_7130337 prefixEnd_7130337 3661290109537774257395683 := by
  unfold tailWord_7130337
  simp only [CollatzResearch.WordTrace]
  refine ⟨260064755569014288453517265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173376503712676192302344843 260064755569014288453517265)
  ·
    refine ⟨195048566676760716340137949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260064755569014288453517265 195048566676760716340137949)
    ·
      refine ⟨73143212503785268627551731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195048566676760716340137949 73143212503785268627551731)
      ·
        refine ⟨109714818755677902941327597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73143212503785268627551731 109714818755677902941327597)
        ·
          refine ⟨41143057033379213602997849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109714818755677902941327597 41143057033379213602997849)
          ·
            refine ⟨30857292775034410202248387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41143057033379213602997849 30857292775034410202248387)
            ·
              refine ⟨46285939162551615303372581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30857292775034410202248387 46285939162551615303372581)
              ·
                refine ⟨8678613592978427869382359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46285939162551615303372581 8678613592978427869382359)
                ·
                  refine ⟨13017920389467641804073539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8678613592978427869382359 13017920389467641804073539)
                  ·
                    refine ⟨19526880584201462706110309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13017920389467641804073539 19526880584201462706110309)
                    ·
                      refine ⟨3661290109537774257395683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19526880584201462706110309 3661290109537774257395683)
                      ·
                        rfl

theorem cell23_7130337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_7130337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130337 prefixEnd_7130337 := by exact prefixLift 7130337
  have htrace : WordTrace (prefixWord ++ tailWord_7130337) baseStart_7130337 baseEnd_7130337 := by
    simpa [prefixWord, tailWord_7130337, baseEnd_7130337] using wordTrace_append hprefix tailTrace_7130337
  have hstable : (prefixWord ++ tailWord_7130337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130337).length < 2 ^ (prefixWord ++ tailWord_7130337).sum := by decide
  have hdescent : baseEnd_7130337 < baseStart_7130337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130371 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 3, 2, 2]
def baseStart_7130371 : Nat := 118140960795 + 7130371 * 2 ^ 59
def prefixEnd_7130371 : Nat := 4983230072969 + 3 ^ 40 * 7130371 * 2
def baseEnd_7130371 : Nat := 3661307567880027124370527

theorem tailTrace_7130371 : CollatzResearch.WordTrace tailWord_7130371 prefixEnd_7130371 3661307567880027124370527 := by
  unfold tailWord_7130371
  simp only [CollatzResearch.WordTrace]
  refine ⟨260065995650891112260254967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173377330433927408173503311 260065995650891112260254967)
  ·
    refine ⟨390098993476336668390382451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260065995650891112260254967 390098993476336668390382451)
    ·
      refine ⟨585148490214505002585573677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390098993476336668390382451 585148490214505002585573677)
      ·
        refine ⟨219430683830439375969590129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585148490214505002585573677 219430683830439375969590129)
        ·
          refine ⟨164573012872829531977192597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219430683830439375969590129 164573012872829531977192597)
          ·
            refine ⟨7714359978413884311430903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164573012872829531977192597 7714359978413884311430903)
            ·
              refine ⟨11571539967620826467146355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714359978413884311430903 11571539967620826467146355)
              ·
                refine ⟨17357309951431239700719533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571539967620826467146355 17357309951431239700719533)
                ·
                  refine ⟨6508991231786714887769825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17357309951431239700719533 6508991231786714887769825)
                  ·
                    refine ⟨4881743423840036165827369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6508991231786714887769825 4881743423840036165827369)
                    ·
                      refine ⟨3661307567880027124370527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881743423840036165827369 3661307567880027124370527)
                      ·
                        rfl

theorem cell23_7130371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_7130371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130371 prefixEnd_7130371 := by exact prefixLift 7130371
  have htrace : WordTrace (prefixWord ++ tailWord_7130371) baseStart_7130371 baseEnd_7130371 := by
    simpa [prefixWord, tailWord_7130371, baseEnd_7130371] using wordTrace_append hprefix tailTrace_7130371
  have hstable : (prefixWord ++ tailWord_7130371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130371).length < 2 ^ (prefixWord ++ tailWord_7130371).sum := by decide
  have hdescent : baseEnd_7130371 < baseStart_7130371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130421 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_7130421 : Nat := 118140960795 + 7130421 * 2 ^ 59
def prefixEnd_7130421 : Nat := 4983230072969 + 3 ^ 40 * 7130421 * 2
def baseEnd_7130421 : Nat := 3661333241912751928745297

theorem tailTrace_7130421 : CollatzResearch.WordTrace tailWord_7130421 prefixEnd_7130421 3661333241912751928745297 := by
  unfold tailWord_7130421
  simp only [CollatzResearch.WordTrace]
  refine ⟨260067819300709970799575117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173378546200473313866383411 260067819300709970799575117)
  ·
    refine ⟨97525432237766239049840669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260067819300709970799575117 97525432237766239049840669)
    ·
      refine ⟨36572037089162339643690251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97525432237766239049840669 36572037089162339643690251)
      ·
        refine ⟨54858055633743509465535377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36572037089162339643690251 54858055633743509465535377)
        ·
          refine ⟨41143541725307632099151533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54858055633743509465535377 41143541725307632099151533)
          ·
            refine ⟨15428828146990362037181825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41143541725307632099151533 15428828146990362037181825)
            ·
              refine ⟨11571621110242771527886369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15428828146990362037181825 11571621110242771527886369)
              ·
                refine ⟨8678715832682078645914777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11571621110242771527886369 8678715832682078645914777)
                ·
                  refine ⟨6509036874511558984436083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8678715832682078645914777 6509036874511558984436083)
                  ·
                    refine ⟨9763555311767338476654125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509036874511558984436083 9763555311767338476654125)
                    ·
                      refine ⟨3661333241912751928745297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763555311767338476654125 3661333241912751928745297)
                      ·
                        rfl

theorem cell23_7130421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_7130421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130421 prefixEnd_7130421 := by exact prefixLift 7130421
  have htrace : WordTrace (prefixWord ++ tailWord_7130421) baseStart_7130421 baseEnd_7130421 := by
    simpa [prefixWord, tailWord_7130421, baseEnd_7130421] using wordTrace_append hprefix tailTrace_7130421
  have hstable : (prefixWord ++ tailWord_7130421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130421).length < 2 ^ (prefixWord ++ tailWord_7130421).sum := by decide
  have hdescent : baseEnd_7130421 < baseStart_7130421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130422 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7130422 : Nat := 118140960795 + 7130422 * 2 ^ 59
def prefixEnd_7130422 : Nat := 4983230072969 + 3 ^ 40 * 7130422 * 2
def baseEnd_7130422 : Nat := 3661333755393406424832793

theorem tailTrace_7130422 : CollatzResearch.WordTrace tailWord_7130422 prefixEnd_7130422 3661333755393406424832793 := by
  unfold tailWord_7130422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254240985856646748147595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173378570515804231980241013 16254240985856646748147595)
  ·
    refine ⟨24381361478784970122221393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16254240985856646748147595 24381361478784970122221393)
    ·
      refine ⟨18286021109088727591666045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24381361478784970122221393 18286021109088727591666045)
      ·
        refine ⟨6857257915908272846874767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18286021109088727591666045 6857257915908272846874767)
        ·
          refine ⟨10285886873862409270312151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6857257915908272846874767 10285886873862409270312151)
          ·
            refine ⟨15428830310793613905468227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10285886873862409270312151 15428830310793613905468227)
            ·
              refine ⟨23143245466190420858202341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15428830310793613905468227 23143245466190420858202341)
              ·
                refine ⟨4339358524910703910912939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23143245466190420858202341 4339358524910703910912939)
                ·
                  refine ⟨6509037787366055866369409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339358524910703910912939 6509037787366055866369409)
                  ·
                    refine ⟨4881778340524541899777057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509037787366055866369409 4881778340524541899777057)
                    ·
                      refine ⟨3661333755393406424832793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881778340524541899777057 3661333755393406424832793)
                      ·
                        rfl

theorem cell23_7130422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7130422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130422 prefixEnd_7130422 := by exact prefixLift 7130422
  have htrace : WordTrace (prefixWord ++ tailWord_7130422) baseStart_7130422 baseEnd_7130422 := by
    simpa [prefixWord, tailWord_7130422, baseEnd_7130422] using wordTrace_append hprefix tailTrace_7130422
  have hstable : (prefixWord ++ tailWord_7130422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130422).length < 2 ^ (prefixWord ++ tailWord_7130422).sum := by decide
  have hdescent : baseEnd_7130422 < baseStart_7130422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130444 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7130444 : Nat := 118140960795 + 7130444 * 2 ^ 59
def prefixEnd_7130444 : Nat := 4983230072969 + 3 ^ 40 * 7130444 * 2
def baseEnd_7130444 : Nat := 3661345051967805338757691

theorem tailTrace_7130444 : CollatzResearch.WordTrace tailWord_7130444 prefixEnd_7130444 3661345051967805338757691 := by
  unfold tailWord_7130444
  simp only [CollatzResearch.WordTrace]
  refine ⟨130034329089813322863831193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173379105453084430485108257 130034329089813322863831193)
  ·
    refine ⟨97525746817359992147873395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130034329089813322863831193 97525746817359992147873395)
    ·
      refine ⟨146288620226039988221810093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97525746817359992147873395 146288620226039988221810093)
      ·
        refine ⟨54858232584764995583178785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146288620226039988221810093 54858232584764995583178785)
        ·
          refine ⟨41143674438573746687384089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54858232584764995583178785 41143674438573746687384089)
          ·
            refine ⟨30857755828930310015538067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41143674438573746687384089 30857755828930310015538067)
            ·
              refine ⟨46286633743395465023307101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30857755828930310015538067 46286633743395465023307101)
              ·
                refine ⟨17357487653773299383740163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46286633743395465023307101 17357487653773299383740163)
                ·
                  refine ⟨26036231480659949075610245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17357487653773299383740163 26036231480659949075610245)
                  ·
                    refine ⟨4881793402623740451676921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26036231480659949075610245 4881793402623740451676921)
                    ·
                      refine ⟨3661345051967805338757691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881793402623740451676921 3661345051967805338757691)
                      ·
                        rfl

theorem cell23_7130444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7130444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130444 prefixEnd_7130444 := by exact prefixLift 7130444
  have htrace : WordTrace (prefixWord ++ tailWord_7130444) baseStart_7130444 baseEnd_7130444 := by
    simpa [prefixWord, tailWord_7130444, baseEnd_7130444] using wordTrace_append hprefix tailTrace_7130444
  have hstable : (prefixWord ++ tailWord_7130444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130444).length < 2 ^ (prefixWord ++ tailWord_7130444).sum := by decide
  have hdescent : baseEnd_7130444 < baseStart_7130444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130517 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7130517 : Nat := 118140960795 + 7130517 * 2 ^ 59
def prefixEnd_7130517 : Nat := 4983230072969 + 3 ^ 40 * 7130517 * 2
def baseEnd_7130517 : Nat := 3661382536055583553144855

theorem tailTrace_7130517 : CollatzResearch.WordTrace tailWord_7130517 prefixEnd_7130517 3661382536055583553144855 := by
  unfold tailWord_7130517
  simp only [CollatzResearch.WordTrace]
  refine ⟨260071320708362179195069805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173380880472241452796713203 260071320708362179195069805)
  ·
    refine ⟨97526745265635817198151177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260071320708362179195069805 97526745265635817198151177)
    ·
      refine ⟨73145058949226862898613383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97526745265635817198151177 73145058949226862898613383)
      ·
        refine ⟨109717588423840294347920075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73145058949226862898613383 109717588423840294347920075)
        ·
          refine ⟨164576382635760441521880113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109717588423840294347920075 164576382635760441521880113)
          ·
            refine ⟨123432286976820331141410085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164576382635760441521880113 123432286976820331141410085)
            ·
              refine ⟨23143553808153812089014391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123432286976820331141410085 23143553808153812089014391)
              ·
                refine ⟨34715330712230718133521587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23143553808153812089014391 34715330712230718133521587)
                ·
                  refine ⟨52072996068346077200282381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34715330712230718133521587 52072996068346077200282381)
                  ·
                    refine ⟨19527373525629778950105893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52072996068346077200282381 19527373525629778950105893)
                    ·
                      refine ⟨3661382536055583553144855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19527373525629778950105893 3661382536055583553144855)
                      ·
                        rfl

theorem cell23_7130517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7130517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130517 prefixEnd_7130517 := by exact prefixLift 7130517
  have htrace : WordTrace (prefixWord ++ tailWord_7130517) baseStart_7130517 baseEnd_7130517 := by
    simpa [prefixWord, tailWord_7130517, baseEnd_7130517] using wordTrace_append hprefix tailTrace_7130517
  have hstable : (prefixWord ++ tailWord_7130517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130517).length < 2 ^ (prefixWord ++ tailWord_7130517).sum := by decide
  have hdescent : baseEnd_7130517 < baseStart_7130517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130595 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 1, 4]
def baseStart_7130595 : Nat := 118140960795 + 7130595 * 2 ^ 59
def prefixEnd_7130595 : Nat := 4983230072969 + 3 ^ 40 * 7130595 * 2
def baseEnd_7130595 : Nat := 1220474195848878082656499

theorem tailTrace_7130595 : CollatzResearch.WordTrace tailWord_7130595 prefixEnd_7130595 1220474195848878082656499 := by
  unfold tailWord_7130595
  simp only [CollatzResearch.WordTrace]
  refine ⟨260074165602079598516409239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173382777068053065677606159 260074165602079598516409239)
  ·
    refine ⟨390111248403119397774613859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260074165602079598516409239 390111248403119397774613859)
    ·
      refine ⟨585166872604679096661920789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390111248403119397774613859 585166872604679096661920789)
      ·
        refine ⟨27429697153344332656027537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 585166872604679096661920789 27429697153344332656027537)
        ·
          refine ⟨20572272865008249492020653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27429697153344332656027537 20572272865008249492020653)
          ·
            refine ⟨7714602324378093559507745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20572272865008249492020653 7714602324378093559507745)
            ·
              refine ⟨5785951743283570169630809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7714602324378093559507745 5785951743283570169630809)
              ·
                refine ⟨4339463807462677627223107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5785951743283570169630809 4339463807462677627223107)
                ·
                  refine ⟨6509195711194016440834661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339463807462677627223107 6509195711194016440834661)
                  ·
                    refine ⟨1220474195848878082656499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509195711194016440834661 1220474195848878082656499)
                    ·
                      rfl

theorem cell23_7130595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 4].length) (baseStart_7130595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130595 prefixEnd_7130595 := by exact prefixLift 7130595
  have htrace : WordTrace (prefixWord ++ tailWord_7130595) baseStart_7130595 baseEnd_7130595 := by
    simpa [prefixWord, tailWord_7130595, baseEnd_7130595] using wordTrace_append hprefix tailTrace_7130595
  have hstable : (prefixWord ++ tailWord_7130595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130595).length < 2 ^ (prefixWord ++ tailWord_7130595).sum := by decide
  have hdescent : baseEnd_7130595 < baseStart_7130595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130622 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7130622 : Nat := 118140960795 + 7130622 * 2 ^ 59
def prefixEnd_7130622 : Nat := 4983230072969 + 3 ^ 40 * 7130622 * 2
def baseEnd_7130622 : Nat := 3661436451524305642331873

theorem tailTrace_7130622 : CollatzResearch.WordTrace tailWord_7130622 prefixEnd_7130622 3661436451524305642331873 := by
  unfold tailWord_7130622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32509393796622722765955265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173383433581987854751761413 32509393796622722765955265)
  ·
    refine ⟨24382045347467042074466449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32509393796622722765955265 24382045347467042074466449)
    ·
      refine ⟨18286534010600281555849837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24382045347467042074466449 18286534010600281555849837)
      ·
        refine ⟨6857450253975105583443689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18286534010600281555849837 6857450253975105583443689)
        ·
          refine ⟨5143087690481329187582767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857450253975105583443689 5143087690481329187582767)
          ·
            refine ⟨7714631535721993781374151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143087690481329187582767 7714631535721993781374151)
            ·
              refine ⟨11571947303582990672061227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714631535721993781374151 11571947303582990672061227)
              ·
                refine ⟨17357920955374486008091841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571947303582990672061227 17357920955374486008091841)
                ·
                  refine ⟨13018440716530864506068881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17357920955374486008091841 13018440716530864506068881)
                  ·
                    refine ⟨9763830537398148379551661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13018440716530864506068881 9763830537398148379551661)
                    ·
                      refine ⟨3661436451524305642331873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763830537398148379551661 3661436451524305642331873)
                      ·
                        rfl

theorem cell23_7130622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7130622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130622 prefixEnd_7130622 := by exact prefixLift 7130622
  have htrace : WordTrace (prefixWord ++ tailWord_7130622) baseStart_7130622 baseEnd_7130622 := by
    simpa [prefixWord, tailWord_7130622, baseEnd_7130622] using wordTrace_append hprefix tailTrace_7130622
  have hstable : (prefixWord ++ tailWord_7130622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130622).length < 2 ^ (prefixWord ++ tailWord_7130622).sum := by decide
  have hdescent : baseEnd_7130622 < baseStart_7130622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130627 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_7130627 : Nat := 118140960795 + 7130627 * 2 ^ 59
def prefixEnd_7130627 : Nat := 4983230072969 + 3 ^ 40 * 7130627 * 2
def baseEnd_7130627 : Nat := 3661439018927578122769349

theorem tailTrace_7130627 : CollatzResearch.WordTrace tailWord_7130627 prefixEnd_7130627 3661439018927578122769349 := by
  unfold tailWord_7130627
  simp only [CollatzResearch.WordTrace]
  refine ⟨260075332737963667981574135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173383555158642445321049423 260075332737963667981574135)
  ·
    refine ⟨390112999106945501972361203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260075332737963667981574135 390112999106945501972361203)
    ·
      refine ⟨585169498660418252958541805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390112999106945501972361203 585169498660418252958541805)
      ·
        refine ⟨219438561997656844859453177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585169498660418252958541805 219438561997656844859453177)
        ·
          refine ⟨164578921498242633644589883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219438561997656844859453177 164578921498242633644589883)
          ·
            refine ⟨246868382247363950466884825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164578921498242633644589883 246868382247363950466884825)
            ·
              refine ⟨185151286685522962850163619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246868382247363950466884825 185151286685522962850163619)
              ·
                refine ⟨277726930028284444275245429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185151286685522962850163619 277726930028284444275245429)
                ·
                  refine ⟨26036899690151666650804259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277726930028284444275245429 26036899690151666650804259)
                  ·
                    refine ⟨39055349535227499976206389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26036899690151666650804259 39055349535227499976206389)
                    ·
                      refine ⟨3661439018927578122769349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39055349535227499976206389 3661439018927578122769349)
                      ·
                        rfl

theorem cell23_7130627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_7130627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130627 prefixEnd_7130627 := by exact prefixLift 7130627
  have htrace : WordTrace (prefixWord ++ tailWord_7130627) baseStart_7130627 baseEnd_7130627 := by
    simpa [prefixWord, tailWord_7130627, baseEnd_7130627] using wordTrace_append hprefix tailTrace_7130627
  have hstable : (prefixWord ++ tailWord_7130627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130627).length < 2 ^ (prefixWord ++ tailWord_7130627).sum := by decide
  have hdescent : baseEnd_7130627 < baseStart_7130627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130628 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7130628 : Nat := 118140960795 + 7130628 * 2 ^ 59
def prefixEnd_7130628 : Nat := 4983230072969 + 3 ^ 40 * 7130628 * 2
def baseEnd_7130628 : Nat := 3661439532408232618856845

theorem tailTrace_7130628 : CollatzResearch.WordTrace tailWord_7130628 prefixEnd_7130628 3661439532408232618856845 := by
  unfold tailWord_7130628
  simp only [CollatzResearch.WordTrace]
  refine ⟨130037684605480022576180269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173383579473973363434907025 130037684605480022576180269)
  ·
    refine ⟨48764131727055008466067601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130037684605480022576180269 48764131727055008466067601)
    ·
      refine ⟨36573098795291256349550701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48764131727055008466067601 36573098795291256349550701)
      ·
        refine ⟨13714912048234221131081513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36573098795291256349550701 13714912048234221131081513)
        ·
          refine ⟨10286184036175665848311135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13714912048234221131081513 10286184036175665848311135)
          ·
            refine ⟨15429276054263498772466703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286184036175665848311135 15429276054263498772466703)
            ·
              refine ⟨23143914081395248158700055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15429276054263498772466703 23143914081395248158700055)
              ·
                refine ⟨34715871122092872238050083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23143914081395248158700055 34715871122092872238050083)
                ·
                  refine ⟨52073806683139308357075125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34715871122092872238050083 52073806683139308357075125)
                  ·
                    refine ⟨4881919376544310158475793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52073806683139308357075125 4881919376544310158475793)
                    ·
                      refine ⟨3661439532408232618856845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881919376544310158475793 3661439532408232618856845)
                      ·
                        rfl

theorem cell23_7130628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7130628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130628 prefixEnd_7130628 := by exact prefixLift 7130628
  have htrace : WordTrace (prefixWord ++ tailWord_7130628) baseStart_7130628 baseEnd_7130628 := by
    simpa [prefixWord, tailWord_7130628, baseEnd_7130628] using wordTrace_append hprefix tailTrace_7130628
  have hstable : (prefixWord ++ tailWord_7130628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130628).length < 2 ^ (prefixWord ++ tailWord_7130628).sum := by decide
  have hdescent : baseEnd_7130628 < baseStart_7130628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130634 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_7130634 : Nat := 118140960795 + 7130634 * 2 ^ 59
def prefixEnd_7130634 : Nat := 4983230072969 + 3 ^ 40 * 7130634 * 2
def baseEnd_7130634 : Nat := 1220480871097386531793939

theorem tailTrace_7130634 : CollatzResearch.WordTrace tailWord_7130634 prefixEnd_7130634 1220480871097386531793939 := by
  unfold tailWord_7130634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65018897012234577044269739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173383725365958872118052637 65018897012234577044269739)
  ·
    refine ⟨97528345518351865566404609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65018897012234577044269739 97528345518351865566404609)
    ·
      refine ⟨73146259138763899174803457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97528345518351865566404609 73146259138763899174803457)
      ·
        refine ⟨54859694354072924381102593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73146259138763899174803457 54859694354072924381102593)
        ·
          refine ⟨41144770765554693285826945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54859694354072924381102593 41144770765554693285826945)
          ·
            refine ⟨30858578074166019964370209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41144770765554693285826945 30858578074166019964370209)
            ·
              refine ⟨23143933555624514973277657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30858578074166019964370209 23143933555624514973277657)
              ·
                refine ⟨17357950166718386229958243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23143933555624514973277657 17357950166718386229958243)
                ·
                  refine ⟨26036925250077579344937365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17357950166718386229958243 26036925250077579344937365)
                  ·
                    refine ⟨1220480871097386531793939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26036925250077579344937365 1220480871097386531793939)
                    ·
                      rfl

theorem cell23_7130634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_7130634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130634 prefixEnd_7130634 := by exact prefixLift 7130634
  have htrace : WordTrace (prefixWord ++ tailWord_7130634) baseStart_7130634 baseEnd_7130634 := by
    simpa [prefixWord, tailWord_7130634, baseEnd_7130634] using wordTrace_append hprefix tailTrace_7130634
  have hstable : (prefixWord ++ tailWord_7130634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130634).length < 2 ^ (prefixWord ++ tailWord_7130634).sum := by decide
  have hdescent : baseEnd_7130634 < baseStart_7130634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130635 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 1, 1, 3]
def baseStart_7130635 : Nat := 118140960795 + 7130635 * 2 ^ 59
def prefixEnd_7130635 : Nat := 4983230072969 + 3 ^ 40 * 7130635 * 2
def baseEnd_7130635 : Nat := 3661443126772814091469313

theorem tailTrace_7130635 : CollatzResearch.WordTrace tailWord_7130635 prefixEnd_7130635 3661443126772814091469313 := by
  unfold tailWord_7130635
  simp only [CollatzResearch.WordTrace]
  refine ⟨260075624521934685347865359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173383749681289790231910239 260075624521934685347865359)
  ·
    refine ⟨390113436782902028021798039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260075624521934685347865359 390113436782902028021798039)
    ·
      refine ⟨585170155174353042032697059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390113436782902028021798039 585170155174353042032697059)
      ·
        refine ⟨877755232761529563049045589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585170155174353042032697059 877755232761529563049045589)
        ·
          refine ⟨10286194133924174566981003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 877755232761529563049045589 10286194133924174566981003)
          ·
            refine ⟨15429291200886261850471505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286194133924174566981003 15429291200886261850471505)
            ·
              refine ⟨11571968400664696387853629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15429291200886261850471505 11571968400664696387853629)
              ·
                refine ⟨4339488150249261145445111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11571968400664696387853629 4339488150249261145445111)
                ·
                  refine ⟨6509232225373891718167667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339488150249261145445111 6509232225373891718167667)
                  ·
                    refine ⟨9763848338060837577251501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509232225373891718167667 9763848338060837577251501)
                    ·
                      refine ⟨3661443126772814091469313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763848338060837577251501 3661443126772814091469313)
                      ·
                        rfl

theorem cell23_7130635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 1, 3].length) (baseStart_7130635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130635 prefixEnd_7130635 := by exact prefixLift 7130635
  have htrace : WordTrace (prefixWord ++ tailWord_7130635) baseStart_7130635 baseEnd_7130635 := by
    simpa [prefixWord, tailWord_7130635, baseEnd_7130635] using wordTrace_append hprefix tailTrace_7130635
  have hstable : (prefixWord ++ tailWord_7130635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130635).length < 2 ^ (prefixWord ++ tailWord_7130635).sum := by decide
  have hdescent : baseEnd_7130635 < baseStart_7130635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130641 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_7130641 : Nat := 118140960795 + 7130641 * 2 ^ 59
def prefixEnd_7130641 : Nat := 4983230072969 + 3 ^ 40 * 7130641 * 2
def baseEnd_7130641 : Nat := 3661446207656741067994285

theorem tailTrace_7130641 : CollatzResearch.WordTrace tailWord_7130641 prefixEnd_7130641 3661446207656741067994285 := by
  unfold tailWord_7130641
  simp only [CollatzResearch.WordTrace]
  refine ⟨260075843359912948372583777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173383895573275298915055851 260075843359912948372583777)
  ·
    refine ⟨195056882519934711279437833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260075843359912948372583777 195056882519934711279437833)
    ·
      refine ⟨146292661889951033459578375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195056882519934711279437833 146292661889951033459578375)
      ·
        refine ⟨219438992834926550189367563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146292661889951033459578375 219438992834926550189367563)
        ·
          refine ⟨329158489252389825284051345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219438992834926550189367563 329158489252389825284051345)
          ·
            refine ⟨246868866939292368963038509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329158489252389825284051345 246868866939292368963038509)
            ·
              refine ⟨92575825102234638361139441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246868866939292368963038509 92575825102234638361139441)
              ·
                refine ⟨69431868826675978770854581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92575825102234638361139441 69431868826675978770854581)
                ·
                  refine ⟨6509237702500873009767617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69431868826675978770854581 6509237702500873009767617)
                  ·
                    refine ⟨4881928276875654757325713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509237702500873009767617 4881928276875654757325713)
                    ·
                      refine ⟨3661446207656741067994285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881928276875654757325713 3661446207656741067994285)
                      ·
                        rfl

theorem cell23_7130641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_7130641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130641 prefixEnd_7130641 := by exact prefixLift 7130641
  have htrace : WordTrace (prefixWord ++ tailWord_7130641) baseStart_7130641 baseEnd_7130641 := by
    simpa [prefixWord, tailWord_7130641, baseEnd_7130641] using wordTrace_append hprefix tailTrace_7130641
  have hstable : (prefixWord ++ tailWord_7130641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130641).length < 2 ^ (prefixWord ++ tailWord_7130641).sum := by decide
  have hdescent : baseEnd_7130641 < baseStart_7130641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130658 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_7130658 : Nat := 118140960795 + 7130658 * 2 ^ 59
def prefixEnd_7130658 : Nat := 4983230072969 + 3 ^ 40 * 7130658 * 2
def baseEnd_7130658 : Nat := 3661454936827867501481707

theorem tailTrace_7130658 : CollatzResearch.WordTrace tailWord_7130658 prefixEnd_7130658 3661454936827867501481707 := by
  unfold tailWord_7130658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65019115850212840068988157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173384308933900906850635085 65019115850212840068988157)
  ·
    refine ⟨24382168443829815025870559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65019115850212840068988157 24382168443829815025870559)
    ·
      refine ⟨36573252665744722538805839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24382168443829815025870559 36573252665744722538805839)
      ·
        refine ⟨54859878998617083808208759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36573252665744722538805839 54859878998617083808208759)
        ·
          refine ⟨82289818497925625712313139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54859878998617083808208759 82289818497925625712313139)
          ·
            refine ⟨123434727746888438568469709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82289818497925625712313139 123434727746888438568469709)
            ·
              refine ⟨46288022905083164463176141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123434727746888438568469709 46288022905083164463176141)
              ·
                refine ⟨17358008589406186673691053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46288022905083164463176141 17358008589406186673691053)
                ·
                  refine ⟨6509253221027320002634145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17358008589406186673691053 6509253221027320002634145)
                  ·
                    refine ⟨4881939915770490001975609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509253221027320002634145 4881939915770490001975609)
                    ·
                      refine ⟨3661454936827867501481707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4881939915770490001975609 3661454936827867501481707)
                      ·
                        rfl

theorem cell23_7130658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_7130658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130658 prefixEnd_7130658 := by exact prefixLift 7130658
  have htrace : WordTrace (prefixWord ++ tailWord_7130658) baseStart_7130658 baseEnd_7130658 := by
    simpa [prefixWord, tailWord_7130658, baseEnd_7130658] using wordTrace_append hprefix tailTrace_7130658
  have hstable : (prefixWord ++ tailWord_7130658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130658).length < 2 ^ (prefixWord ++ tailWord_7130658).sum := by decide
  have hdescent : baseEnd_7130658 < baseStart_7130658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130681 : List Nat := [1, 2, 1, 5, 1, 4, 2, 7]
def baseStart_7130681 : Nat := 118140960795 + 7130681 * 2 ^ 59
def prefixEnd_7130681 : Nat := 4983230072969 + 3 ^ 40 * 7130681 * 2
def baseEnd_7130681 : Nat := 135609879514182255981263

theorem tailTrace_7130681 : CollatzResearch.WordTrace tailWord_7130681 prefixEnd_7130681 135609879514182255981263 := by
  unfold tailWord_7130681
  simp only [CollatzResearch.WordTrace]
  refine ⟨260077302279768035204039897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173384868186512023469359931 260077302279768035204039897)
  ·
    refine ⟨195057976709826026403029923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260077302279768035204039897 195057976709826026403029923)
    ·
      refine ⟨292586965064739039604544885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195057976709826026403029923 292586965064739039604544885)
      ·
        refine ⟨27430027974819284962926083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292586965064739039604544885 27430027974819284962926083)
        ·
          refine ⟨41145041962228927444389125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27430027974819284962926083 41145041962228927444389125)
          ·
            refine ⟨7714695367917923895822961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41145041962228927444389125 7714695367917923895822961)
            ·
              refine ⟨5786021525938442921867221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7714695367917923895822961 5786021525938442921867221)
              ·
                refine ⟨135609879514182255981263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5786021525938442921867221 135609879514182255981263)
                ·
                  rfl

theorem cell23_7130681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 7].length) (baseStart_7130681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130681 prefixEnd_7130681 := by exact prefixLift 7130681
  have htrace : WordTrace (prefixWord ++ tailWord_7130681) baseStart_7130681 baseEnd_7130681 := by
    simpa [prefixWord, tailWord_7130681, baseEnd_7130681] using wordTrace_append hprefix tailTrace_7130681
  have hstable : (prefixWord ++ tailWord_7130681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130681).length < 2 ^ (prefixWord ++ tailWord_7130681).sum := by decide
  have hdescent : baseEnd_7130681 < baseStart_7130681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130697 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_7130697 : Nat := 118140960795 + 7130697 * 2 ^ 59
def prefixEnd_7130697 : Nat := 4983230072969 + 3 ^ 40 * 7130697 * 2
def baseEnd_7130697 : Nat := 3661474962573392848894027

theorem tailTrace_7130697 : CollatzResearch.WordTrace tailWord_7130697 prefixEnd_7130697 3661474962573392848894027 := by
  unfold tailWord_7130697
  simp only [CollatzResearch.WordTrace]
  refine ⟨260077885847710069936622345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173385257231806713291081563 260077885847710069936622345)
  ·
    refine ⟨195058414385782552452466759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260077885847710069936622345 195058414385782552452466759)
    ·
      refine ⟨292587621578673828678700139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195058414385782552452466759 292587621578673828678700139)
      ·
        refine ⟨438881432368010743018050209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292587621578673828678700139 438881432368010743018050209)
        ·
          refine ⟨329161074276008057263537657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438881432368010743018050209 329161074276008057263537657)
          ·
            refine ⟨246870805707006042947653243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329161074276008057263537657 246870805707006042947653243)
            ·
              refine ⟨370306208560509064421479865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246870805707006042947653243 370306208560509064421479865)
              ·
                refine ⟨277729656420381798316109899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370306208560509064421479865 277729656420381798316109899)
                ·
                  refine ⟨416594484630572697474164849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277729656420381798316109899 416594484630572697474164849)
                  ·
                    refine ⟨312445863472929523105623637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416594484630572697474164849 312445863472929523105623637)
                    ·
                      refine ⟨3661474962573392848894027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 312445863472929523105623637 3661474962573392848894027)
                      ·
                        rfl

theorem cell23_7130697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_7130697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130697 prefixEnd_7130697 := by exact prefixLift 7130697
  have htrace : WordTrace (prefixWord ++ tailWord_7130697) baseStart_7130697 baseEnd_7130697 := by
    simpa [prefixWord, tailWord_7130697, baseEnd_7130697] using wordTrace_append hprefix tailTrace_7130697
  have hstable : (prefixWord ++ tailWord_7130697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130697).length < 2 ^ (prefixWord ++ tailWord_7130697).sum := by decide
  have hdescent : baseEnd_7130697 < baseStart_7130697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130707 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 8]
def baseStart_7130707 : Nat := 118140960795 + 7130707 * 2 ^ 59
def prefixEnd_7130707 : Nat := 4983230072969 + 3 ^ 40 * 7130707 * 2
def baseEnd_7130707 : Nat := 1220493365793312603256327

theorem tailTrace_7130707 : CollatzResearch.WordTrace tailWord_7130707 prefixEnd_7130707 1220493365793312603256327 := by
  unfold tailWord_7130707
  simp only [CollatzResearch.WordTrace]
  refine ⟨260078250577673841644486375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173385500385115894429657583 260078250577673841644486375)
  ·
    refine ⟨390117375866510762466729563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260078250577673841644486375 390117375866510762466729563)
    ·
      refine ⟨585176063799766143700094345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390117375866510762466729563 585176063799766143700094345)
      ·
        refine ⟨438882047849824607775070759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585176063799766143700094345 438882047849824607775070759)
        ·
          refine ⟨658323071774736911662606139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438882047849824607775070759 658323071774736911662606139)
          ·
            refine ⟨987484607662105367493909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658323071774736911662606139 987484607662105367493909209)
            ·
              refine ⟨740613455746579025620431907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987484607662105367493909209 740613455746579025620431907)
              ·
                refine ⟨1110920183619868538430647861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740613455746579025620431907 1110920183619868538430647861)
                ·
                  refine ⟨104148767214362675477873237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110920183619868538430647861 104148767214362675477873237)
                  ·
                    refine ⟨1220493365793312603256327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104148767214362675477873237 1220493365793312603256327)
                    ·
                      rfl

theorem cell23_7130707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_7130707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130707 prefixEnd_7130707 := by exact prefixLift 7130707
  have htrace : WordTrace (prefixWord ++ tailWord_7130707) baseStart_7130707 baseEnd_7130707 := by
    simpa [prefixWord, tailWord_7130707, baseEnd_7130707] using wordTrace_append hprefix tailTrace_7130707
  have hstable : (prefixWord ++ tailWord_7130707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130707).length < 2 ^ (prefixWord ++ tailWord_7130707).sum := by decide
  have hdescent : baseEnd_7130707 < baseStart_7130707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130708 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_7130708 : Nat := 118140960795 + 7130708 * 2 ^ 59
def prefixEnd_7130708 : Nat := 4983230072969 + 3 ^ 40 * 7130708 * 2
def baseEnd_7130708 : Nat := 3661480610860592305856477

theorem tailTrace_7130708 : CollatzResearch.WordTrace tailWord_7130708 prefixEnd_7130708 3661480610860592305856477 := by
  unfold tailWord_7130708
  simp only [CollatzResearch.WordTrace]
  refine ⟨130039143525335109407636389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173385524700446812543515185 130039143525335109407636389)
  ·
    refine ⟨24382339411000333013931823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130039143525335109407636389 24382339411000333013931823)
    ·
      refine ⟨36573509116500499520897735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24382339411000333013931823 36573509116500499520897735)
      ·
        refine ⟨54860263674750749281346603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36573509116500499520897735 54860263674750749281346603)
        ·
          refine ⟨82290395512126123922019905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54860263674750749281346603 82290395512126123922019905)
          ·
            refine ⟨61717796634094592941514929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82290395512126123922019905 61717796634094592941514929)
            ·
              refine ⟨46288347475570944706136197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61717796634094592941514929 46288347475570944706136197)
              ·
                refine ⟨8679065151669552132400537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46288347475570944706136197 8679065151669552132400537)
                ·
                  refine ⟨6509298863752164099300403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679065151669552132400537 6509298863752164099300403)
                  ·
                    refine ⟨9763948295628246148950605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509298863752164099300403 9763948295628246148950605)
                    ·
                      refine ⟨3661480610860592305856477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763948295628246148950605 3661480610860592305856477)
                      ·
                        rfl

theorem cell23_7130708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_7130708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130708 prefixEnd_7130708 := by exact prefixLift 7130708
  have htrace : WordTrace (prefixWord ++ tailWord_7130708) baseStart_7130708 baseEnd_7130708 := by
    simpa [prefixWord, tailWord_7130708, baseEnd_7130708] using wordTrace_append hprefix tailTrace_7130708
  have hstable : (prefixWord ++ tailWord_7130708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130708).length < 2 ^ (prefixWord ++ tailWord_7130708).sum := by decide
  have hdescent : baseEnd_7130708 < baseStart_7130708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130725 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_7130725 : Nat := 118140960795 + 7130725 * 2 ^ 59
def prefixEnd_7130725 : Nat := 4983230072969 + 3 ^ 40 * 7130725 * 2
def baseEnd_7130725 : Nat := 3661489340031718739343899

theorem tailTrace_7130725 : CollatzResearch.WordTrace tailWord_7130725 prefixEnd_7130725 3661489340031718739343899 := by
  unfold tailWord_7130725
  simp only [CollatzResearch.WordTrace]
  refine ⟨260078907091608630718641629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173385938061072420479094419 260078907091608630718641629)
  ·
    refine ⟨97529590159353236519490611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260078907091608630718641629 97529590159353236519490611)
    ·
      refine ⟨146294385239029854779235917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97529590159353236519490611 146294385239029854779235917)
      ·
        refine ⟨54860394464636195542213469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146294385239029854779235917 54860394464636195542213469)
        ·
          refine ⟨20572647924238573328330051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54860394464636195542213469 20572647924238573328330051)
          ·
            refine ⟨30858971886357859992495077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20572647924238573328330051 30858971886357859992495077)
            ·
              refine ⟨5786057228692098748592827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30858971886357859992495077 5786057228692098748592827)
              ·
                refine ⟨8679085843038148122889241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786057228692098748592827 8679085843038148122889241)
                ·
                  refine ⟨6509314382278611092166931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679085843038148122889241 6509314382278611092166931)
                  ·
                    refine ⟨9763971573417916638250397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509314382278611092166931 9763971573417916638250397)
                    ·
                      refine ⟨3661489340031718739343899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9763971573417916638250397 3661489340031718739343899)
                      ·
                        rfl

theorem cell23_7130725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_7130725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130725 prefixEnd_7130725 := by exact prefixLift 7130725
  have htrace : WordTrace (prefixWord ++ tailWord_7130725) baseStart_7130725 baseEnd_7130725 := by
    simpa [prefixWord, tailWord_7130725, baseEnd_7130725] using wordTrace_append hprefix tailTrace_7130725
  have hstable : (prefixWord ++ tailWord_7130725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130725).length < 2 ^ (prefixWord ++ tailWord_7130725).sum := by decide
  have hdescent : baseEnd_7130725 < baseStart_7130725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130782 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7130782 : Nat := 118140960795 + 7130782 * 2 ^ 59
def prefixEnd_7130782 : Nat := 4983230072969 + 3 ^ 40 * 7130782 * 2
def baseEnd_7130782 : Nat := 3661518608429025016331137

theorem tailTrace_7130782 : CollatzResearch.WordTrace tailWord_7130782 prefixEnd_7130782 3661518608429025016331137 := by
  unfold tailWord_7130782
  simp only [CollatzResearch.WordTrace]
  refine ⟨32510123256550266181683325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173387324034934752968977733 32510123256550266181683325)
  ·
    refine ⟨12191296221206349818131247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32510123256550266181683325 12191296221206349818131247)
    ·
      refine ⟨18286944331809524727196871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12191296221206349818131247 18286944331809524727196871)
      ·
        refine ⟨27430416497714287090795307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18286944331809524727196871 27430416497714287090795307)
        ·
          refine ⟨41145624746571430636192961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27430416497714287090795307 41145624746571430636192961)
          ·
            refine ⟨30859218559928572977144721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41145624746571430636192961 30859218559928572977144721)
            ·
              refine ⟨23144413919946429732858541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30859218559928572977144721 23144413919946429732858541)
              ·
                refine ⟨8679155219979911149821953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23144413919946429732858541 8679155219979911149821953)
                ·
                  refine ⟨6509366414984933362366465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679155219979911149821953 6509366414984933362366465)
                  ·
                    refine ⟨4882024811238700021774849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509366414984933362366465 4882024811238700021774849)
                    ·
                      refine ⟨3661518608429025016331137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882024811238700021774849 3661518608429025016331137)
                      ·
                        rfl

theorem cell23_7130782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7130782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130782 prefixEnd_7130782 := by exact prefixLift 7130782
  have htrace : WordTrace (prefixWord ++ tailWord_7130782) baseStart_7130782 baseEnd_7130782 := by
    simpa [prefixWord, tailWord_7130782, baseEnd_7130782] using wordTrace_append hprefix tailTrace_7130782
  have hstable : (prefixWord ++ tailWord_7130782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130782).length < 2 ^ (prefixWord ++ tailWord_7130782).sum := by decide
  have hdescent : baseEnd_7130782 < baseStart_7130782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130805 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 5]
def baseStart_7130805 : Nat := 118140960795 + 7130805 * 2 ^ 59
def prefixEnd_7130805 : Nat := 4983230072969 + 3 ^ 40 * 7130805 * 2
def baseEnd_7130805 : Nat := 406836713164897602927059

theorem tailTrace_7130805 : CollatzResearch.WordTrace tailWord_7130805 prefixEnd_7130805 406836713164897602927059 := by
  unfold tailWord_7130805
  simp only [CollatzResearch.WordTrace]
  refine ⟨260081824931318804381553869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173387883287545869587702579 260081824931318804381553869)
  ·
    refine ⟨97530684349244551643082701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260081824931318804381553869 97530684349244551643082701)
    ·
      refine ⟨36574006630966706866156013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97530684349244551643082701 36574006630966706866156013)
      ·
        refine ⟨13715252486612515074808505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36574006630966706866156013 13715252486612515074808505)
        ·
          refine ⟨10286439364959386306106379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13715252486612515074808505 10286439364959386306106379)
          ·
            refine ⟨15429659047439079459159569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10286439364959386306106379 15429659047439079459159569)
            ·
              refine ⟨11572244285579309594369677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15429659047439079459159569 11572244285579309594369677)
              ·
                refine ⟨4339591607092241097888629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11572244285579309594369677 4339591607092241097888629)
                ·
                  refine ⟨406836713164897602927059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4339591607092241097888629 406836713164897602927059)
                  ·
                    rfl

theorem cell23_7130805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_7130805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130805 prefixEnd_7130805 := by exact prefixLift 7130805
  have htrace : WordTrace (prefixWord ++ tailWord_7130805) baseStart_7130805 baseEnd_7130805 := by
    simpa [prefixWord, tailWord_7130805, baseEnd_7130805] using wordTrace_append hprefix tailTrace_7130805
  have hstable : (prefixWord ++ tailWord_7130805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130805).length < 2 ^ (prefixWord ++ tailWord_7130805).sum := by decide
  have hdescent : baseEnd_7130805 < baseStart_7130805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130821 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_7130821 : Nat := 118140960795 + 7130821 * 2 ^ 59
def prefixEnd_7130821 : Nat := 4983230072969 + 3 ^ 40 * 7130821 * 2
def baseEnd_7130821 : Nat := 3661538634174550363743457

theorem tailTrace_7130821 : CollatzResearch.WordTrace tailWord_7130821 prefixEnd_7130821 3661538634174550363743457 := by
  unfold tailWord_7130821
  simp only [CollatzResearch.WordTrace]
  refine ⟨260082408499260839114136317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173388272332840559409424211 260082408499260839114136317)
  ·
    refine ⟨97530903187222814667801119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260082408499260839114136317 97530903187222814667801119)
    ·
      refine ⟨146296354780834222001701679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97530903187222814667801119 146296354780834222001701679)
      ·
        refine ⟨219444532171251333002552519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146296354780834222001701679 219444532171251333002552519)
        ·
          refine ⟨329166798256876999503828779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219444532171251333002552519 329166798256876999503828779)
          ·
            refine ⟨493750197385315499255743169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329166798256876999503828779 493750197385315499255743169)
            ·
              refine ⟨370312648038986624441807377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493750197385315499255743169 370312648038986624441807377)
              ·
                refine ⟨277734486029239968331355533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370312648038986624441807377 277734486029239968331355533)
                ·
                  refine ⟨104150432260964988124258325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277734486029239968331355533 104150432260964988124258325)
                  ·
                    refine ⟨4882051512232733818324609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104150432260964988124258325 4882051512232733818324609)
                    ·
                      refine ⟨3661538634174550363743457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882051512232733818324609 3661538634174550363743457)
                      ·
                        rfl

theorem cell23_7130821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_7130821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130821 prefixEnd_7130821 := by exact prefixLift 7130821
  have htrace : WordTrace (prefixWord ++ tailWord_7130821) baseStart_7130821 baseEnd_7130821 := by
    simpa [prefixWord, tailWord_7130821, baseEnd_7130821] using wordTrace_append hprefix tailTrace_7130821
  have hstable : (prefixWord ++ tailWord_7130821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130821).length < 2 ^ (prefixWord ++ tailWord_7130821).sum := by decide
  have hdescent : baseEnd_7130821 < baseStart_7130821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130822 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_7130822 : Nat := 118140960795 + 7130822 * 2 ^ 59
def prefixEnd_7130822 : Nat := 4983230072969 + 3 ^ 40 * 7130822 * 2
def baseEnd_7130822 : Nat := 406837683072800539981217

theorem tailTrace_7130822 : CollatzResearch.WordTrace tailWord_7130822 prefixEnd_7130822 406837683072800539981217 := by
  unfold tailWord_7130822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127576405383038008903835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173388296648171477523281813 8127576405383038008903835)
  ·
    refine ⟨12191364608074557013355753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8127576405383038008903835 12191364608074557013355753)
    ·
      refine ⟨9143523456055917760016815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12191364608074557013355753 9143523456055917760016815)
      ·
        refine ⟨13715285184083876640025223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9143523456055917760016815 13715285184083876640025223)
        ·
          refine ⟨20572927776125814960037835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13715285184083876640025223 20572927776125814960037835)
          ·
            refine ⟨30859391664188722440056753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20572927776125814960037835 30859391664188722440056753)
            ·
              refine ⟨23144543748141541830042565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30859391664188722440056753 23144543748141541830042565)
              ·
                refine ⟨4339601952776539093132981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23144543748141541830042565 4339601952776539093132981)
                ·
                  refine ⟨406837683072800539981217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4339601952776539093132981 406837683072800539981217)
                  ·
                    rfl

theorem cell23_7130822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_7130822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130822 prefixEnd_7130822 := by exact prefixLift 7130822
  have htrace : WordTrace (prefixWord ++ tailWord_7130822) baseStart_7130822 baseEnd_7130822 := by
    simpa [prefixWord, tailWord_7130822, baseEnd_7130822] using wordTrace_append hprefix tailTrace_7130822
  have hstable : (prefixWord ++ tailWord_7130822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130822).length < 2 ^ (prefixWord ++ tailWord_7130822).sum := by decide
  have hdescent : baseEnd_7130822 < baseStart_7130822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130841 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_7130841 : Nat := 118140960795 + 7130841 * 2 ^ 59
def prefixEnd_7130841 : Nat := 4983230072969 + 3 ^ 40 * 7130841 * 2
def baseEnd_7130841 : Nat := 3661548903787640285493365

theorem tailTrace_7130841 : CollatzResearch.WordTrace tailWord_7130841 prefixEnd_7130841 3661548903787640285493365 := by
  unfold tailWord_7130841
  simp only [CollatzResearch.WordTrace]
  refine ⟨260083137959188382529864377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173388758639458921686576251 260083137959188382529864377)
  ·
    refine ⟨195062353469391286897398283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260083137959188382529864377 195062353469391286897398283)
    ·
      refine ⟨292593530204086930346097425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195062353469391286897398283 292593530204086930346097425)
      ·
        refine ⟨219445147653065197759573069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292593530204086930346097425 219445147653065197759573069)
        ·
          refine ⟨82291930369899449159839901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219445147653065197759573069 82291930369899449159839901)
          ·
            refine ⟨30859473888712293434939963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82291930369899449159839901 30859473888712293434939963)
            ·
              refine ⟨46289210833068440152409945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30859473888712293434939963 46289210833068440152409945)
              ·
                refine ⟨34716908124801330114307459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46289210833068440152409945 34716908124801330114307459)
                ·
                  refine ⟨52075362187201995171461189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34716908124801330114307459 52075362187201995171461189)
                  ·
                    refine ⟨9764130410100374094648973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52075362187201995171461189 9764130410100374094648973)
                    ·
                      refine ⟨3661548903787640285493365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9764130410100374094648973 3661548903787640285493365)
                      ·
                        rfl

theorem cell23_7130841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_7130841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130841 prefixEnd_7130841 := by exact prefixLift 7130841
  have htrace : WordTrace (prefixWord ++ tailWord_7130841) baseStart_7130841 baseEnd_7130841 := by
    simpa [prefixWord, tailWord_7130841, baseEnd_7130841] using wordTrace_append hprefix tailTrace_7130841
  have hstable : (prefixWord ++ tailWord_7130841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130841).length < 2 ^ (prefixWord ++ tailWord_7130841).sum := by decide
  have hdescent : baseEnd_7130841 < baseStart_7130841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130861 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 8]
def baseStart_7130861 : Nat := 118140960795 + 7130861 * 2 ^ 59
def prefixEnd_7130861 : Nat := 4983230072969 + 3 ^ 40 * 7130861 * 2
def baseEnd_7130861 : Nat := 406839908155636689693697

theorem tailTrace_7130861 : CollatzResearch.WordTrace tailWord_7130861 prefixEnd_7130861 406839908155636689693697 := by
  unfold tailWord_7130861
  simp only [CollatzResearch.WordTrace]
  refine ⟨260083867419115925945592437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173389244946077283963728291 260083867419115925945592437)
  ·
    refine ⟨24382862570542118057399291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260083867419115925945592437 24382862570542118057399291)
    ·
      refine ⟨36574293855813177086098937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24382862570542118057399291 36574293855813177086098937)
      ·
        refine ⟨27430720391859882814574203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36574293855813177086098937 27430720391859882814574203)
        ·
          refine ⟨41146080587789824221861305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27430720391859882814574203 41146080587789824221861305)
          ·
            refine ⟨30859560440842368166395979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41146080587789824221861305 30859560440842368166395979)
            ·
              refine ⟨46289340661263552249593969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30859560440842368166395979 46289340661263552249593969)
              ·
                refine ⟨34717005495947664187195477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46289340661263552249593969 34717005495947664187195477)
                ·
                  refine ⟨406839908155636689693697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34717005495947664187195477 406839908155636689693697)
                  ·
                    rfl

theorem cell23_7130861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_7130861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130861 prefixEnd_7130861 := by exact prefixLift 7130861
  have htrace : WordTrace (prefixWord ++ tailWord_7130861) baseStart_7130861 baseEnd_7130861 := by
    simpa [prefixWord, tailWord_7130861, baseEnd_7130861] using wordTrace_append hprefix tailTrace_7130861
  have hstable : (prefixWord ++ tailWord_7130861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130861).length < 2 ^ (prefixWord ++ tailWord_7130861).sum := by decide
  have hdescent : baseEnd_7130861 < baseStart_7130861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_7130864 : Nat := 118140960795 + 7130864 * 2 ^ 59
def prefixEnd_7130864 : Nat := 4983230072969 + 3 ^ 40 * 7130864 * 2
def baseEnd_7130864 : Nat := 3661560713842693695505759

theorem tailTrace_7130864 : CollatzResearch.WordTrace tailWord_7130864 prefixEnd_7130864 3661560713842693695505759 := by
  unfold tailWord_7130864
  simp only [CollatzResearch.WordTrace]
  refine ⟨130041988419052528728975823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173389317892070038305301097 130041988419052528728975823)
  ·
    refine ⟨195062982628578793093463735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130041988419052528728975823 195062982628578793093463735)
    ·
      refine ⟨292594473942868189640195603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195062982628578793093463735 292594473942868189640195603)
      ·
        refine ⟨438891710914302284460293405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292594473942868189640195603 438891710914302284460293405)
        ·
          refine ⟨164584391592863356672610027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438891710914302284460293405 164584391592863356672610027)
          ·
            refine ⟨246876587389295035008915041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164584391592863356672610027 246876587389295035008915041)
            ·
              refine ⟨185157440541971276256686281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246876587389295035008915041 185157440541971276256686281)
              ·
                refine ⟨138868080406478457192514711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185157440541971276256686281 138868080406478457192514711)
                ·
                  refine ⟨208302120609717685788772067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138868080406478457192514711 208302120609717685788772067)
                  ·
                    refine ⟨312453180914576528683158101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 208302120609717685788772067 312453180914576528683158101)
                    ·
                      refine ⟨3661560713842693695505759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 312453180914576528683158101 3661560713842693695505759)
                      ·
                        rfl

theorem cell23_7130864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_7130864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130864 prefixEnd_7130864 := by exact prefixLift 7130864
  have htrace : WordTrace (prefixWord ++ tailWord_7130864) baseStart_7130864 baseEnd_7130864 := by
    simpa [prefixWord, tailWord_7130864, baseEnd_7130864] using wordTrace_append hprefix tailTrace_7130864
  have hstable : (prefixWord ++ tailWord_7130864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130864).length < 2 ^ (prefixWord ++ tailWord_7130864).sum := by decide
  have hdescent : baseEnd_7130864 < baseStart_7130864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130865 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 1, 4]
def baseStart_7130865 : Nat := 118140960795 + 7130865 * 2 ^ 59
def prefixEnd_7130865 : Nat := 4983230072969 + 3 ^ 40 * 7130865 * 2
def baseEnd_7130865 : Nat := 1220520409107782730531085

theorem tailTrace_7130865 : CollatzResearch.WordTrace tailWord_7130865 prefixEnd_7130865 1220520409107782730531085 := by
  unfold tailWord_7130865
  simp only [CollatzResearch.WordTrace]
  refine ⟨260084013311101434628738049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173389342207400956419158699 260084013311101434628738049)
  ·
    refine ⟨195063009983326075971553537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260084013311101434628738049 195063009983326075971553537)
    ·
      refine ⟨146297257487494556978665153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195063009983326075971553537 146297257487494556978665153)
      ·
        refine ⟨109722943115620917733998865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146297257487494556978665153 109722943115620917733998865)
        ·
          refine ⟨82292207336715688300499149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109722943115620917733998865 82292207336715688300499149)
          ·
            refine ⟨30859577751268383112687181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82292207336715688300499149 30859577751268383112687181)
            ·
              refine ⟨11572341656725643667257693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30859577751268383112687181 11572341656725643667257693)
              ·
                refine ⟨4339628121272116375221635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11572341656725643667257693 4339628121272116375221635)
                ·
                  refine ⟨6509442181908174562832453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339628121272116375221635 6509442181908174562832453)
                  ·
                    refine ⟨1220520409107782730531085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509442181908174562832453 1220520409107782730531085)
                    ·
                      rfl

theorem cell23_7130865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_7130865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130865 prefixEnd_7130865 := by exact prefixLift 7130865
  have htrace : WordTrace (prefixWord ++ tailWord_7130865) baseStart_7130865 baseEnd_7130865 := by
    simpa [prefixWord, tailWord_7130865, baseEnd_7130865] using wordTrace_append hprefix tailTrace_7130865
  have hstable : (prefixWord ++ tailWord_7130865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130865).length < 2 ^ (prefixWord ++ tailWord_7130865).sum := by decide
  have hdescent : baseEnd_7130865 < baseStart_7130865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130932 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7130932 : Nat := 118140960795 + 7130932 * 2 ^ 59
def prefixEnd_7130932 : Nat := 4983230072969 + 3 ^ 40 * 7130932 * 2
def baseEnd_7130932 : Nat := 3661595630527199429455447

theorem tailTrace_7130932 : CollatzResearch.WordTrace tailWord_7130932 prefixEnd_7130932 3661595630527199429455447 := by
  unfold tailWord_7130932
  simp only [CollatzResearch.WordTrace]
  refine ⟨130043228500929352535713525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173390971334572470047618033 130043228500929352535713525)
  ·
    refine ⟨12191552671962126800223143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130043228500929352535713525 12191552671962126800223143)
    ·
      refine ⟨18287329007943190200334715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12191552671962126800223143 18287329007943190200334715)
      ·
        refine ⟨27430993511914785300502073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18287329007943190200334715 27430993511914785300502073)
        ·
          refine ⟨20573245133936088975376555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27430993511914785300502073 20573245133936088975376555)
          ·
            refine ⟨30859867700904133463064833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20573245133936088975376555 30859867700904133463064833)
            ·
              refine ⟨23144900775678100097298625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30859867700904133463064833 23144900775678100097298625)
              ·
                refine ⟨17358675581758575072973969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23144900775678100097298625 17358675581758575072973969)
                ·
                  refine ⟨13019006686318931304730477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17358675581758575072973969 13019006686318931304730477)
                  ·
                    refine ⟨4882127507369599239273929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13019006686318931304730477 4882127507369599239273929)
                    ·
                      refine ⟨3661595630527199429455447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882127507369599239273929 3661595630527199429455447)
                      ·
                        rfl

theorem cell23_7130932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7130932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130932 prefixEnd_7130932 := by exact prefixLift 7130932
  have htrace : WordTrace (prefixWord ++ tailWord_7130932) baseStart_7130932 baseEnd_7130932 := by
    simpa [prefixWord, tailWord_7130932, baseEnd_7130932] using wordTrace_append hprefix tailTrace_7130932
  have hstable : (prefixWord ++ tailWord_7130932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130932).length < 2 ^ (prefixWord ++ tailWord_7130932).sum := by decide
  have hdescent : baseEnd_7130932 < baseStart_7130932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130951 : List Nat := [1, 1, 4, 1, 2, 1, 5, 8]
def baseStart_7130951 : Nat := 118140960795 + 7130951 * 2 ^ 59
def prefixEnd_7130951 : Nat := 4983230072969 + 3 ^ 40 * 7130951 * 2
def baseEnd_7130951 : Nat := 135615014320727216856217

theorem tailTrace_7130951 : CollatzResearch.WordTrace tailWord_7130951 prefixEnd_7130951 135615014320727216856217 := by
  unfold tailWord_7130951
  simp only [CollatzResearch.WordTrace]
  refine ⟨260087149988789871316368707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173391433325859914210912471 260087149988789871316368707)
  ·
    refine ⟨390130724983184806974553061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260087149988789871316368707 390130724983184806974553061)
    ·
      refine ⟨73149510934347151307728699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 390130724983184806974553061 73149510934347151307728699)
      ·
        refine ⟨109724266401520726961593049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73149510934347151307728699 109724266401520726961593049)
        ·
          refine ⟨82293199801140545221194787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109724266401520726961593049 82293199801140545221194787)
          ·
            refine ⟨123439799701710817831792181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82293199801140545221194787 123439799701710817831792181)
            ·
              refine ⟨11572481222035389171730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123439799701710817831792181 11572481222035389171730517)
              ·
                refine ⟨135615014320727216856217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11572481222035389171730517 135615014320727216856217)
                ·
                  rfl

theorem cell23_7130951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 8].length) (baseStart_7130951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130951 prefixEnd_7130951 := by exact prefixLift 7130951
  have htrace : WordTrace (prefixWord ++ tailWord_7130951) baseStart_7130951 baseEnd_7130951 := by
    simpa [prefixWord, tailWord_7130951, baseEnd_7130951] using wordTrace_append hprefix tailTrace_7130951
  have hstable : (prefixWord ++ tailWord_7130951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130951).length < 2 ^ (prefixWord ++ tailWord_7130951).sum := by decide
  have hdescent : baseEnd_7130951 < baseStart_7130951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130962 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_7130962 : Nat := 118140960795 + 7130962 * 2 ^ 59
def prefixEnd_7130962 : Nat := 4983230072969 + 3 ^ 40 * 7130962 * 2
def baseEnd_7130962 : Nat := 3661611034946834312080309

theorem tailTrace_7130962 : CollatzResearch.WordTrace tailWord_7130962 prefixEnd_7130962 3661611034946834312080309 := by
  unfold tailWord_7130962
  simp only [CollatzResearch.WordTrace]
  refine ⟨65021887797937505048754785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173391700794500013463346093 65021887797937505048754785)
  ·
    refine ⟨48766415848453128786566089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65021887797937505048754785 48766415848453128786566089)
    ·
      refine ⟨36574811886339846589924567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48766415848453128786566089 36574811886339846589924567)
      ·
        refine ⟨54862217829509769884886851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36574811886339846589924567 54862217829509769884886851)
        ·
          refine ⟨82293326744264654827330277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54862217829509769884886851 82293326744264654827330277)
          ·
            refine ⟨15429998764549622780124427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82293326744264654827330277 15429998764549622780124427)
            ·
              refine ⟨23144998146824434170186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15429998764549622780124427 23144998146824434170186641)
              ·
                refine ⟨17358748610118325627639981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23144998146824434170186641 17358748610118325627639981)
                ·
                  refine ⟨6509530728794372110364993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17358748610118325627639981 6509530728794372110364993)
                  ·
                    refine ⟨4882148046595779082773745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509530728794372110364993 4882148046595779082773745)
                    ·
                      refine ⟨3661611034946834312080309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882148046595779082773745 3661611034946834312080309)
                      ·
                        rfl

theorem cell23_7130962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_7130962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130962 prefixEnd_7130962 := by exact prefixLift 7130962
  have htrace : WordTrace (prefixWord ++ tailWord_7130962) baseStart_7130962 baseEnd_7130962 := by
    simpa [prefixWord, tailWord_7130962, baseEnd_7130962] using wordTrace_append hprefix tailTrace_7130962
  have hstable : (prefixWord ++ tailWord_7130962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130962).length < 2 ^ (prefixWord ++ tailWord_7130962).sum := by decide
  have hdescent : baseEnd_7130962 < baseStart_7130962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7130979 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 1, 1, 4]
def baseStart_7130979 : Nat := 118140960795 + 7130979 * 2 ^ 59
def prefixEnd_7130979 : Nat := 4983230072969 + 3 ^ 40 * 7130979 * 2
def baseEnd_7130979 : Nat := 3661619764117960745567731

theorem tailTrace_7130979 : CollatzResearch.WordTrace tailWord_7130979 prefixEnd_7130979 3661619764117960745567731 := by
  unfold tailWord_7130979
  simp only [CollatzResearch.WordTrace]
  refine ⟨260088171232688432098387991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173392114155125621398925327 260088171232688432098387991)
  ·
    refine ⟨390132256849032648147581987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260088171232688432098387991 390132256849032648147581987)
    ·
      refine ⟨585198385273548972221372981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390132256849032648147581987 585198385273548972221372981)
      ·
        refine ⟨54862348619395216145753717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 585198385273548972221372981 54862348619395216145753717)
        ·
          refine ⟨5143345183068301513664411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54862348619395216145753717 5143345183068301513664411)
          ·
            refine ⟨7715017774602452270496617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143345183068301513664411 7715017774602452270496617)
            ·
              refine ⟨5786263330951839202872463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715017774602452270496617 5786263330951839202872463)
              ·
                refine ⟨8679394996427758804308695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786263330951839202872463 8679394996427758804308695)
                ·
                  refine ⟨13019092494641638206463043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8679394996427758804308695 13019092494641638206463043)
                  ·
                    refine ⟨19528638741962457309694565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13019092494641638206463043 19528638741962457309694565)
                    ·
                      refine ⟨3661619764117960745567731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19528638741962457309694565 3661619764117960745567731)
                      ·
                        rfl

theorem cell23_7130979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_7130979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7130979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7130979 prefixEnd_7130979 := by exact prefixLift 7130979
  have htrace : WordTrace (prefixWord ++ tailWord_7130979) baseStart_7130979 baseEnd_7130979 := by
    simpa [prefixWord, tailWord_7130979, baseEnd_7130979] using wordTrace_append hprefix tailTrace_7130979
  have hstable : (prefixWord ++ tailWord_7130979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7130979).length < 2 ^ (prefixWord ++ tailWord_7130979).sum := by decide
  have hdescent : baseEnd_7130979 < baseStart_7130979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7130979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131009 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7131009 : Nat := 118140960795 + 7131009 * 2 ^ 59
def prefixEnd_7131009 : Nat := 4983230072969 + 3 ^ 40 * 7131009 * 2
def baseEnd_7131009 : Nat := 3661635168537595628192593

theorem tailTrace_7131009 : CollatzResearch.WordTrace tailWord_7131009 prefixEnd_7131009 3661635168537595628192593 := by
  unfold tailWord_7131009
  simp only [CollatzResearch.WordTrace]
  refine ⟨260089265422579747221980081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173392843615053164814653387 260089265422579747221980081)
  ·
    refine ⟨195066949066934810416485061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260089265422579747221980081 195066949066934810416485061)
    ·
      refine ⟨36575052950050276953090949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195066949066934810416485061 36575052950050276953090949)
      ·
        refine ⟨6857822428134426928704553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36575052950050276953090949 6857822428134426928704553)
        ·
          refine ⟨5143366821100820196528415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857822428134426928704553 5143366821100820196528415)
          ·
            refine ⟨7715050231651230294792623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143366821100820196528415 7715050231651230294792623)
            ·
              refine ⟨11572575347476845442188935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715050231651230294792623 11572575347476845442188935)
              ·
                refine ⟨17358863021215268163283403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11572575347476845442188935 17358863021215268163283403)
                ·
                  refine ⟨26038294531822902244925105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17358863021215268163283403 26038294531822902244925105)
                  ·
                    refine ⟨19528720898867176683693829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26038294531822902244925105 19528720898867176683693829)
                    ·
                      refine ⟨3661635168537595628192593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19528720898867176683693829 3661635168537595628192593)
                      ·
                        rfl

theorem cell23_7131009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7131009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131009 prefixEnd_7131009 := by exact prefixLift 7131009
  have htrace : WordTrace (prefixWord ++ tailWord_7131009) baseStart_7131009 baseEnd_7131009 := by
    simpa [prefixWord, tailWord_7131009, baseEnd_7131009] using wordTrace_append hprefix tailTrace_7131009
  have hstable : (prefixWord ++ tailWord_7131009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131009).length < 2 ^ (prefixWord ++ tailWord_7131009).sum := by decide
  have hdescent : baseEnd_7131009 < baseStart_7131009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131069 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_7131069 : Nat := 118140960795 + 7131069 * 2 ^ 59
def prefixEnd_7131069 : Nat := 4983230072969 + 3 ^ 40 * 7131069 * 2
def baseEnd_7131069 : Nat := 3661665977376865393442317

theorem tailTrace_7131069 : CollatzResearch.WordTrace tailWord_7131069 prefixEnd_7131069 3661665977376865393442317 := by
  unfold tailWord_7131069
  simp only [CollatzResearch.WordTrace]
  refine ⟨260091453802362377469164261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173394302534908251646109507 260091453802362377469164261)
  ·
    refine ⟨48767147587942945775468299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260091453802362377469164261 48767147587942945775468299)
    ·
      refine ⟨73150721381914418663202449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48767147587942945775468299 73150721381914418663202449)
      ·
        refine ⟨54863041036435813997401837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73150721381914418663202449 54863041036435813997401837)
        ·
          refine ⟨20573640388663430249025689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54863041036435813997401837 20573640388663430249025689)
          ·
            refine ⟨15430230291497572686769267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20573640388663430249025689 15430230291497572686769267)
            ·
              refine ⟨23145345437246359030153901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15430230291497572686769267 23145345437246359030153901)
              ·
                refine ⟨8679504538967384636307713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23145345437246359030153901 8679504538967384636307713)
                ·
                  refine ⟨6509628404225538477230785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679504538967384636307713 6509628404225538477230785)
                  ·
                    refine ⟨4882221303169153857923089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509628404225538477230785 4882221303169153857923089)
                    ·
                      refine ⟨3661665977376865393442317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882221303169153857923089 3661665977376865393442317)
                      ·
                        rfl

theorem cell23_7131069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_7131069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131069 prefixEnd_7131069 := by exact prefixLift 7131069
  have htrace : WordTrace (prefixWord ++ tailWord_7131069) baseStart_7131069 baseEnd_7131069 := by
    simpa [prefixWord, tailWord_7131069, baseEnd_7131069] using wordTrace_append hprefix tailTrace_7131069
  have hstable : (prefixWord ++ tailWord_7131069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131069).length < 2 ^ (prefixWord ++ tailWord_7131069).sum := by decide
  have hdescent : baseEnd_7131069 < baseStart_7131069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131088 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_7131088 : Nat := 118140960795 + 7131088 * 2 ^ 59
def prefixEnd_7131088 : Nat := 4983230072969 + 3 ^ 40 * 7131088 * 2
def baseEnd_7131088 : Nat := 1220558577836433606368243

theorem tailTrace_7131088 : CollatzResearch.WordTrace tailWord_7131088 prefixEnd_7131088 1220558577836433606368243 := by
  unfold tailWord_7131088
  simp only [CollatzResearch.WordTrace]
  refine ⟨130046073394646771857052959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173394764526195695809403945 130046073394646771857052959)
  ·
    refine ⟨195069110091970157785579439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130046073394646771857052959 195069110091970157785579439)
    ·
      refine ⟨292603665137955236678369159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195069110091970157785579439 292603665137955236678369159)
      ·
        refine ⟨438905497706932855017553739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292603665137955236678369159 438905497706932855017553739)
        ·
          refine ⟨658358246560399282526330609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438905497706932855017553739 658358246560399282526330609)
          ·
            refine ⟨493768684920299461894747957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658358246560399282526330609 493768684920299461894747957)
            ·
              refine ⟨46290814211278074552632621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 493768684920299461894747957 46290814211278074552632621)
              ·
                refine ⟨17359055329229277957237233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46290814211278074552632621 17359055329229277957237233)
                ·
                  refine ⟨13019291496921958467927925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17359055329229277957237233 13019291496921958467927925)
                  ·
                    refine ⟨1220558577836433606368243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13019291496921958467927925 1220558577836433606368243)
                    ·
                      rfl

theorem cell23_7131088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_7131088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131088 prefixEnd_7131088 := by exact prefixLift 7131088
  have htrace : WordTrace (prefixWord ++ tailWord_7131088) baseStart_7131088 baseEnd_7131088 := by
    simpa [prefixWord, tailWord_7131088, baseEnd_7131088] using wordTrace_append hprefix tailTrace_7131088
  have hstable : (prefixWord ++ tailWord_7131088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131088).length < 2 ^ (prefixWord ++ tailWord_7131088).sum := by decide
  have hdescent : baseEnd_7131088 < baseStart_7131088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131148 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 8]
def baseStart_7131148 : Nat := 118140960795 + 7131148 * 2 ^ 59
def prefixEnd_7131148 : Nat := 4983230072969 + 3 ^ 40 * 7131148 * 2
def baseEnd_7131148 : Nat := 406856282483174509372717

theorem tailTrace_7131148 : CollatzResearch.WordTrace tailWord_7131148 prefixEnd_7131148 406856282483174509372717 := by
  unfold tailWord_7131148
  simp only [CollatzResearch.WordTrace]
  refine ⟨130047167584538086980645049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173396223446050782640860065 130047167584538086980645049)
  ·
    refine ⟨97535375688403565235483787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130047167584538086980645049 97535375688403565235483787)
    ·
      refine ⟨146303063532605347853225681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97535375688403565235483787 146303063532605347853225681)
      ·
        refine ⟨109727297649454010889919261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146303063532605347853225681 109727297649454010889919261)
        ·
          refine ⟨41147736618545254083719723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109727297649454010889919261 41147736618545254083719723)
          ·
            refine ⟨61721604927817881125579585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41147736618545254083719723 61721604927817881125579585)
            ·
              refine ⟨46291203695863410844184689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61721604927817881125579585 46291203695863410844184689)
              ·
                refine ⟨34718402771897558133138517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46291203695863410844184689 34718402771897558133138517)
                ·
                  refine ⟨406856282483174509372717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34718402771897558133138517 406856282483174509372717)
                  ·
                    rfl

theorem cell23_7131148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_7131148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131148 prefixEnd_7131148 := by exact prefixLift 7131148
  have htrace : WordTrace (prefixWord ++ tailWord_7131148) baseStart_7131148 baseEnd_7131148 := by
    simpa [prefixWord, tailWord_7131148, baseEnd_7131148] using wordTrace_append hprefix tailTrace_7131148
  have hstable : (prefixWord ++ tailWord_7131148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131148).length < 2 ^ (prefixWord ++ tailWord_7131148).sum := by decide
  have hdescent : baseEnd_7131148 < baseStart_7131148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131165 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 8]
def baseStart_7131165 : Nat := 118140960795 + 7131165 * 2 ^ 59
def prefixEnd_7131165 : Nat := 4983230072969 + 3 ^ 40 * 7131165 * 2
def baseEnd_7131165 : Nat := 406857252391077446426875

theorem tailTrace_7131165 : CollatzResearch.WordTrace tailWord_7131165 prefixEnd_7131165 406857252391077446426875 := by
  unfold tailWord_7131165
  simp only [CollatzResearch.WordTrace]
  refine ⟨260094955210014585864658949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173396636806676390576439299 260094955210014585864658949)
  ·
    refine ⟨48767804101877734849623553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260094955210014585864658949 48767804101877734849623553)
    ·
      refine ⟨36575853076408301137217665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48767804101877734849623553 36575853076408301137217665)
      ·
        refine ⟨27431889807306225852913249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36575853076408301137217665 27431889807306225852913249)
        ·
          refine ⟨20573917355479669389684937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27431889807306225852913249 20573917355479669389684937)
          ·
            refine ⟨15430438016609752042263703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20573917355479669389684937 15430438016609752042263703)
            ·
              refine ⟨23145657024914628063395555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15430438016609752042263703 23145657024914628063395555)
              ·
                refine ⟨34718485537371942095093333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23145657024914628063395555 34718485537371942095093333)
                ·
                  refine ⟨406857252391077446426875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34718485537371942095093333 406857252391077446426875)
                  ·
                    rfl

theorem cell23_7131165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_7131165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131165 prefixEnd_7131165 := by exact prefixLift 7131165
  have htrace : WordTrace (prefixWord ++ tailWord_7131165) baseStart_7131165 baseEnd_7131165 := by
    simpa [prefixWord, tailWord_7131165, baseEnd_7131165] using wordTrace_append hprefix tailTrace_7131165
  have hstable : (prefixWord ++ tailWord_7131165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131165).length < 2 ^ (prefixWord ++ tailWord_7131165).sum := by decide
  have hdescent : baseEnd_7131165 < baseStart_7131165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131215 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 8, 2]
def baseStart_7131215 : Nat := 118140960795 + 7131215 * 2 ^ 59
def prefixEnd_7131215 : Nat := 4983230072969 + 3 ^ 40 * 7131215 * 2
def baseEnd_7131215 : Nat := 3661740945552421822216645

theorem tailTrace_7131215 : CollatzResearch.WordTrace tailWord_7131215 prefixEnd_7131215 3661740945552421822216645 := by
  unfold tailWord_7131215
  simp only [CollatzResearch.WordTrace]
  refine ⟨260096778859833444403979099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173397852573222296269319399 260096778859833444403979099)
  ·
    refine ⟨390145168289750166605968649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260096778859833444403979099 390145168289750166605968649)
    ·
      refine ⟨292608876217312624954476487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390145168289750166605968649 292608876217312624954476487)
      ·
        refine ⟨438913314325968937431714731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292608876217312624954476487 438913314325968937431714731)
        ·
          refine ⟨658369971488953406147572097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438913314325968937431714731 658369971488953406147572097)
          ·
            refine ⟨493777478616715054610679073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658369971488953406147572097 493777478616715054610679073)
            ·
              refine ⟨370333108962536290958009305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493777478616715054610679073 370333108962536290958009305)
              ·
                refine ⟨277749831721902218218506979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370333108962536290958009305 277749831721902218218506979)
                ·
                  refine ⟨416624747582853327327760469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277749831721902218218506979 416624747582853327327760469)
                  ·
                    refine ⟨4882321260736562429622193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 416624747582853327327760469 4882321260736562429622193)
                    ·
                      refine ⟨3661740945552421822216645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882321260736562429622193 3661740945552421822216645)
                      ·
                        rfl

theorem cell23_7131215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8, 2].length) (baseStart_7131215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131215 prefixEnd_7131215 := by exact prefixLift 7131215
  have htrace : WordTrace (prefixWord ++ tailWord_7131215) baseStart_7131215 baseEnd_7131215 := by
    simpa [prefixWord, tailWord_7131215, baseEnd_7131215] using wordTrace_append hprefix tailTrace_7131215
  have hstable : (prefixWord ++ tailWord_7131215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131215).length < 2 ^ (prefixWord ++ tailWord_7131215).sum := by decide
  have hdescent : baseEnd_7131215 < baseStart_7131215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131225 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_7131225 : Nat := 118140960795 + 7131225 * 2 ^ 59
def prefixEnd_7131225 : Nat := 4983230072969 + 3 ^ 40 * 7131225 * 2
def baseEnd_7131225 : Nat := 1220582026786322261030533

theorem tailTrace_7131225 : CollatzResearch.WordTrace tailWord_7131225 prefixEnd_7131225 1220582026786322261030533 := by
  unfold tailWord_7131225
  simp only [CollatzResearch.WordTrace]
  refine ⟨260097143589797216111843129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173398095726531477407895419 260097143589797216111843129)
  ·
    refine ⟨195072857692347912083882347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260097143589797216111843129 195072857692347912083882347)
    ·
      refine ⟨292609286538521868125823521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195072857692347912083882347 292609286538521868125823521)
      ·
        refine ⟨219456964903891401094367641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292609286538521868125823521 219456964903891401094367641)
        ·
          refine ⟨164592723677918550820775731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219456964903891401094367641 164592723677918550820775731)
          ·
            refine ⟨246889085516877826231163597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164592723677918550820775731 246889085516877826231163597)
            ·
              refine ⟨92583407068829184836686349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246889085516877826231163597 92583407068829184836686349)
              ·
                refine ⟨34718777650810944313757381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92583407068829184836686349 34718777650810944313757381)
                ·
                  refine ⟨6509770809527052058829509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34718777650810944313757381 6509770809527052058829509)
                  ·
                    refine ⟨1220582026786322261030533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6509770809527052058829509 1220582026786322261030533)
                    ·
                      rfl

theorem cell23_7131225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_7131225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131225 prefixEnd_7131225 := by exact prefixLift 7131225
  have htrace : WordTrace (prefixWord ++ tailWord_7131225) baseStart_7131225 baseEnd_7131225 := by
    simpa [prefixWord, tailWord_7131225, baseEnd_7131225] using wordTrace_append hprefix tailTrace_7131225
  have hstable : (prefixWord ++ tailWord_7131225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131225).length < 2 ^ (prefixWord ++ tailWord_7131225).sum := by decide
  have hdescent : baseEnd_7131225 < baseStart_7131225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131226 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_7131226 : Nat := 118140960795 + 7131226 * 2 ^ 59
def prefixEnd_7131226 : Nat := 4983230072969 + 3 ^ 40 * 7131226 * 2
def baseEnd_7131226 : Nat := 3661746593839621279179095

theorem tailTrace_7131226 : CollatzResearch.WordTrace tailWord_7131226 prefixEnd_7131226 3661746593839621279179095 := by
  unfold tailWord_7131226
  simp only [CollatzResearch.WordTrace]
  refine ⟨65024295015698398320657383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173398120041862395521753021 65024295015698398320657383)
  ·
    refine ⟨97536442523547597480986075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65024295015698398320657383 97536442523547597480986075)
    ·
      refine ⟨146304663785321396221479113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97536442523547597480986075 146304663785321396221479113)
      ·
        refine ⟨109728497838991047166109335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146304663785321396221479113 109728497838991047166109335)
        ·
          refine ⟨164592746758486570749164003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109728497838991047166109335 164592746758486570749164003)
          ·
            refine ⟨246889120137729856123746005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164592746758486570749164003 246889120137729856123746005)
            ·
              refine ⟨5786463753228043502900297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 246889120137729856123746005 5786463753228043502900297)
              ·
                refine ⟨4339847814921032627175223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786463753228043502900297 4339847814921032627175223)
                ·
                  refine ⟨6509771722381548940762835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4339847814921032627175223 6509771722381548940762835)
                  ·
                    refine ⟨9764657583572323411144253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509771722381548940762835 9764657583572323411144253)
                    ·
                      refine ⟨3661746593839621279179095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9764657583572323411144253 3661746593839621279179095)
                      ·
                        rfl

theorem cell23_7131226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_7131226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131226 prefixEnd_7131226 := by exact prefixLift 7131226
  have htrace : WordTrace (prefixWord ++ tailWord_7131226) baseStart_7131226 baseEnd_7131226 := by
    simpa [prefixWord, tailWord_7131226, baseEnd_7131226] using wordTrace_append hprefix tailTrace_7131226
  have hstable : (prefixWord ++ tailWord_7131226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131226).length < 2 ^ (prefixWord ++ tailWord_7131226).sum := by decide
  have hdescent : baseEnd_7131226 < baseStart_7131226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131235 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7131235 : Nat := 118140960795 + 7131235 * 2 ^ 59
def prefixEnd_7131235 : Nat := 4983230072969 + 3 ^ 40 * 7131235 * 2
def baseEnd_7131235 : Nat := 3661751215165511743966553

theorem tailTrace_7131235 : CollatzResearch.WordTrace tailWord_7131235 prefixEnd_7131235 3661751215165511743966553 := by
  unfold tailWord_7131235
  simp only [CollatzResearch.WordTrace]
  refine ⟨260097508319760987819707159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173398338879840658546471439 260097508319760987819707159)
  ·
    refine ⟨390146262479641481729560739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260097508319760987819707159 390146262479641481729560739)
    ·
      refine ⟨585219393719462222594341109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390146262479641481729560739 585219393719462222594341109)
      ·
        refine ⟨54864318161199583368219479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 585219393719462222594341109 54864318161199583368219479)
        ·
          refine ⟨82296477241799375052329219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54864318161199583368219479 82296477241799375052329219)
          ·
            refine ⟨123444715862699062578493829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82296477241799375052329219 123444715862699062578493829)
            ·
              refine ⟨23145884224256074233467593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123444715862699062578493829 23145884224256074233467593)
              ·
                refine ⟨17359413168192055675100695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23145884224256074233467593 17359413168192055675100695)
                ·
                  refine ⟨26039119752288083512651043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17359413168192055675100695 26039119752288083512651043)
                  ·
                    refine ⟨39058679628432125268976565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26039119752288083512651043 39058679628432125268976565)
                    ·
                      refine ⟨3661751215165511743966553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39058679628432125268976565 3661751215165511743966553)
                      ·
                        rfl

theorem cell23_7131235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7131235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131235 prefixEnd_7131235 := by exact prefixLift 7131235
  have htrace : WordTrace (prefixWord ++ tailWord_7131235) baseStart_7131235 baseEnd_7131235 := by
    simpa [prefixWord, tailWord_7131235, baseEnd_7131235] using wordTrace_append hprefix tailTrace_7131235
  have hstable : (prefixWord ++ tailWord_7131235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131235).length < 2 ^ (prefixWord ++ tailWord_7131235).sum := by decide
  have hdescent : baseEnd_7131235 < baseStart_7131235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131245 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7131245 : Nat := 118140960795 + 7131245 * 2 ^ 59
def prefixEnd_7131245 : Nat := 4983230072969 + 3 ^ 40 * 7131245 * 2
def baseEnd_7131245 : Nat := 3661756349972056704841507

theorem tailTrace_7131245 : CollatzResearch.WordTrace tailWord_7131245 prefixEnd_7131245 3661756349972056704841507 := by
  unfold tailWord_7131245
  simp only [CollatzResearch.WordTrace]
  refine ⟨260097873049724759527571189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173398582033149839685047459 260097873049724759527571189)
  ·
    refine ⟨24384175598411696205709799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260097873049724759527571189 24384175598411696205709799)
    ·
      refine ⟨36576263397617544308564699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24384175598411696205709799 36576263397617544308564699)
      ·
        refine ⟨54864395096426316462847049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36576263397617544308564699 54864395096426316462847049)
        ·
          refine ⟨41148296322319737347135287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54864395096426316462847049 41148296322319737347135287)
          ·
            refine ⟨61722444483479606020702931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41148296322319737347135287 61722444483479606020702931)
            ·
              refine ⟨92583666725219409031054397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61722444483479606020702931 92583666725219409031054397)
              ·
                refine ⟨34718875021957278386645399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92583666725219409031054397 34718875021957278386645399)
                ·
                  refine ⟨52078312532935917579968099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34718875021957278386645399 52078312532935917579968099)
                  ·
                    refine ⟨78117468799403876369952149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52078312532935917579968099 78117468799403876369952149)
                    ·
                      refine ⟨3661756349972056704841507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78117468799403876369952149 3661756349972056704841507)
                      ·
                        rfl

theorem cell23_7131245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7131245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131245 prefixEnd_7131245 := by exact prefixLift 7131245
  have htrace : WordTrace (prefixWord ++ tailWord_7131245) baseStart_7131245 baseEnd_7131245 := by
    simpa [prefixWord, tailWord_7131245, baseEnd_7131245] using wordTrace_append hprefix tailTrace_7131245
  have hstable : (prefixWord ++ tailWord_7131245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131245).length < 2 ^ (prefixWord ++ tailWord_7131245).sum := by decide
  have hdescent : baseEnd_7131245 < baseStart_7131245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131282 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7131282 : Nat := 118140960795 + 7131282 * 2 ^ 59
def prefixEnd_7131282 : Nat := 4983230072969 + 3 ^ 40 * 7131282 * 2
def baseEnd_7131282 : Nat := 3661775348756273060078837

theorem tailTrace_7131282 : CollatzResearch.WordTrace tailWord_7131282 prefixEnd_7131282 3661775348756273060078837 := by
  unfold tailWord_7131282
  simp only [CollatzResearch.WordTrace]
  refine ⟨65024805637647678711667025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173399481700393809897778733 65024805637647678711667025)
  ·
    refine ⟨48768604228235759033750269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65024805637647678711667025 48768604228235759033750269)
    ·
      refine ⟨18288226585588409637656351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48768604228235759033750269 18288226585588409637656351)
      ·
        refine ⟨27432339878382614456484527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18288226585588409637656351 27432339878382614456484527)
        ·
          refine ⟨41148509817573921684726791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27432339878382614456484527 41148509817573921684726791)
          ·
            refine ⟨61722764726360882527090187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41148509817573921684726791 61722764726360882527090187)
            ·
              refine ⟨92584147089541323790635281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61722764726360882527090187 92584147089541323790635281)
              ·
                refine ⟨69438110317155992842976461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92584147089541323790635281 69438110317155992842976461)
                ·
                  refine ⟨26039291368933497316116173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69438110317155992842976461 26039291368933497316116173)
                  ·
                    refine ⟨9764734263350061493543565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26039291368933497316116173 9764734263350061493543565)
                    ·
                      refine ⟨3661775348756273060078837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9764734263350061493543565 3661775348756273060078837)
                      ·
                        rfl

theorem cell23_7131282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7131282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131282 prefixEnd_7131282 := by exact prefixLift 7131282
  have htrace : WordTrace (prefixWord ++ tailWord_7131282) baseStart_7131282 baseEnd_7131282 := by
    simpa [prefixWord, tailWord_7131282, baseEnd_7131282] using wordTrace_append hprefix tailTrace_7131282
  have hstable : (prefixWord ++ tailWord_7131282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131282).length < 2 ^ (prefixWord ++ tailWord_7131282).sum := by decide
  have hdescent : baseEnd_7131282 < baseStart_7131282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131325 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7131325 : Nat := 118140960795 + 7131325 * 2 ^ 59
def prefixEnd_7131325 : Nat := 4983230072969 + 3 ^ 40 * 7131325 * 2
def baseEnd_7131325 : Nat := 3661797428424416391841139

theorem tailTrace_7131325 : CollatzResearch.WordTrace tailWord_7131325 prefixEnd_7131325 3661797428424416391841139 := by
  unfold tailWord_7131325
  simp only [CollatzResearch.WordTrace]
  refine ⟨260100790889434933190483429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173400527259623288793655619 260100790889434933190483429)
  ·
    refine ⟨48768898291769049973215643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260100790889434933190483429 48768898291769049973215643)
    ·
      refine ⟨73153347437653574959823465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48768898291769049973215643 73153347437653574959823465)
      ·
        refine ⟨54865010578240181219867599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73153347437653574959823465 54865010578240181219867599)
        ·
          refine ⟨82297515867360271829801399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54865010578240181219867599 82297515867360271829801399)
          ·
            refine ⟨123446273801040407744702099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82297515867360271829801399 123446273801040407744702099)
            ·
              refine ⟨185169410701560611617053149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123446273801040407744702099 185169410701560611617053149)
              ·
                refine ⟨69438529013085229356394931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185169410701560611617053149 69438529013085229356394931)
                ·
                  refine ⟨104157793519627844034592397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69438529013085229356394931 104157793519627844034592397)
                  ·
                    refine ⟨39059172569860441512972149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104157793519627844034592397 39059172569860441512972149)
                    ·
                      refine ⟨3661797428424416391841139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39059172569860441512972149 3661797428424416391841139)
                      ·
                        rfl

theorem cell23_7131325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7131325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131325 prefixEnd_7131325 := by exact prefixLift 7131325
  have htrace : WordTrace (prefixWord ++ tailWord_7131325) baseStart_7131325 baseEnd_7131325 := by
    simpa [prefixWord, tailWord_7131325, baseEnd_7131325] using wordTrace_append hprefix tailTrace_7131325
  have hstable : (prefixWord ++ tailWord_7131325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131325).length < 2 ^ (prefixWord ++ tailWord_7131325).sum := by decide
  have hdescent : baseEnd_7131325 < baseStart_7131325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131332 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7131332 : Nat := 118140960795 + 7131332 * 2 ^ 59
def prefixEnd_7131332 : Nat := 4983230072969 + 3 ^ 40 * 7131332 * 2
def baseEnd_7131332 : Nat := 1220600340929665954817869

theorem tailTrace_7131332 : CollatzResearch.WordTrace tailWord_7131332 prefixEnd_7131332 1220600340929665954817869 := by
  unfold tailWord_7131332
  simp only [CollatzResearch.WordTrace]
  refine ⟨130050523100204786692994125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173400697466939715590658833 130050523100204786692994125)
  ·
    refine ⟨48768946162576795009872797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130050523100204786692994125 48768946162576795009872797)
    ·
      refine ⟨18288354810966298128702299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48768946162576795009872797 18288354810966298128702299)
      ·
        refine ⟨27432532216449447193053449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18288354810966298128702299 27432532216449447193053449)
        ·
          refine ⟨20574399162337085394790087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27432532216449447193053449 20574399162337085394790087)
          ·
            refine ⟨30861598743505628092185131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574399162337085394790087 30861598743505628092185131)
            ·
              refine ⟨46292398115258442138277697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30861598743505628092185131 46292398115258442138277697)
              ·
                refine ⟨34719298586443831603708273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46292398115258442138277697 34719298586443831603708273)
                ·
                  refine ⟨26039473939832873702781205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34719298586443831603708273 26039473939832873702781205)
                  ·
                    refine ⟨1220600340929665954817869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26039473939832873702781205 1220600340929665954817869)
                    ·
                      rfl

theorem cell23_7131332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7131332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131332 prefixEnd_7131332 := by exact prefixLift 7131332
  have htrace : WordTrace (prefixWord ++ tailWord_7131332) baseStart_7131332 baseEnd_7131332 := by
    simpa [prefixWord, tailWord_7131332, baseEnd_7131332] using wordTrace_append hprefix tailTrace_7131332
  have hstable : (prefixWord ++ tailWord_7131332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131332).length < 2 ^ (prefixWord ++ tailWord_7131332).sum := by decide
  have hdescent : baseEnd_7131332 < baseStart_7131332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131339 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 4, 2, 2]
def baseStart_7131339 : Nat := 118140960795 + 7131339 * 2 ^ 59
def prefixEnd_7131339 : Nat := 4983230072969 + 3 ^ 40 * 7131339 * 2
def baseEnd_7131339 : Nat := 3661804617153579337066075

theorem tailTrace_7131339 : CollatzResearch.WordTrace tailWord_7131339 prefixEnd_7131339 3661804617153579337066075 := by
  unfold tailWord_7131339
  simp only [CollatzResearch.WordTrace]
  refine ⟨260101301511384213581493071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173400867674256142387662047 260101301511384213581493071)
  ·
    refine ⟨390151952267076320372239607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260101301511384213581493071 390151952267076320372239607)
    ·
      refine ⟨585227928400614480558359411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390151952267076320372239607 585227928400614480558359411)
      ·
        refine ⟨877841892600921720837539117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585227928400614480558359411 877841892600921720837539117)
        ·
          refine ⟨329190709725345645314077169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877841892600921720837539117 329190709725345645314077169)
          ·
            refine ⟨246893032294009233985557877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329190709725345645314077169 246893032294009233985557877)
            ·
              refine ⟨23146221777563365686146051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246893032294009233985557877 23146221777563365686146051)
              ·
                refine ⟨34719332666345048529219077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23146221777563365686146051 34719332666345048529219077)
                ·
                  refine ⟨6509874874939696599228577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34719332666345048529219077 6509874874939696599228577)
                  ·
                    refine ⟨4882406156204772449421433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509874874939696599228577 4882406156204772449421433)
                    ·
                      refine ⟨3661804617153579337066075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882406156204772449421433 3661804617153579337066075)
                      ·
                        rfl

theorem cell23_7131339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2, 2].length) (baseStart_7131339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131339 prefixEnd_7131339 := by exact prefixLift 7131339
  have htrace : WordTrace (prefixWord ++ tailWord_7131339) baseStart_7131339 baseEnd_7131339 := by
    simpa [prefixWord, tailWord_7131339, baseEnd_7131339] using wordTrace_append hprefix tailTrace_7131339
  have hstable : (prefixWord ++ tailWord_7131339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131339).length < 2 ^ (prefixWord ++ tailWord_7131339).sum := by decide
  have hdescent : baseEnd_7131339 < baseStart_7131339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131345 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 7]
def baseStart_7131345 : Nat := 118140960795 + 7131345 * 2 ^ 59
def prefixEnd_7131345 : Nat := 4983230072969 + 3 ^ 40 * 7131345 * 2
def baseEnd_7131345 : Nat := 406867522004167368176783

theorem tailTrace_7131345 : CollatzResearch.WordTrace tailWord_7131345 prefixEnd_7131345 406867522004167368176783 := by
  unfold tailWord_7131345
  simp only [CollatzResearch.WordTrace]
  refine ⟨260101520349362476606211489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173401013566241651070807659 260101520349362476606211489)
  ·
    refine ⟨195076140262021857454658617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260101520349362476606211489 195076140262021857454658617)
    ·
      refine ⟨146307105196516393090993963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195076140262021857454658617 146307105196516393090993963)
      ·
        refine ⟨219460657794774589636490945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146307105196516393090993963 219460657794774589636490945)
        ·
          refine ⟨164595493346080942227368209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219460657794774589636490945 164595493346080942227368209)
          ·
            refine ⟨123446620009560706670526157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164595493346080942227368209 123446620009560706670526157)
            ·
              refine ⟨46292482503585265001447309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123446620009560706670526157 46292482503585265001447309)
              ·
                refine ⟨17359680938844474375542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46292482503585265001447309 17359680938844474375542741)
                ·
                  refine ⟨406867522004167368176783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17359680938844474375542741 406867522004167368176783)
                  ·
                    rfl

theorem cell23_7131345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_7131345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131345 prefixEnd_7131345 := by exact prefixLift 7131345
  have htrace : WordTrace (prefixWord ++ tailWord_7131345) baseStart_7131345 baseEnd_7131345 := by
    simpa [prefixWord, tailWord_7131345, baseEnd_7131345] using wordTrace_append hprefix tailTrace_7131345
  have hstable : (prefixWord ++ tailWord_7131345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131345).length < 2 ^ (prefixWord ++ tailWord_7131345).sum := by decide
  have hdescent : baseEnd_7131345 < baseStart_7131345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131350 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7131350 : Nat := 118140960795 + 7131350 * 2 ^ 59
def prefixEnd_7131350 : Nat := 4983230072969 + 3 ^ 40 * 7131350 * 2
def baseEnd_7131350 : Nat := 3661810265440778794028525

theorem tailTrace_7131350 : CollatzResearch.WordTrace tailWord_7131350 prefixEnd_7131350 3661810265440778794028525 := by
  unfold tailWord_7131350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16256356419646522653758969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173401135142896241640095669 16256356419646522653758969)
  ·
    refine ⟨12192267314734891990319227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16256356419646522653758969 12192267314734891990319227)
    ·
      refine ⟨18288400972102337985478841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12192267314734891990319227 18288400972102337985478841)
      ·
        refine ⟨13716300729076753489109131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18288400972102337985478841 13716300729076753489109131)
        ·
          refine ⟨20574451093615130233663697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716300729076753489109131 20574451093615130233663697)
          ·
            refine ⟨15430838320211347675247773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20574451093615130233663697 15430838320211347675247773)
            ·
              refine ⟨5786564370079255378217915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15430838320211347675247773 5786564370079255378217915)
              ·
                refine ⟨8679846555118883067326873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786564370079255378217915 8679846555118883067326873)
                ·
                  refine ⟨6509884916339162300495155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679846555118883067326873 6509884916339162300495155)
                  ·
                    refine ⟨9764827374508743450742733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509884916339162300495155 9764827374508743450742733)
                    ·
                      refine ⟨3661810265440778794028525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9764827374508743450742733 3661810265440778794028525)
                      ·
                        rfl

theorem cell23_7131350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7131350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131350 prefixEnd_7131350 := by exact prefixLift 7131350
  have htrace : WordTrace (prefixWord ++ tailWord_7131350) baseStart_7131350 baseEnd_7131350 := by
    simpa [prefixWord, tailWord_7131350, baseEnd_7131350] using wordTrace_append hprefix tailTrace_7131350
  have hstable : (prefixWord ++ tailWord_7131350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131350).length < 2 ^ (prefixWord ++ tailWord_7131350).sum := by decide
  have hdescent : baseEnd_7131350 < baseStart_7131350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131352 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7131352 : Nat := 118140960795 + 7131352 * 2 ^ 59
def prefixEnd_7131352 : Nat := 4983230072969 + 3 ^ 40 * 7131352 * 2
def baseEnd_7131352 : Nat := 3661811292402087786203515

theorem tailTrace_7131352 : CollatzResearch.WordTrace tailWord_7131352 prefixEnd_7131352 3661811292402087786203515 := by
  unfold tailWord_7131352
  simp only [CollatzResearch.WordTrace]
  refine ⟨130050887830168558400858155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173401183773558077867810873 130050887830168558400858155)
  ·
    refine ⟨195076331745252837601287233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130050887830168558400858155 195076331745252837601287233)
    ·
      refine ⟨146307248808939628200965425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195076331745252837601287233 146307248808939628200965425)
      ·
        refine ⟨109730436606704721150724069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146307248808939628200965425 109730436606704721150724069)
        ·
          refine ⟨20574456863757135215760763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109730436606704721150724069 20574456863757135215760763)
          ·
            refine ⟨30861685295635702823641145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574456863757135215760763 30861685295635702823641145)
            ·
              refine ⟨23146263971726777117730859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30861685295635702823641145 23146263971726777117730859)
              ·
                refine ⟨34719395957590165676596289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23146263971726777117730859 34719395957590165676596289)
                ·
                  refine ⟨26039546968192624257447217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34719395957590165676596289 26039546968192624257447217)
                  ·
                    refine ⟨19529660226144468193085413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26039546968192624257447217 19529660226144468193085413)
                    ·
                      refine ⟨3661811292402087786203515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19529660226144468193085413 3661811292402087786203515)
                      ·
                        rfl

theorem cell23_7131352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7131352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131352 prefixEnd_7131352 := by exact prefixLift 7131352
  have htrace : WordTrace (prefixWord ++ tailWord_7131352) baseStart_7131352 baseEnd_7131352 := by
    simpa [prefixWord, tailWord_7131352, baseEnd_7131352] using wordTrace_append hprefix tailTrace_7131352
  have hstable : (prefixWord ++ tailWord_7131352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131352).length < 2 ^ (prefixWord ++ tailWord_7131352).sum := by decide
  have hdescent : baseEnd_7131352 < baseStart_7131352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131396 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 7]
def baseStart_7131396 : Nat := 118140960795 + 7131396 * 2 ^ 59
def prefixEnd_7131396 : Nat := 4983230072969 + 3 ^ 40 * 7131396 * 2
def baseEnd_7131396 : Nat := 406870431727876179339257

theorem tailTrace_7131396 : CollatzResearch.WordTrace tailWord_7131396 prefixEnd_7131396 406870431727876179339257 := by
  unfold tailWord_7131396
  simp only [CollatzResearch.WordTrace]
  refine ⟨130051690236088856158159021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173402253648118474877545361 130051690236088856158159021)
  ·
    refine ⟨48769383838533321059309633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130051690236088856158159021 48769383838533321059309633)
    ·
      refine ⟨36577037878899990794482225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48769383838533321059309633 36577037878899990794482225)
      ·
        refine ⟨27432778409174993095861669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36577037878899990794482225 27432778409174993095861669)
        ·
          refine ⟨5143645951720311205474063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27432778409174993095861669 5143645951720311205474063)
          ·
            refine ⟨7715468927580466808211095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143645951720311205474063 7715468927580466808211095)
            ·
              refine ⟨11573203391370700212316643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715468927580466808211095 11573203391370700212316643)
              ·
                refine ⟨17359805087056050318474965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11573203391370700212316643 17359805087056050318474965)
                ·
                  refine ⟨406870431727876179339257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17359805087056050318474965 406870431727876179339257)
                  ·
                    rfl

theorem cell23_7131396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_7131396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131396 prefixEnd_7131396 := by exact prefixLift 7131396
  have htrace : WordTrace (prefixWord ++ tailWord_7131396) baseStart_7131396 baseEnd_7131396 := by
    simpa [prefixWord, tailWord_7131396, baseEnd_7131396] using wordTrace_append hprefix tailTrace_7131396
  have hstable : (prefixWord ++ tailWord_7131396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131396).length < 2 ^ (prefixWord ++ tailWord_7131396).sum := by decide
  have hdescent : baseEnd_7131396 < baseStart_7131396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131529 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_7131529 : Nat := 118140960795 + 7131529 * 2 ^ 59
def prefixEnd_7131529 : Nat := 4983230072969 + 3 ^ 40 * 7131529 * 2
def baseEnd_7131529 : Nat := 1220634059492644531230067

theorem tailTrace_7131529 : CollatzResearch.WordTrace tailWord_7131529 prefixEnd_7131529 1220634059492644531230067 := by
  unfold tailWord_7131529
  simp only [CollatzResearch.WordTrace]
  refine ⟨260108231380695876030909641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173405487587130584020606427 260108231380695876030909641)
  ·
    refine ⟨195081173535521907023182231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260108231380695876030909641 195081173535521907023182231)
    ·
      refine ⟨292621760303282860534773347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195081173535521907023182231 292621760303282860534773347)
      ·
        refine ⟨438932640454924290802160021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292621760303282860534773347 438932640454924290802160021)
        ·
          refine ⟨20574967521324576131351251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 438932640454924290802160021 20574967521324576131351251)
          ·
            refine ⟨30862451281986864197026877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574967521324576131351251 30862451281986864197026877)
            ·
              refine ⟨11573419230745074073885079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30862451281986864197026877 11573419230745074073885079)
              ·
                refine ⟨17360128846117611110827619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11573419230745074073885079 17360128846117611110827619)
                ·
                  refine ⟨26040193269176416666241429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17360128846117611110827619 26040193269176416666241429)
                  ·
                    refine ⟨1220634059492644531230067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26040193269176416666241429 1220634059492644531230067)
                    ·
                      rfl

theorem cell23_7131529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_7131529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131529 prefixEnd_7131529 := by exact prefixLift 7131529
  have htrace : WordTrace (prefixWord ++ tailWord_7131529) baseStart_7131529 baseEnd_7131529 := by
    simpa [prefixWord, tailWord_7131529, baseEnd_7131529] using wordTrace_append hprefix tailTrace_7131529
  have hstable : (prefixWord ++ tailWord_7131529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131529).length < 2 ^ (prefixWord ++ tailWord_7131529).sum := by decide
  have hdescent : baseEnd_7131529 < baseStart_7131529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131556 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_7131556 : Nat := 118140960795 + 7131556 * 2 ^ 59
def prefixEnd_7131556 : Nat := 4983230072969 + 3 ^ 40 * 7131556 * 2
def baseEnd_7131556 : Nat := 3661916042455604988052577

theorem tailTrace_7131556 : CollatzResearch.WordTrace tailWord_7131556 prefixEnd_7131556 3661916042455604988052577 := by
  unfold tailWord_7131556
  simp only [CollatzResearch.WordTrace]
  refine ⟨130054608075799029821071261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173406144101065373094761681 130054608075799029821071261)
  ·
    refine ⟨48770478028424636182901723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130054608075799029821071261 48770478028424636182901723)
    ·
      refine ⟨73155717042636954274352585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48770478028424636182901723 73155717042636954274352585)
      ·
        refine ⟨54866787781977715705764439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73155717042636954274352585 54866787781977715705764439)
        ·
          refine ⟨82300181672966573558646659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54866787781977715705764439 82300181672966573558646659)
          ·
            refine ⟨123450272509449860337969989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82300181672966573558646659 123450272509449860337969989)
            ·
              refine ⟨23146926095521848813369373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123450272509449860337969989 23146926095521848813369373)
              ·
                refine ⟨8680097285820693305013515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23146926095521848813369373 8680097285820693305013515)
                ·
                  refine ⟨13020145928731039957520273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680097285820693305013515 13020145928731039957520273)
                  ·
                    refine ⟨9765109446548279968140205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13020145928731039957520273 9765109446548279968140205)
                    ·
                      refine ⟨3661916042455604988052577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765109446548279968140205 3661916042455604988052577)
                      ·
                        rfl

theorem cell23_7131556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_7131556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131556 prefixEnd_7131556 := by exact prefixLift 7131556
  have htrace : WordTrace (prefixWord ++ tailWord_7131556) baseStart_7131556 baseEnd_7131556 := by
    simpa [prefixWord, tailWord_7131556, baseEnd_7131556] using wordTrace_append hprefix tailTrace_7131556
  have hstable : (prefixWord ++ tailWord_7131556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131556).length < 2 ^ (prefixWord ++ tailWord_7131556).sum := by decide
  have hdescent : baseEnd_7131556 < baseStart_7131556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131559 : List Nat := [1, 1, 6, 1, 1, 4, 9]
def baseStart_7131559 : Nat := 118140960795 + 7131559 * 2 ^ 59
def prefixEnd_7131559 : Nat := 4983230072969 + 3 ^ 40 * 7131559 * 2
def baseEnd_7131559 : Nat := 45208859048118129337223

theorem tailTrace_7131559 : CollatzResearch.WordTrace tailWord_7131559 prefixEnd_7131559 45208859048118129337223 := by
  unfold tailWord_7131559
  simp only [CollatzResearch.WordTrace]
  refine ⟨260109325570587191154501731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173406217047058127436334487 260109325570587191154501731)
  ·
    refine ⟨390163988355880786731752597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260109325570587191154501731 390163988355880786731752597)
    ·
      refine ⟨18288936954181911878050903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 390163988355880786731752597 18288936954181911878050903)
      ·
        refine ⟨27433405431272867817076355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18288936954181911878050903 27433405431272867817076355)
        ·
          refine ⟨41150108146909301725614533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27433405431272867817076355 41150108146909301725614533)
          ·
            refine ⟨7715645277545494073552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41150108146909301725614533 7715645277545494073552725)
            ·
              refine ⟨45208859048118129337223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7715645277545494073552725 45208859048118129337223)
              ·
                rfl

theorem cell23_7131559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 9].length) (baseStart_7131559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131559 prefixEnd_7131559 := by exact prefixLift 7131559
  have htrace : WordTrace (prefixWord ++ tailWord_7131559) baseStart_7131559 baseEnd_7131559 := by
    simpa [prefixWord, tailWord_7131559, baseEnd_7131559] using wordTrace_append hprefix tailTrace_7131559
  have hstable : (prefixWord ++ tailWord_7131559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131559).length < 2 ^ (prefixWord ++ tailWord_7131559).sum := by decide
  have hdescent : baseEnd_7131559 < baseStart_7131559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131580 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_7131580 : Nat := 118140960795 + 7131580 * 2 ^ 59
def prefixEnd_7131580 : Nat := 4983230072969 + 3 ^ 40 * 7131580 * 2
def baseEnd_7131580 : Nat := 1220642788663770964717489

theorem tailTrace_7131580 : CollatzResearch.WordTrace tailWord_7131580 prefixEnd_7131580 1220642788663770964717489 := by
  unfold tailWord_7131580
  simp only [CollatzResearch.WordTrace]
  refine ⟨130055045751755555870508097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173406727669007407827344129 130055045751755555870508097)
  ·
    refine ⟨97541284313816666902881073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130055045751755555870508097 97541284313816666902881073)
    ·
      refine ⟨73155963235362500177160805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97541284313816666902881073 73155963235362500177160805)
      ·
        refine ⟨13716743106630468783217651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73155963235362500177160805 13716743106630468783217651)
        ·
          refine ⟨20575114659945703174826477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13716743106630468783217651 20575114659945703174826477)
          ·
            refine ⟨7715667997479638690559929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20575114659945703174826477 7715667997479638690559929)
            ·
              refine ⟨5786750998109729017919947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715667997479638690559929 5786750998109729017919947)
              ·
                refine ⟨8680126497164593526879921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786750998109729017919947 8680126497164593526879921)
                ·
                  refine ⟨6510094872873445145159941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680126497164593526879921 6510094872873445145159941)
                  ·
                    refine ⟨1220642788663770964717489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510094872873445145159941 1220642788663770964717489)
                    ·
                      rfl

theorem cell23_7131580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_7131580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131580 prefixEnd_7131580 := by exact prefixLift 7131580
  have htrace : WordTrace (prefixWord ++ tailWord_7131580) baseStart_7131580 baseEnd_7131580 := by
    simpa [prefixWord, tailWord_7131580, baseEnd_7131580] using wordTrace_append hprefix tailTrace_7131580
  have hstable : (prefixWord ++ tailWord_7131580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131580).length < 2 ^ (prefixWord ++ tailWord_7131580).sum := by decide
  have hdescent : baseEnd_7131580 < baseStart_7131580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131621 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7131621 : Nat := 118140960795 + 7131621 * 2 ^ 59
def prefixEnd_7131621 : Nat := 4983230072969 + 3 ^ 40 * 7131621 * 2
def baseEnd_7131621 : Nat := 3661949418698147233739779

theorem tailTrace_7131621 : CollatzResearch.WordTrace tailWord_7131621 prefixEnd_7131621 3661949418698147233739779 := by
  unfold tailWord_7131621
  simp only [CollatzResearch.WordTrace]
  refine ⟨260111586896362575743258717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173407724597575050495505811 260111586896362575743258717)
  ·
    refine ⟨97541845086135965903722019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260111586896362575743258717 97541845086135965903722019)
    ·
      refine ⟨146312767629203948855583029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97541845086135965903722019 146312767629203948855583029)
      ·
        refine ⟨13716821965237870205210909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146312767629203948855583029 13716821965237870205210909)
        ·
          refine ⟨5143808236964201326954091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13716821965237870205210909 5143808236964201326954091)
          ·
            refine ⟨7715712355446301990431137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143808236964201326954091 7715712355446301990431137)
            ·
              refine ⟨5786784266584726492823353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715712355446301990431137 5786784266584726492823353)
              ·
                refine ⟨4340088199938544869617515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786784266584726492823353 4340088199938544869617515)
                ·
                  refine ⟨6510132299907817304426273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340088199938544869617515 6510132299907817304426273)
                  ·
                    refine ⟨4882599224930862978319705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510132299907817304426273 4882599224930862978319705)
                    ·
                      refine ⟨3661949418698147233739779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882599224930862978319705 3661949418698147233739779)
                      ·
                        rfl

theorem cell23_7131621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7131621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131621 prefixEnd_7131621 := by exact prefixLift 7131621
  have htrace : WordTrace (prefixWord ++ tailWord_7131621) baseStart_7131621 baseEnd_7131621 := by
    simpa [prefixWord, tailWord_7131621, baseEnd_7131621] using wordTrace_append hprefix tailTrace_7131621
  have hstable : (prefixWord ++ tailWord_7131621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131621).length < 2 ^ (prefixWord ++ tailWord_7131621).sum := by decide
  have hdescent : baseEnd_7131621 < baseStart_7131621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131649 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 9]
def baseStart_7131649 : Nat := 118140960795 + 7131649 * 2 ^ 59
def prefixEnd_7131649 : Nat := 4983230072969 + 3 ^ 40 * 7131649 * 2
def baseEnd_7131649 : Nat := 406884866239608124909961

theorem tailTrace_7131649 : CollatzResearch.WordTrace tailWord_7131649 prefixEnd_7131649 406884866239608124909961 := by
  unfold tailWord_7131649
  simp only [CollatzResearch.WordTrace]
  refine ⟨260112608140261136525278001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173408405426840757683518667 260112608140261136525278001)
  ·
    refine ⟨195084456105195852393958501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260112608140261136525278001 195084456105195852393958501)
    ·
      refine ⟨36578335519724222323867219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195084456105195852393958501 36578335519724222323867219)
      ·
        refine ⟨54867503279586333485800829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36578335519724222323867219 54867503279586333485800829)
        ·
          refine ⟨20575313729844875057175311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54867503279586333485800829 20575313729844875057175311)
          ·
            refine ⟨30862970594767312585762967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20575313729844875057175311 30862970594767312585762967)
            ·
              refine ⟨46294455892150968878644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30862970594767312585762967 46294455892150968878644451)
              ·
                refine ⟨69441683838226453317966677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46294455892150968878644451 69441683838226453317966677)
                ·
                  refine ⟨406884866239608124909961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69441683838226453317966677 406884866239608124909961)
                  ·
                    rfl

theorem cell23_7131649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_7131649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131649 prefixEnd_7131649 := by exact prefixLift 7131649
  have htrace : WordTrace (prefixWord ++ tailWord_7131649) baseStart_7131649 baseEnd_7131649 := by
    simpa [prefixWord, tailWord_7131649, baseEnd_7131649] using wordTrace_append hprefix tailTrace_7131649
  have hstable : (prefixWord ++ tailWord_7131649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131649).length < 2 ^ (prefixWord ++ tailWord_7131649).sum := by decide
  have hdescent : baseEnd_7131649 < baseStart_7131649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131676 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7131676 : Nat := 118140960795 + 7131676 * 2 ^ 59
def prefixEnd_7131676 : Nat := 4983230072969 + 3 ^ 40 * 7131676 * 2
def baseEnd_7131676 : Nat := 3661977660134144518552025

theorem tailTrace_7131676 : CollatzResearch.WordTrace tailWord_7131676 prefixEnd_7131676 3661977660134144518552025 := by
  unfold tailWord_7131676
  simp only [CollatzResearch.WordTrace]
  refine ⟨130056796455581660068255441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173409061940775546757673921 130056796455581660068255441)
  ·
    refine ⟨97542597341686245051191581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130056796455581660068255441 97542597341686245051191581)
    ·
      refine ⟨36578474003132341894196843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97542597341686245051191581 36578474003132341894196843)
      ·
        refine ⟨54867711004698512841295265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36578474003132341894196843 54867711004698512841295265)
        ·
          refine ⟨41150783253523884630971449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54867711004698512841295265 41150783253523884630971449)
          ·
            refine ⟨30863087440142913473228587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41150783253523884630971449 30863087440142913473228587)
            ·
              refine ⟨46294631160214370209842881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30863087440142913473228587 46294631160214370209842881)
              ·
                refine ⟨34720973370160777657382161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46294631160214370209842881 34720973370160777657382161)
                ·
                  refine ⟨26040730027620583243036621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34720973370160777657382161 26040730027620583243036621)
                  ·
                    refine ⟨9765273760357718716138733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26040730027620583243036621 9765273760357718716138733)
                    ·
                      refine ⟨3661977660134144518552025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765273760357718716138733 3661977660134144518552025)
                      ·
                        rfl

theorem cell23_7131676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7131676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131676 prefixEnd_7131676 := by exact prefixLift 7131676
  have htrace : WordTrace (prefixWord ++ tailWord_7131676) baseStart_7131676 baseEnd_7131676 := by
    simpa [prefixWord, tailWord_7131676, baseEnd_7131676] using wordTrace_append hprefix tailTrace_7131676
  have hstable : (prefixWord ++ tailWord_7131676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131676).length < 2 ^ (prefixWord ++ tailWord_7131676).sum := by decide
  have hdescent : baseEnd_7131676 < baseStart_7131676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131677 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7131677 : Nat := 118140960795 + 7131677 * 2 ^ 59
def prefixEnd_7131677 : Nat := 4983230072969 + 3 ^ 40 * 7131677 * 2
def baseEnd_7131677 : Nat := 3661978173614799014639521

theorem tailTrace_7131677 : CollatzResearch.WordTrace tailWord_7131677 prefixEnd_7131677 3661978173614799014639521 := by
  unfold tailWord_7131677
  simp only [CollatzResearch.WordTrace]
  refine ⟨260113629384159697307297285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173409086256106464871531523 260113629384159697307297285)
  ·
    refine ⟨48771305509529943245118241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260113629384159697307297285 48771305509529943245118241)
    ·
      refine ⟨36578479132147457433838681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48771305509529943245118241 36578479132147457433838681)
      ·
        refine ⟨27433859349110593075379011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36578479132147457433838681 27433859349110593075379011)
        ·
          refine ⟨41150789023665889613068517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27433859349110593075379011 41150789023665889613068517)
          ·
            refine ⟨7715772941937354302450347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41150789023665889613068517 7715772941937354302450347)
            ·
              refine ⟨11573659412906031453675521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715772941937354302450347 11573659412906031453675521)
              ·
                refine ⟨8680244559679523590256641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11573659412906031453675521 8680244559679523590256641)
                ·
                  refine ⟨6510183419759642692692481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680244559679523590256641 6510183419759642692692481)
                  ·
                    refine ⟨4882637564819732019519361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510183419759642692692481 4882637564819732019519361)
                    ·
                      refine ⟨3661978173614799014639521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882637564819732019519361 3661978173614799014639521)
                      ·
                        rfl

theorem cell23_7131677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7131677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131677 prefixEnd_7131677 := by exact prefixLift 7131677
  have htrace : WordTrace (prefixWord ++ tailWord_7131677) baseStart_7131677 baseEnd_7131677 := by
    simpa [prefixWord, tailWord_7131677, baseEnd_7131677] using wordTrace_append hprefix tailTrace_7131677
  have hstable : (prefixWord ++ tailWord_7131677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131677).length < 2 ^ (prefixWord ++ tailWord_7131677).sum := by decide
  have hdescent : baseEnd_7131677 < baseStart_7131677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131679 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 4, 5]
def baseStart_7131679 : Nat := 118140960795 + 7131679 * 2 ^ 59
def prefixEnd_7131679 : Nat := 4983230072969 + 3 ^ 40 * 7131679 * 2
def baseEnd_7131679 : Nat := 1220659733525369335604837

theorem tailTrace_7131679 : CollatzResearch.WordTrace tailWord_7131679 prefixEnd_7131679 1220659733525369335604837 := by
  unfold tailWord_7131679
  simp only [CollatzResearch.WordTrace]
  refine ⟨260113702330152451648870091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173409134886768301099246727 260113702330152451648870091)
  ·
    refine ⟨390170553495228677473305137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260113702330152451648870091 390170553495228677473305137)
    ·
      refine ⟨292627915121421508104978853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390170553495228677473305137 292627915121421508104978853)
      ·
        refine ⟨54867734085266532769683535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292627915121421508104978853 54867734085266532769683535)
        ·
          refine ⟨82301601127899799154525303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54867734085266532769683535 82301601127899799154525303)
          ·
            refine ⟨123452401691849698731787955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82301601127899799154525303 123452401691849698731787955)
            ·
              refine ⟨185178602537774548097681933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123452401691849698731787955 185178602537774548097681933)
              ·
                refine ⟨69441975951665455536630725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185178602537774548097681933 69441975951665455536630725)
                ·
                  refine ⟨13020370490937272913118261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69441975951665455536630725 13020370490937272913118261)
                  ·
                    refine ⟨1220659733525369335604837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13020370490937272913118261 1220659733525369335604837)
                    ·
                      rfl

theorem cell23_7131679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_7131679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131679 prefixEnd_7131679 := by exact prefixLift 7131679
  have htrace : WordTrace (prefixWord ++ tailWord_7131679) baseStart_7131679 baseEnd_7131679 := by
    simpa [prefixWord, tailWord_7131679, baseEnd_7131679] using wordTrace_append hprefix tailTrace_7131679
  have hstable : (prefixWord ++ tailWord_7131679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131679).length < 2 ^ (prefixWord ++ tailWord_7131679).sum := by decide
  have hdescent : baseEnd_7131679 < baseStart_7131679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131694 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7131694 : Nat := 118140960795 + 7131694 * 2 ^ 59
def prefixEnd_7131694 : Nat := 4983230072969 + 3 ^ 40 * 7131694 * 2
def baseEnd_7131694 : Nat := 3661986902785925448126943

theorem tailTrace_7131694 : CollatzResearch.WordTrace tailWord_7131694 prefixEnd_7131694 3661986902785925448126943 := by
  unfold tailWord_7131694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514281178137263651333267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173409499616732072807110757 32514281178137263651333267)
  ·
    refine ⟨48771421767205895476999901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514281178137263651333267 48771421767205895476999901)
    ·
      refine ⟨18289283162702210803874963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48771421767205895476999901 18289283162702210803874963)
      ·
        refine ⟨27433924744053316205812445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18289283162702210803874963 27433924744053316205812445)
        ·
          refine ⟨10287721779019993577179667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27433924744053316205812445 10287721779019993577179667)
          ·
            refine ⟨15431582668529990365769501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287721779019993577179667 15431582668529990365769501)
            ·
              refine ⟨5786843500698746387163563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15431582668529990365769501 5786843500698746387163563)
              ·
                refine ⟨8680265251048119580745345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786843500698746387163563 8680265251048119580745345)
                ·
                  refine ⟨6510198938286089685559009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680265251048119580745345 6510198938286089685559009)
                  ·
                    refine ⟨4882649203714567264169257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510198938286089685559009 4882649203714567264169257)
                    ·
                      refine ⟨3661986902785925448126943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882649203714567264169257 3661986902785925448126943)
                      ·
                        rfl

theorem cell23_7131694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7131694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131694 prefixEnd_7131694 := by exact prefixLift 7131694
  have htrace : WordTrace (prefixWord ++ tailWord_7131694) baseStart_7131694 baseEnd_7131694 := by
    simpa [prefixWord, tailWord_7131694, baseEnd_7131694] using wordTrace_append hprefix tailTrace_7131694
  have hstable : (prefixWord ++ tailWord_7131694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131694).length < 2 ^ (prefixWord ++ tailWord_7131694).sum := by decide
  have hdescent : baseEnd_7131694 < baseStart_7131694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131699 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_7131699 : Nat := 118140960795 + 7131699 * 2 ^ 59
def prefixEnd_7131699 : Nat := 4983230072969 + 3 ^ 40 * 7131699 * 2
def baseEnd_7131699 : Nat := 3661989470189197928564419

theorem tailTrace_7131699 : CollatzResearch.WordTrace tailWord_7131699 prefixEnd_7131699 3661989470189197928564419 := by
  unfold tailWord_7131699
  simp only [CollatzResearch.WordTrace]
  refine ⟨260114431790079995064598151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173409621193386663376398767 260114431790079995064598151)
  ·
    refine ⟨390171647685119992596897227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260114431790079995064598151 390171647685119992596897227)
    ·
      refine ⟨585257471527679988895345841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390171647685119992596897227 585257471527679988895345841)
      ·
        refine ⟨438943103645759991671509381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585257471527679988895345841 438943103645759991671509381)
        ·
          refine ⟨82301831933579998438408009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438943103645759991671509381 82301831933579998438408009)
          ·
            refine ⟨61726373950184998828806007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82301831933579998438408009 61726373950184998828806007)
            ·
              refine ⟨92589560925277498243209011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61726373950184998828806007 92589560925277498243209011)
              ·
                refine ⟨138884341387916247364813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92589560925277498243209011 138884341387916247364813517)
                ·
                  refine ⟨52081628020468592761805069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138884341387916247364813517 52081628020468592761805069)
                  ·
                    refine ⟨19530610507675722285676901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52081628020468592761805069 19530610507675722285676901)
                    ·
                      refine ⟨3661989470189197928564419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19530610507675722285676901 3661989470189197928564419)
                      ·
                        rfl

theorem cell23_7131699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_7131699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131699 prefixEnd_7131699 := by exact prefixLift 7131699
  have htrace : WordTrace (prefixWord ++ tailWord_7131699) baseStart_7131699 baseEnd_7131699 := by
    simpa [prefixWord, tailWord_7131699, baseEnd_7131699] using wordTrace_append hprefix tailTrace_7131699
  have hstable : (prefixWord ++ tailWord_7131699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131699).length < 2 ^ (prefixWord ++ tailWord_7131699).sum := by decide
  have hdescent : baseEnd_7131699 < baseStart_7131699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131726 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_7131726 : Nat := 118140960795 + 7131726 * 2 ^ 59
def prefixEnd_7131726 : Nat := 4983230072969 + 3 ^ 40 * 7131726 * 2
def baseEnd_7131726 : Nat := 1220667778055623107642265

theorem tailTrace_7131726 : CollatzResearch.WordTrace tailWord_7131726 prefixEnd_7131726 1220667778055623107642265 := by
  unfold tailWord_7131726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514427070122772334478879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173410277707321452450554021 32514427070122772334478879)
  ·
    refine ⟨48771640605184158501718319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514427070122772334478879 48771640605184158501718319)
    ·
      refine ⟨73157460907776237752577479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48771640605184158501718319 73157460907776237752577479)
      ·
        refine ⟨109736191361664356628866219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73157460907776237752577479 109736191361664356628866219)
        ·
          refine ⟨164604287042496534943299329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109736191361664356628866219 164604287042496534943299329)
          ·
            refine ⟨123453215281872401207474497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164604287042496534943299329 123453215281872401207474497)
            ·
              refine ⟨92589911461404300905605873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123453215281872401207474497 92589911461404300905605873)
              ·
                refine ⟨69442433596053225679204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92589911461404300905605873 69442433596053225679204405)
                ·
                  refine ⟨6510228149629989907425413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69442433596053225679204405 6510228149629989907425413)
                  ·
                    refine ⟨1220667778055623107642265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510228149629989907425413 1220667778055623107642265)
                    ·
                      rfl

theorem cell23_7131726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_7131726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131726 prefixEnd_7131726 := by exact prefixLift 7131726
  have htrace : WordTrace (prefixWord ++ tailWord_7131726) baseStart_7131726 baseEnd_7131726 := by
    simpa [prefixWord, tailWord_7131726, baseEnd_7131726] using wordTrace_append hprefix tailTrace_7131726
  have hstable : (prefixWord ++ tailWord_7131726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131726).length < 2 ^ (prefixWord ++ tailWord_7131726).sum := by decide
  have hdescent : baseEnd_7131726 < baseStart_7131726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131736 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7131736 : Nat := 118140960795 + 7131736 * 2 ^ 59
def prefixEnd_7131736 : Nat := 4983230072969 + 3 ^ 40 * 7131736 * 2
def baseEnd_7131736 : Nat := 3662008468973414283801749

theorem tailTrace_7131736 : CollatzResearch.WordTrace tailWord_7131736 prefixEnd_7131736 3662008468973414283801749 := by
  unfold tailWord_7131736
  simp only [CollatzResearch.WordTrace]
  refine ⟨130057890645472975191847531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173410520860630633589130041 130057890645472975191847531)
  ·
    refine ⟨195086835968209462787771297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130057890645472975191847531 195086835968209462787771297)
    ·
      refine ⟨146315126976157097090828473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195086835968209462787771297 146315126976157097090828473)
      ·
        refine ⟨109736345232117822818121355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146315126976157097090828473 109736345232117822818121355)
        ·
          refine ⟨164604517848176734227182033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109736345232117822818121355 164604517848176734227182033)
          ·
            refine ⟨123453388386132550670386525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164604517848176734227182033 123453388386132550670386525)
            ·
              refine ⟨46295020644799706501394947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123453388386132550670386525 46295020644799706501394947)
              ·
                refine ⟨69442530967199559752092421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46295020644799706501394947 69442530967199559752092421)
                ·
                  refine ⟨13020474556349917453517329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69442530967199559752092421 13020474556349917453517329)
                  ·
                    refine ⟨9765355917262438090137997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13020474556349917453517329 9765355917262438090137997)
                    ·
                      refine ⟨3662008468973414283801749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765355917262438090137997 3662008468973414283801749)
                      ·
                        rfl

theorem cell23_7131736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7131736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131736 prefixEnd_7131736 := by exact prefixLift 7131736
  have htrace : WordTrace (prefixWord ++ tailWord_7131736) baseStart_7131736 baseEnd_7131736 := by
    simpa [prefixWord, tailWord_7131736, baseEnd_7131736] using wordTrace_append hprefix tailTrace_7131736
  have hstable : (prefixWord ++ tailWord_7131736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131736).length < 2 ^ (prefixWord ++ tailWord_7131736).sum := by decide
  have hdescent : baseEnd_7131736 < baseStart_7131736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131743 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 1, 4]
def baseStart_7131743 : Nat := 118140960795 + 7131743 * 2 ^ 59
def prefixEnd_7131743 : Nat := 4983230072969 + 3 ^ 40 * 7131743 * 2
def baseEnd_7131743 : Nat := 1220670687779331918804739

theorem tailTrace_7131743 : CollatzResearch.WordTrace tailWord_7131743 prefixEnd_7131743 1220670687779331918804739 := by
  unfold tailWord_7131743
  simp only [CollatzResearch.WordTrace]
  refine ⟨260116036601920590579199883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173410691067947060386133255 260116036601920590579199883)
  ·
    refine ⟨390174054902880885868799825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260116036601920590579199883 390174054902880885868799825)
    ·
      refine ⟨292630541177160664401599869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390174054902880885868799825 292630541177160664401599869)
      ·
        refine ⟨109736452941435249150599951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292630541177160664401599869 109736452941435249150599951)
        ·
          refine ⟨164604679412152873725899927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109736452941435249150599951 164604679412152873725899927)
          ·
            refine ⟨246907019118229310588849891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164604679412152873725899927 246907019118229310588849891)
            ·
              refine ⟨370360528677343965883274837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246907019118229310588849891 370360528677343965883274837)
              ·
                refine ⟨4340162445437624600194627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 370360528677343965883274837 4340162445437624600194627)
                ·
                  refine ⟨6510243668156436900291941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340162445437624600194627 6510243668156436900291941)
                  ·
                    refine ⟨1220670687779331918804739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510243668156436900291941 1220670687779331918804739)
                    ·
                      rfl

theorem cell23_7131743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_7131743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131743 prefixEnd_7131743 := by exact prefixLift 7131743
  have htrace : WordTrace (prefixWord ++ tailWord_7131743) baseStart_7131743 baseEnd_7131743 := by
    simpa [prefixWord, tailWord_7131743, baseEnd_7131743] using wordTrace_append hprefix tailTrace_7131743
  have hstable : (prefixWord ++ tailWord_7131743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131743).length < 2 ^ (prefixWord ++ tailWord_7131743).sum := by decide
  have hdescent : baseEnd_7131743 < baseStart_7131743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131759 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_7131759 : Nat := 118140960795 + 7131759 * 2 ^ 59
def prefixEnd_7131759 : Nat := 4983230072969 + 3 ^ 40 * 7131759 * 2
def baseEnd_7131759 : Nat := 3662020279028467693814143

theorem tailTrace_7131759 : CollatzResearch.WordTrace tailWord_7131759 prefixEnd_7131759 3662020279028467693814143 := by
  unfold tailWord_7131759
  simp only [CollatzResearch.WordTrace]
  refine ⟨260116620169862625311782331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173411080113241750207854887 260116620169862625311782331)
  ·
    refine ⟨390174930254793937967673497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260116620169862625311782331 390174930254793937967673497)
    ·
      refine ⟨292631197691095453475755123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390174930254793937967673497 292631197691095453475755123)
      ·
        refine ⟨438946796536643180213632685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292631197691095453475755123 438946796536643180213632685)
        ·
          refine ⟨164605048701241192580112257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438946796536643180213632685 164605048701241192580112257)
          ·
            refine ⟨123453786525930894435084193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164605048701241192580112257 123453786525930894435084193)
            ·
              refine ⟨92590339894448170826313145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123453786525930894435084193 92590339894448170826313145)
              ·
                refine ⟨69442754920836128119734859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92590339894448170826313145 69442754920836128119734859)
                ·
                  refine ⟨104164132381254192179602289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69442754920836128119734859 104164132381254192179602289)
                  ·
                    refine ⟨78123099285940644134701717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104164132381254192179602289 78123099285940644134701717)
                    ·
                      refine ⟨3662020279028467693814143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78123099285940644134701717 3662020279028467693814143)
                      ·
                        rfl

theorem cell23_7131759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_7131759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131759 prefixEnd_7131759 := by exact prefixLift 7131759
  have htrace : WordTrace (prefixWord ++ tailWord_7131759) baseStart_7131759 baseEnd_7131759 := by
    simpa [prefixWord, tailWord_7131759, baseEnd_7131759] using wordTrace_append hprefix tailTrace_7131759
  have hstable : (prefixWord ++ tailWord_7131759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131759).length < 2 ^ (prefixWord ++ tailWord_7131759).sum := by decide
  have hdescent : baseEnd_7131759 < baseStart_7131759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131794 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7131794 : Nat := 118140960795 + 7131794 * 2 ^ 59
def prefixEnd_7131794 : Nat := 4983230072969 + 3 ^ 40 * 7131794 * 2
def baseEnd_7131794 : Nat := 1220679416950458352292161

theorem tailTrace_7131794 : CollatzResearch.WordTrace tailWord_7131794 prefixEnd_7131794 1220679416950458352292161 := by
  unfold tailWord_7131794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65029474181183956572326609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173411931149823884192870957 65029474181183956572326609)
  ·
    refine ⟨48772105635887967429244957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65029474181183956572326609 48772105635887967429244957)
    ·
      refine ⟨18289539613457987785966859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48772105635887967429244957 18289539613457987785966859)
      ·
        refine ⟨27434309420186981678950289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18289539613457987785966859 27434309420186981678950289)
        ·
          refine ⟨20575732065140236259212717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27434309420186981678950289 20575732065140236259212717)
          ·
            refine ⟨7715899524427588597204769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20575732065140236259212717 7715899524427588597204769)
            ·
              refine ⟨5786924643320691447903577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715899524427588597204769 5786924643320691447903577)
              ·
                refine ⟨4340193482490518585927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786924643320691447903577 4340193482490518585927683)
                ·
                  refine ⟨6510290223735777878891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340193482490518585927683 6510290223735777878891525)
                  ·
                    refine ⟨1220679416950458352292161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510290223735777878891525 1220679416950458352292161)
                    ·
                      rfl

theorem cell23_7131794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7131794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131794 prefixEnd_7131794 := by exact prefixLift 7131794
  have htrace : WordTrace (prefixWord ++ tailWord_7131794) baseStart_7131794 baseEnd_7131794 := by
    simpa [prefixWord, tailWord_7131794, baseEnd_7131794] using wordTrace_append hprefix tailTrace_7131794
  have hstable : (prefixWord ++ tailWord_7131794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131794).length < 2 ^ (prefixWord ++ tailWord_7131794).sum := by decide
  have hdescent : baseEnd_7131794 < baseStart_7131794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131840 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4]
def baseStart_7131840 : Nat := 118140960795 + 7131840 * 2 ^ 59
def prefixEnd_7131840 : Nat := 4983230072969 + 3 ^ 40 * 7131840 * 2
def baseEnd_7131840 : Nat := 3662061870961481876901271

theorem tailTrace_7131840 : CollatzResearch.WordTrace tailWord_7131840 prefixEnd_7131840 3662061870961481876901271 := by
  unfold tailWord_7131840
  simp only [CollatzResearch.WordTrace]
  refine ⟨130059787241284588072740487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173413049655046117430320649 130059787241284588072740487)
  ·
    refine ⟨195089680861926882109110731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130059787241284588072740487 195089680861926882109110731)
    ·
      refine ⟨292634521292890323163666097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195089680861926882109110731 292634521292890323163666097)
      ·
        refine ⟨219475890969667742372749573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292634521292890323163666097 219475890969667742372749573)
        ·
          refine ⟨41151729556812701694890545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219475890969667742372749573 41151729556812701694890545)
          ·
            refine ⟨30863797167609526271167909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41151729556812701694890545 30863797167609526271167909)
            ·
              refine ⟨5786961968926786175843983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30863797167609526271167909 5786961968926786175843983)
              ·
                refine ⟨8680442953390179263765975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786961968926786175843983 8680442953390179263765975)
                ·
                  refine ⟨13020664430085268895648963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680442953390179263765975 13020664430085268895648963)
                  ·
                    refine ⟨19530996645127903343473445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13020664430085268895648963 19530996645127903343473445)
                    ·
                      refine ⟨3662061870961481876901271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19530996645127903343473445 3662061870961481876901271)
                      ·
                        rfl

theorem cell23_7131840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_7131840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131840 prefixEnd_7131840 := by exact prefixLift 7131840
  have htrace : WordTrace (prefixWord ++ tailWord_7131840) baseStart_7131840 baseEnd_7131840 := by
    simpa [prefixWord, tailWord_7131840, baseEnd_7131840] using wordTrace_append hprefix tailTrace_7131840
  have hstable : (prefixWord ++ tailWord_7131840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131840).length < 2 ^ (prefixWord ++ tailWord_7131840).sum := by decide
  have hdescent : baseEnd_7131840 < baseStart_7131840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131850 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_7131850 : Nat := 118140960795 + 7131850 * 2 ^ 59
def prefixEnd_7131850 : Nat := 4983230072969 + 3 ^ 40 * 7131850 * 2
def baseEnd_7131850 : Nat := 1220689001922675612592075

theorem tailTrace_7131850 : CollatzResearch.WordTrace tailWord_7131850 prefixEnd_7131850 1220689001922675612592075 := by
  unfold tailWord_7131850
  simp only [CollatzResearch.WordTrace]
  refine ⟨65029984803133236963336251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173413292808355298568896669 65029984803133236963336251)
  ·
    refine ⟨97544977204699855445004377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65029984803133236963336251 97544977204699855445004377)
    ·
      refine ⟨73158732903524891583753283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97544977204699855445004377 73158732903524891583753283)
      ·
        refine ⟨109738099355287337375629925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73158732903524891583753283 109738099355287337375629925)
        ·
          refine ⟨20575893629116375757930611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109738099355287337375629925 20575893629116375757930611)
          ·
            refine ⟨30863840443674563636895917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20575893629116375757930611 30863840443674563636895917)
            ·
              refine ⟨11573940166377961363835969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30863840443674563636895917 11573940166377961363835969)
              ·
                refine ⟨8680455124783471022876977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11573940166377961363835969 8680455124783471022876977)
                ·
                  refine ⟨6510341343587603267157733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8680455124783471022876977 6510341343587603267157733)
                  ·
                    refine ⟨1220689001922675612592075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510341343587603267157733 1220689001922675612592075)
                    ·
                      rfl

theorem cell23_7131850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_7131850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131850 prefixEnd_7131850 := by exact prefixLift 7131850
  have htrace : WordTrace (prefixWord ++ tailWord_7131850) baseStart_7131850 baseEnd_7131850 := by
    simpa [prefixWord, tailWord_7131850, baseEnd_7131850] using wordTrace_append hprefix tailTrace_7131850
  have hstable : (prefixWord ++ tailWord_7131850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131850).length < 2 ^ (prefixWord ++ tailWord_7131850).sum := by decide
  have hdescent : baseEnd_7131850 < baseStart_7131850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131857 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_7131857 : Nat := 118140960795 + 7131857 * 2 ^ 59
def prefixEnd_7131857 : Nat := 4983230072969 + 3 ^ 40 * 7131857 * 2
def baseEnd_7131857 : Nat := 3662070600132608310388693

theorem tailTrace_7131857 : CollatzResearch.WordTrace tailWord_7131857 prefixEnd_7131857 3662070600132608310388693 := by
  unfold tailWord_7131857
  simp only [CollatzResearch.WordTrace]
  refine ⟨260120194523507588048849825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173413463015671725365899883 260120194523507588048849825)
  ·
    refine ⟨195090145892630691036637369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260120194523507588048849825 195090145892630691036637369)
    ·
      refine ⟨146317609419473018277478027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195090145892630691036637369 146317609419473018277478027)
      ·
        refine ⟨219476414129209527416217041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146317609419473018277478027 219476414129209527416217041)
        ·
          refine ⟨164607310596907145562162781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219476414129209527416217041 164607310596907145562162781)
          ·
            refine ⟨61727741473840179585811043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164607310596907145562162781 61727741473840179585811043)
            ·
              refine ⟨92591612210760269378716565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61727741473840179585811043 92591612210760269378716565)
              ·
                refine ⟨4340231822379387627127339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92591612210760269378716565 4340231822379387627127339)
                ·
                  refine ⟨6510347733569081440691009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340231822379387627127339 6510347733569081440691009)
                  ·
                    refine ⟨4882760800176811080518257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510347733569081440691009 4882760800176811080518257)
                    ·
                      refine ⟨3662070600132608310388693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882760800176811080518257 3662070600132608310388693)
                      ·
                        rfl

theorem cell23_7131857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_7131857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131857 prefixEnd_7131857 := by exact prefixLift 7131857
  have htrace : WordTrace (prefixWord ++ tailWord_7131857) baseStart_7131857 baseEnd_7131857 := by
    simpa [prefixWord, tailWord_7131857, baseEnd_7131857] using wordTrace_append hprefix tailTrace_7131857
  have hstable : (prefixWord ++ tailWord_7131857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131857).length < 2 ^ (prefixWord ++ tailWord_7131857).sum := by decide
  have hdescent : baseEnd_7131857 < baseStart_7131857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131860 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7131860 : Nat := 118140960795 + 7131860 * 2 ^ 59
def prefixEnd_7131860 : Nat := 4983230072969 + 3 ^ 40 * 7131860 * 2
def baseEnd_7131860 : Nat := 3662072140574571798651179

theorem tailTrace_7131860 : CollatzResearch.WordTrace tailWord_7131860 prefixEnd_7131860 3662072140574571798651179 := by
  unfold tailWord_7131860
  simp only [CollatzResearch.WordTrace]
  refine ⟨130060151971248359780604517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173413535961664479707472689 130060151971248359780604517)
  ·
    refine ⟨24386278494609067458863347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130060151971248359780604517 24386278494609067458863347)
    ·
      refine ⟨36579417741913601188295021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24386278494609067458863347 36579417741913601188295021)
      ·
        refine ⟨13717281653217600445610633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36579417741913601188295021 13717281653217600445610633)
        ·
          refine ⟨10287961239913200334207975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13717281653217600445610633 10287961239913200334207975)
          ·
            refine ⟨15431941859869800501311963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287961239913200334207975 15431941859869800501311963)
            ·
              refine ⟨23147912789804700751967945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15431941859869800501311963 23147912789804700751967945)
              ·
                refine ⟨17360934592353525563975959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23147912789804700751967945 17360934592353525563975959)
                ·
                  refine ⟨26041401888530288345963939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17360934592353525563975959 26041401888530288345963939)
                  ·
                    refine ⟨39062102832795432518945909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26041401888530288345963939 39062102832795432518945909)
                    ·
                      refine ⟨3662072140574571798651179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39062102832795432518945909 3662072140574571798651179)
                      ·
                        rfl

theorem cell23_7131860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7131860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131860 prefixEnd_7131860 := by exact prefixLift 7131860
  have htrace : WordTrace (prefixWord ++ tailWord_7131860) baseStart_7131860 baseEnd_7131860 := by
    simpa [prefixWord, tailWord_7131860, baseEnd_7131860] using wordTrace_append hprefix tailTrace_7131860
  have hstable : (prefixWord ++ tailWord_7131860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131860).length < 2 ^ (prefixWord ++ tailWord_7131860).sum := by decide
  have hdescent : baseEnd_7131860 < baseStart_7131860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131880 : List Nat := [2, 1, 4, 1, 4, 2, 2, 7]
def baseStart_7131880 : Nat := 118140960795 + 7131880 * 2 ^ 59
def prefixEnd_7131880 : Nat := 4983230072969 + 3 ^ 40 * 7131880 * 2
def baseEnd_7131880 : Nat := 135632681858802285940781

theorem tailTrace_7131880 : CollatzResearch.WordTrace tailWord_7131880 prefixEnd_7131880 135632681858802285940781 := by
  unfold tailWord_7131880
  simp only [CollatzResearch.WordTrace]
  refine ⟨130060516701212131488468547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173414022268282841984624729 130060516701212131488468547)
  ·
    refine ⟨195090775051818197232702821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130060516701212131488468547 195090775051818197232702821)
    ·
      refine ⟨36579520322215911981131779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195090775051818197232702821 36579520322215911981131779)
      ·
        refine ⟨54869280483323867971697669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36579520322215911981131779 54869280483323867971697669)
        ·
          refine ⟨10287990090623225244693313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54869280483323867971697669 10287990090623225244693313)
          ·
            refine ⟨7715992567967418933519985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10287990090623225244693313 7715992567967418933519985)
            ·
              refine ⟨5786994425975564200139989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715992567967418933519985 5786994425975564200139989)
              ·
                refine ⟨135632681858802285940781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5786994425975564200139989 135632681858802285940781)
                ·
                  rfl

theorem cell23_7131880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 7].length) (baseStart_7131880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131880 prefixEnd_7131880 := by exact prefixLift 7131880
  have htrace : WordTrace (prefixWord ++ tailWord_7131880) baseStart_7131880 baseEnd_7131880 := by
    simpa [prefixWord, tailWord_7131880, baseEnd_7131880] using wordTrace_append hprefix tailTrace_7131880
  have hstable : (prefixWord ++ tailWord_7131880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131880).length < 2 ^ (prefixWord ++ tailWord_7131880).sum := by decide
  have hdescent : baseEnd_7131880 < baseStart_7131880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131890 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7131890 : Nat := 118140960795 + 7131890 * 2 ^ 59
def prefixEnd_7131890 : Nat := 4983230072969 + 3 ^ 40 * 7131890 * 2
def baseEnd_7131890 : Nat := 3662087544994206681276041

theorem tailTrace_7131890 : CollatzResearch.WordTrace tailWord_7131890 prefixEnd_7131890 3662087544994206681276041 := by
  unfold tailWord_7131890
  simp only [CollatzResearch.WordTrace]
  refine ⟨65030349533097008671200281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173414265421592023123200749 65030349533097008671200281)
  ·
    refine ⟨48772762149822756503400211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65030349533097008671200281 48772762149822756503400211)
    ·
      refine ⟨73159143224734134755100317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48772762149822756503400211 73159143224734134755100317)
      ·
        refine ⟨27434678709275300533162619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73159143224734134755100317 27434678709275300533162619)
        ·
          refine ⟨41152018063912950799743929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27434678709275300533162619 41152018063912950799743929)
          ·
            refine ⟨30864013547934713099807947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41152018063912950799743929 30864013547934713099807947)
            ·
              refine ⟨46296020321902069649711921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30864013547934713099807947 46296020321902069649711921)
              ·
                refine ⟨34722015241426552237283941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46296020321902069649711921 34722015241426552237283941)
                ·
                  refine ⟨6510377857767478544490739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34722015241426552237283941 6510377857767478544490739)
                  ·
                    refine ⟨9765566786651217816736109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510377857767478544490739 9765566786651217816736109)
                    ·
                      refine ⟨3662087544994206681276041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765566786651217816736109 3662087544994206681276041)
                      ·
                        rfl

theorem cell23_7131890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7131890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131890 prefixEnd_7131890 := by exact prefixLift 7131890
  have htrace : WordTrace (prefixWord ++ tailWord_7131890) baseStart_7131890 baseEnd_7131890 := by
    simpa [prefixWord, tailWord_7131890, baseEnd_7131890] using wordTrace_append hprefix tailTrace_7131890
  have hstable : (prefixWord ++ tailWord_7131890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131890).length < 2 ^ (prefixWord ++ tailWord_7131890).sum := by decide
  have hdescent : baseEnd_7131890 < baseStart_7131890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131916 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7131916 : Nat := 118140960795 + 7131916 * 2 ^ 59
def prefixEnd_7131916 : Nat := 4983230072969 + 3 ^ 40 * 7131916 * 2
def baseEnd_7131916 : Nat := 3662100895491223579550921

theorem tailTrace_7131916 : CollatzResearch.WordTrace tailWord_7131916 prefixEnd_7131916 3662100895491223579550921 := by
  unfold tailWord_7131916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130061173215146920562623801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173414897620195894083498401 130061173215146920562623801)
  ·
    refine ⟨97545879911360190421967851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130061173215146920562623801 97545879911360190421967851)
    ·
      refine ⟨146318819867040285632951777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97545879911360190421967851 146318819867040285632951777)
      ·
        refine ⟨109739114900280214224713833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146318819867040285632951777 109739114900280214224713833)
        ·
          refine ⟨82304336175210160668535375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109739114900280214224713833 82304336175210160668535375)
          ·
            refine ⟨123456504262815241002803063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82304336175210160668535375 123456504262815241002803063)
            ·
              refine ⟨185184756394222861504204595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123456504262815241002803063 185184756394222861504204595)
              ·
                refine ⟨277777134591334292256306893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185184756394222861504204595 277777134591334292256306893)
                ·
                  refine ⟨104166425471750359596115085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277777134591334292256306893 104166425471750359596115085)
                  ·
                    refine ⟨39062409551906384848543157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104166425471750359596115085 39062409551906384848543157)
                    ·
                      refine ⟨3662100895491223579550921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39062409551906384848543157 3662100895491223579550921)
                      ·
                        rfl

theorem cell23_7131916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7131916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131916 prefixEnd_7131916 := by exact prefixLift 7131916
  have htrace : WordTrace (prefixWord ++ tailWord_7131916) baseStart_7131916 baseEnd_7131916 := by
    simpa [prefixWord, tailWord_7131916, baseEnd_7131916] using wordTrace_append hprefix tailTrace_7131916
  have hstable : (prefixWord ++ tailWord_7131916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131916).length < 2 ^ (prefixWord ++ tailWord_7131916).sum := by decide
  have hdescent : baseEnd_7131916 < baseStart_7131916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131930 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_7131930 : Nat := 118140960795 + 7131930 * 2 ^ 59
def prefixEnd_7131930 : Nat := 4983230072969 + 3 ^ 40 * 7131930 * 2
def baseEnd_7131930 : Nat := 3662108084220386524775857

theorem tailTrace_7131930 : CollatzResearch.WordTrace tailWord_7131930 prefixEnd_7131930 3662108084220386524775857 := by
  unfold tailWord_7131930
  simp only [CollatzResearch.WordTrace]
  refine ⟨65030714263060780379064311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173415238034828747677504829 65030714263060780379064311)
  ·
    refine ⟨97546071394591170568596467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65030714263060780379064311 97546071394591170568596467)
    ·
      refine ⟨146319107091886755852894701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97546071394591170568596467 146319107091886755852894701)
      ·
        refine ⟨54869665159457533444835513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146319107091886755852894701 54869665159457533444835513)
        ·
          refine ⟨41152248869593150083626635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54869665159457533444835513 41152248869593150083626635)
          ·
            refine ⟨61728373304389725125439953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41152248869593150083626635 61728373304389725125439953)
            ·
              refine ⟨46296279978292293844079965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61728373304389725125439953 46296279978292293844079965)
              ·
                refine ⟨17361104991859610191529987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46296279978292293844079965 17361104991859610191529987)
                ·
                  refine ⟨26041657487789415287294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17361104991859610191529987 26041657487789415287294981)
                  ·
                    refine ⟨4882810778960515366367809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26041657487789415287294981 4882810778960515366367809)
                    ·
                      refine ⟨3662108084220386524775857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882810778960515366367809 3662108084220386524775857)
                      ·
                        rfl

theorem cell23_7131930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_7131930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131930 prefixEnd_7131930 := by exact prefixLift 7131930
  have htrace : WordTrace (prefixWord ++ tailWord_7131930) baseStart_7131930 baseEnd_7131930 := by
    simpa [prefixWord, tailWord_7131930, baseEnd_7131930] using wordTrace_append hprefix tailTrace_7131930
  have hstable : (prefixWord ++ tailWord_7131930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131930).length < 2 ^ (prefixWord ++ tailWord_7131930).sum := by decide
  have hdescent : baseEnd_7131930 < baseStart_7131930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131950 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7131950 : Nat := 118140960795 + 7131950 * 2 ^ 59
def prefixEnd_7131950 : Nat := 4983230072969 + 3 ^ 40 * 7131950 * 2
def baseEnd_7131950 : Nat := 3662118353833476446525765

theorem tailTrace_7131950 : CollatzResearch.WordTrace tailWord_7131950 prefixEnd_7131950 3662118353833476446525765 := by
  unfold tailWord_7131950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32515448314021333116498163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173415724341447109954656869 32515448314021333116498163)
  ·
    refine ⟨48773172471031999674747245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32515448314021333116498163 48773172471031999674747245)
    ·
      refine ⟨18289939676636999878030217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48773172471031999674747245 18289939676636999878030217)
      ·
        refine ⟨13717454757477749908522663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18289939676636999878030217 13717454757477749908522663)
        ·
          refine ⟨20576182136216624862783995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13717454757477749908522663 20576182136216624862783995)
          ·
            refine ⟨30864273204324937294175993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576182136216624862783995 30864273204324937294175993)
            ·
              refine ⟨23148204903243702970631995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30864273204324937294175993 23148204903243702970631995)
              ·
                refine ⟨34722307354865554455947993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23148204903243702970631995 34722307354865554455947993)
                ·
                  refine ⟨26041730516149165841960995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34722307354865554455947993 26041730516149165841960995)
                  ·
                    refine ⟨39062595774223748762941493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26041730516149165841960995 39062595774223748762941493)
                    ·
                      refine ⟨3662118353833476446525765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39062595774223748762941493 3662118353833476446525765)
                      ·
                        rfl

theorem cell23_7131950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7131950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131950 prefixEnd_7131950 := by exact prefixLift 7131950
  have htrace : WordTrace (prefixWord ++ tailWord_7131950) baseStart_7131950 baseEnd_7131950 := by
    simpa [prefixWord, tailWord_7131950, baseEnd_7131950] using wordTrace_append hprefix tailTrace_7131950
  have hstable : (prefixWord ++ tailWord_7131950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131950).length < 2 ^ (prefixWord ++ tailWord_7131950).sum := by decide
  have hdescent : baseEnd_7131950 < baseStart_7131950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7131980 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7131980 : Nat := 118140960795 + 7131980 * 2 ^ 59
def prefixEnd_7131980 : Nat := 4983230072969 + 3 ^ 40 * 7131980 * 2
def baseEnd_7131980 : Nat := 3662133758253111329150627

theorem tailTrace_7131980 : CollatzResearch.WordTrace tailWord_7131980 prefixEnd_7131980 3662133758253111329150627 := by
  unfold tailWord_7131980
  simp only [CollatzResearch.WordTrace]
  refine ⟨130062340351030990027788697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173416453801374653370384929 130062340351030990027788697)
  ·
    refine ⟨97546755263273242520841523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130062340351030990027788697 97546755263273242520841523)
    ·
      refine ⟨146320132894909863781262285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97546755263273242520841523 146320132894909863781262285)
      ·
        refine ⟨54870049835591198917973357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146320132894909863781262285 54870049835591198917973357)
        ·
          refine ⟨20576268688346699594240009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54870049835591198917973357 20576268688346699594240009)
          ·
            refine ⟨15432201516260024695680007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20576268688346699594240009 15432201516260024695680007)
            ·
              refine ⟨23148302274390037043520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15432201516260024695680007 23148302274390037043520011)
              ·
                refine ⟨34722453411585055565280017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23148302274390037043520011 34722453411585055565280017)
                ·
                  refine ⟨26041840058688791673960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34722453411585055565280017 26041840058688791673960013)
                  ·
                    refine ⟨9765690022008296877735005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26041840058688791673960013 9765690022008296877735005)
                    ·
                      refine ⟨3662133758253111329150627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765690022008296877735005 3662133758253111329150627)
                      ·
                        rfl

theorem cell23_7131980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7131980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7131980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7131980 prefixEnd_7131980 := by exact prefixLift 7131980
  have htrace : WordTrace (prefixWord ++ tailWord_7131980) baseStart_7131980 baseEnd_7131980 := by
    simpa [prefixWord, tailWord_7131980, baseEnd_7131980] using wordTrace_append hprefix tailTrace_7131980
  have hstable : (prefixWord ++ tailWord_7131980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7131980).length < 2 ^ (prefixWord ++ tailWord_7131980).sum := by decide
  have hdescent : baseEnd_7131980 < baseStart_7131980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7131980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132040 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_7132040 : Nat := 118140960795 + 7132040 * 2 ^ 59
def prefixEnd_7132040 : Nat := 4983230072969 + 3 ^ 40 * 7132040 * 2
def baseEnd_7132040 : Nat := 3662164567092381094400351

theorem tailTrace_7132040 : CollatzResearch.WordTrace tailWord_7132040 prefixEnd_7132040 3662164567092381094400351 := by
  unfold tailWord_7132040
  simp only [CollatzResearch.WordTrace]
  refine ⟨130063434540922305151380787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173417912721229740201841049 130063434540922305151380787)
  ·
    refine ⟨195095151811383457727071181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130063434540922305151380787 195095151811383457727071181)
    ·
      refine ⟨73160681929268796647651693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195095151811383457727071181 73160681929268796647651693)
      ·
        refine ⟨27435255723475798742869385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73160681929268796647651693 27435255723475798742869385)
        ·
          refine ⟨20576441792606849057152039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27435255723475798742869385 20576441792606849057152039)
          ·
            refine ⟨30864662688910273585728059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576441792606849057152039 30864662688910273585728059)
            ·
              refine ⟨46296994033365410378592089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30864662688910273585728059 46296994033365410378592089)
              ·
                refine ⟨34722745525024057783944067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46296994033365410378592089 34722745525024057783944067)
                ·
                  refine ⟨52084118287536086675916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34722745525024057783944067 52084118287536086675916101)
                  ·
                    refine ⟨9765772178913016251734269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52084118287536086675916101 9765772178913016251734269)
                    ·
                      refine ⟨3662164567092381094400351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765772178913016251734269 3662164567092381094400351)
                      ·
                        rfl

theorem cell23_7132040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_7132040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132040 prefixEnd_7132040 := by exact prefixLift 7132040
  have htrace : WordTrace (prefixWord ++ tailWord_7132040) baseStart_7132040 baseEnd_7132040 := by
    simpa [prefixWord, tailWord_7132040, baseEnd_7132040] using wordTrace_append hprefix tailTrace_7132040
  have hstable : (prefixWord ++ tailWord_7132040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132040).length < 2 ^ (prefixWord ++ tailWord_7132040).sum := by decide
  have hdescent : baseEnd_7132040 < baseStart_7132040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132043 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 6]
def baseStart_7132043 : Nat := 118140960795 + 7132043 * 2 ^ 59
def prefixEnd_7132043 : Nat := 4983230072969 + 3 ^ 40 * 7132043 * 2
def baseEnd_7132043 : Nat := 406907345281593842518093

theorem tailTrace_7132043 : CollatzResearch.WordTrace tailWord_7132043 prefixEnd_7132043 406907345281593842518093 := by
  unfold tailWord_7132043
  simp only [CollatzResearch.WordTrace]
  refine ⟨260126978500833741815120783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173417985667222494543413855 260126978500833741815120783)
  ·
    refine ⟨390190467751250612722681175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260126978500833741815120783 390190467751250612722681175)
    ·
      refine ⟨585285701626875919084021763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390190467751250612722681175 585285701626875919084021763)
      ·
        refine ⟨877928552440313878626032645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585285701626875919084021763 877928552440313878626032645)
        ·
          refine ⟨164611603582558852242381121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877928552440313878626032645 164611603582558852242381121)
          ·
            refine ⟨123458702686919139181785841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164611603582558852242381121 123458702686919139181785841)
            ·
              refine ⟨92594027015189354386339381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123458702686919139181785841 92594027015189354386339381)
              ·
                refine ⟨8680690032674001973719317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92594027015189354386339381 8680690032674001973719317)
                ·
                  refine ⟨406907345281593842518093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8680690032674001973719317 406907345281593842518093)
                  ·
                    rfl

theorem cell23_7132043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 6].length) (baseStart_7132043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132043 prefixEnd_7132043 := by exact prefixLift 7132043
  have htrace : WordTrace (prefixWord ++ tailWord_7132043) baseStart_7132043 baseEnd_7132043 := by
    simpa [prefixWord, tailWord_7132043, baseEnd_7132043] using wordTrace_append hprefix tailTrace_7132043
  have hstable : (prefixWord ++ tailWord_7132043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132043).length < 2 ^ (prefixWord ++ tailWord_7132043).sum := by decide
  have hdescent : baseEnd_7132043 < baseStart_7132043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132054 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7132054 : Nat := 118140960795 + 7132054 * 2 ^ 59
def prefixEnd_7132054 : Nat := 4983230072969 + 3 ^ 40 * 7132054 * 2
def baseEnd_7132054 : Nat := 3662171755821544039625287

theorem tailTrace_7132054 : CollatzResearch.WordTrace tailWord_7132054 prefixEnd_7132054 3662171755821544039625287 := by
  unfold tailWord_7132054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257961231487118168360701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173418253135862593795847477 16257961231487118168360701)
  ·
    refine ⟨6096735461807669313135263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16257961231487118168360701 6096735461807669313135263)
    ·
      refine ⟨9145103192711503969702895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096735461807669313135263 9145103192711503969702895)
      ·
        refine ⟨13717654789067255954554343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145103192711503969702895 13717654789067255954554343)
        ·
          refine ⟨20576482183600883931831515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13717654789067255954554343 20576482183600883931831515)
          ·
            refine ⟨30864723275401325897747273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576482183600883931831515 30864723275401325897747273)
            ·
              refine ⟨23148542456550994423310455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30864723275401325897747273 23148542456550994423310455)
              ·
                refine ⟨34722813684826491634965683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23148542456550994423310455 34722813684826491634965683)
                ·
                  refine ⟨52084220527239737452448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34722813684826491634965683 52084220527239737452448525)
                  ·
                    refine ⟨19531582697714901544668197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52084220527239737452448525 19531582697714901544668197)
                    ·
                      refine ⟨3662171755821544039625287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19531582697714901544668197 3662171755821544039625287)
                      ·
                        rfl

theorem cell23_7132054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7132054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132054 prefixEnd_7132054 := by exact prefixLift 7132054
  have htrace : WordTrace (prefixWord ++ tailWord_7132054) baseStart_7132054 baseEnd_7132054 := by
    simpa [prefixWord, tailWord_7132054, baseEnd_7132054] using wordTrace_append hprefix tailTrace_7132054
  have hstable : (prefixWord ++ tailWord_7132054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132054).length < 2 ^ (prefixWord ++ tailWord_7132054).sum := by decide
  have hdescent : baseEnd_7132054 < baseStart_7132054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132081 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 1, 4]
def baseStart_7132081 : Nat := 118140960795 + 7132081 * 2 ^ 59
def prefixEnd_7132081 : Nat := 4983230072969 + 3 ^ 40 * 7132081 * 2
def baseEnd_7132081 : Nat := 1220728539933071811329221

theorem tailTrace_7132081 : CollatzResearch.WordTrace tailWord_7132081 prefixEnd_7132081 1220728539933071811329221 := by
  unfold tailWord_7132081
  simp only [CollatzResearch.WordTrace]
  refine ⟨260128364474696074305004097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173418909649797382870002731 260128364474696074305004097)
  ·
    refine ⟨195096273356022055728753073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260128364474696074305004097 195096273356022055728753073)
    ·
      refine ⟨146322205017016541796564805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195096273356022055728753073 146322205017016541796564805)
      ·
        refine ⟨27435413440690601586855901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146322205017016541796564805 27435413440690601586855901)
        ·
          refine ⟨10288280040258975595070963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27435413440690601586855901 10288280040258975595070963)
          ·
            refine ⟨15432420060388463392606445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10288280040258975595070963 15432420060388463392606445)
            ·
              refine ⟨5787157522645673772227417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15432420060388463392606445 5787157522645673772227417)
              ·
                refine ⟨4340368141984255329170563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787157522645673772227417 4340368141984255329170563)
                ·
                  refine ⟨6510552212976382993755845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340368141984255329170563 6510552212976382993755845)
                  ·
                    refine ⟨1220728539933071811329221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6510552212976382993755845 1220728539933071811329221)
                    ·
                      rfl

theorem cell23_7132081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_7132081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132081 prefixEnd_7132081 := by exact prefixLift 7132081
  have htrace : WordTrace (prefixWord ++ tailWord_7132081) baseStart_7132081 baseEnd_7132081 := by
    simpa [prefixWord, tailWord_7132081, baseEnd_7132081] using wordTrace_append hprefix tailTrace_7132081
  have hstable : (prefixWord ++ tailWord_7132081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132081).length < 2 ^ (prefixWord ++ tailWord_7132081).sum := by decide
  have hdescent : baseEnd_7132081 < baseStart_7132081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132087 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_7132087 : Nat := 118140960795 + 7132087 * 2 ^ 59
def prefixEnd_7132087 : Nat := 4983230072969 + 3 ^ 40 * 7132087 * 2
def baseEnd_7132087 : Nat := 3662188700683142410512635

theorem tailTrace_7132087 : CollatzResearch.WordTrace tailWord_7132087 prefixEnd_7132087 3662188700683142410512635 := by
  unfold tailWord_7132087
  simp only [CollatzResearch.WordTrace]
  refine ⟨260128583312674337329722515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173419055541782891553148343 260128583312674337329722515)
  ·
    refine ⟨390192874969011505994583773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260128583312674337329722515 390192874969011505994583773)
    ·
      refine ⟨146322328113379314747968915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390192874969011505994583773 146322328113379314747968915)
      ·
        refine ⟨219483492170068972121953373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146322328113379314747968915 219483492170068972121953373)
        ·
          refine ⟨82306309563775864545732515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219483492170068972121953373 82306309563775864545732515)
          ·
            refine ⟨123459464345663796818598773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82306309563775864545732515 123459464345663796818598773)
            ·
              refine ⟨11574324782405980951743635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123459464345663796818598773 11574324782405980951743635)
              ·
                refine ⟨17361487173608971427615453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11574324782405980951743635 17361487173608971427615453)
                ·
                  refine ⟨6510557690103364285355795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17361487173608971427615453 6510557690103364285355795)
                  ·
                    refine ⟨9765836535155046428033693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510557690103364285355795 9765836535155046428033693)
                    ·
                      refine ⟨3662188700683142410512635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765836535155046428033693 3662188700683142410512635)
                      ·
                        rfl

theorem cell23_7132087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_7132087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132087 prefixEnd_7132087 := by exact prefixLift 7132087
  have htrace : WordTrace (prefixWord ++ tailWord_7132087) baseStart_7132087 baseEnd_7132087 := by
    simpa [prefixWord, tailWord_7132087, baseEnd_7132087] using wordTrace_append hprefix tailTrace_7132087
  have hstable : (prefixWord ++ tailWord_7132087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132087).length < 2 ^ (prefixWord ++ tailWord_7132087).sum := by decide
  have hdescent : baseEnd_7132087 < baseStart_7132087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132107 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 1, 5]
def baseStart_7132107 : Nat := 118140960795 + 7132107 * 2 ^ 59
def prefixEnd_7132107 : Nat := 4983230072969 + 3 ^ 40 * 7132107 * 2
def baseEnd_7132107 : Nat := 1220732990098744110754181

theorem tailTrace_7132107 : CollatzResearch.WordTrace tailWord_7132107 prefixEnd_7132107 1220732990098744110754181 := by
  unfold tailWord_7132107
  simp only [CollatzResearch.WordTrace]
  refine ⟨260129312772601880745450575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173419541848401253830300383 260129312772601880745450575)
  ·
    refine ⟨390193969158902821118175863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260129312772601880745450575 390193969158902821118175863)
    ·
      refine ⟨585290953738354231677263795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390193969158902821118175863 585290953738354231677263795)
      ·
        refine ⟨877936430607531347515895693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585290953738354231677263795 877936430607531347515895693)
        ·
          refine ⟨329226161477824255318460885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877936430607531347515895693 329226161477824255318460885)
          ·
            refine ⟨7716238159636505984026427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 329226161477824255318460885 7716238159636505984026427)
            ·
              refine ⟨11574357239454758976039641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716238159636505984026427 11574357239454758976039641)
              ·
                refine ⟨8680767929591069232029731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11574357239454758976039641 8680767929591069232029731)
                ·
                  refine ⟨13021151894386603848044597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680767929591069232029731 13021151894386603848044597)
                  ·
                    refine ⟨1220732990098744110754181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13021151894386603848044597 1220732990098744110754181)
                    ·
                      rfl

theorem cell23_7132107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 5].length) (baseStart_7132107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132107 prefixEnd_7132107 := by exact prefixLift 7132107
  have htrace : WordTrace (prefixWord ++ tailWord_7132107) baseStart_7132107 baseEnd_7132107 := by
    simpa [prefixWord, tailWord_7132107, baseEnd_7132107] using wordTrace_append hprefix tailTrace_7132107
  have hstable : (prefixWord ++ tailWord_7132107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132107).length < 2 ^ (prefixWord ++ tailWord_7132107).sum := by decide
  have hdescent : baseEnd_7132107 < baseStart_7132107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132114 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7132114 : Nat := 118140960795 + 7132114 * 2 ^ 59
def prefixEnd_7132114 : Nat := 4983230072969 + 3 ^ 40 * 7132114 * 2
def baseEnd_7132114 : Nat := 3662202564660813804875011

theorem tailTrace_7132114 : CollatzResearch.WordTrace tailWord_7132114 prefixEnd_7132114 3662202564660813804875011 := by
  unfold tailWord_7132114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65032392020894130235238849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173419712055717680627303597 65032392020894130235238849)
  ·
    refine ⟨48774294015670597676429137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65032392020894130235238849 48774294015670597676429137)
    ·
      refine ⟨36580720511752948257321853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48774294015670597676429137 36580720511752948257321853)
      ·
        refine ⟨13717770191907355596495695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36580720511752948257321853 13717770191907355596495695)
        ·
          refine ⟨20576655287861033394743543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13717770191907355596495695 20576655287861033394743543)
          ·
            refine ⟨30864982931791550092115315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20576655287861033394743543 30864982931791550092115315)
            ·
              refine ⟨46297474397687325138172973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30864982931791550092115315 46297474397687325138172973)
              ·
                refine ⟨17361552899132746926814865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46297474397687325138172973 17361552899132746926814865)
                ·
                  refine ⟨13021164674349560195111149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17361552899132746926814865 13021164674349560195111149)
                  ·
                    refine ⟨4882936752881085073166681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13021164674349560195111149 4882936752881085073166681)
                    ·
                      refine ⟨3662202564660813804875011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4882936752881085073166681 3662202564660813804875011)
                      ·
                        rfl

theorem cell23_7132114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7132114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132114 prefixEnd_7132114 := by exact prefixLift 7132114
  have htrace : WordTrace (prefixWord ++ tailWord_7132114) baseStart_7132114 baseEnd_7132114 := by
    simpa [prefixWord, tailWord_7132114, baseEnd_7132114] using wordTrace_append hprefix tailTrace_7132114
  have hstable : (prefixWord ++ tailWord_7132114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132114).length < 2 ^ (prefixWord ++ tailWord_7132114).sum := by decide
  have hdescent : baseEnd_7132114 < baseStart_7132114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132120 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_7132120 : Nat := 118140960795 + 7132120 * 2 ^ 59
def prefixEnd_7132120 : Nat := 4983230072969 + 3 ^ 40 * 7132120 * 2
def baseEnd_7132120 : Nat := 1220735215181580260466661

theorem tailTrace_7132120 : CollatzResearch.WordTrace tailWord_7132120 prefixEnd_7132120 1220735215181580260466661 := by
  unfold tailWord_7132120
  simp only [CollatzResearch.WordTrace]
  refine ⟨130064893460777391982836907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173419857947703189310449209 130064893460777391982836907)
  ·
    refine ⟨195097340191166087974255361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130064893460777391982836907 195097340191166087974255361)
    ·
      refine ⟨146323005143374565980691521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195097340191166087974255361 146323005143374565980691521)
      ·
        refine ⟨109742253857530924485518641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146323005143374565980691521 109742253857530924485518641)
        ·
          refine ⟨82306690393148193364138981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109742253857530924485518641 82306690393148193364138981)
          ·
            refine ⟨15432504448715286255776059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82306690393148193364138981 15432504448715286255776059)
            ·
              refine ⟨23148756673072929383664089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15432504448715286255776059 23148756673072929383664089)
              ·
                refine ⟨17361567504804697037748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23148756673072929383664089 17361567504804697037748067)
                ·
                  refine ⟨26042351257207045556622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17361567504804697037748067 26042351257207045556622101)
                  ·
                    refine ⟨1220735215181580260466661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26042351257207045556622101 1220735215181580260466661)
                    ·
                      rfl

theorem cell23_7132120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_7132120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132120 prefixEnd_7132120 := by exact prefixLift 7132120
  have htrace : WordTrace (prefixWord ++ tailWord_7132120) baseStart_7132120 baseEnd_7132120 := by
    simpa [prefixWord, tailWord_7132120, baseEnd_7132120] using wordTrace_append hprefix tailTrace_7132120
  have hstable : (prefixWord ++ tailWord_7132120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132120).length < 2 ^ (prefixWord ++ tailWord_7132120).sum := by decide
  have hdescent : baseEnd_7132120 < baseStart_7132120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132138 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_7132138 : Nat := 118140960795 + 7132138 * 2 ^ 59
def prefixEnd_7132138 : Nat := 4983230072969 + 3 ^ 40 * 7132138 * 2
def baseEnd_7132138 : Nat := 3662214888196521710974901

theorem tailTrace_7132138 : CollatzResearch.WordTrace tailWord_7132138 prefixEnd_7132138 3662214888196521710974901 := by
  unfold tailWord_7132138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65032610858872393259957267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173420295623659715359886045 65032610858872393259957267)
  ·
    refine ⟨97548916288308589889935901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65032610858872393259957267 97548916288308589889935901)
    ·
      refine ⟨36580843608115721208725963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97548916288308589889935901 36580843608115721208725963)
      ·
        refine ⟨54871265412173581813088945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36580843608115721208725963 54871265412173581813088945)
        ·
          refine ⟨41153449059130186359816709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54871265412173581813088945 41153449059130186359816709)
          ·
            refine ⟨7716271698586909942465633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41153449059130186359816709 7716271698586909942465633)
            ·
              refine ⟨5787203773940182456849225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716271698586909942465633 5787203773940182456849225)
              ·
                refine ⟨4340402830455136842636919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787203773940182456849225 4340402830455136842636919)
                ·
                  refine ⟨6510604245682705263955379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340402830455136842636919 6510604245682705263955379)
                  ·
                    refine ⟨9765906368524057895933069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510604245682705263955379 9765906368524057895933069)
                    ·
                      refine ⟨3662214888196521710974901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765906368524057895933069 3662214888196521710974901)
                      ·
                        rfl

theorem cell23_7132138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_7132138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132138 prefixEnd_7132138 := by exact prefixLift 7132138
  have htrace : WordTrace (prefixWord ++ tailWord_7132138) baseStart_7132138 baseEnd_7132138 := by
    simpa [prefixWord, tailWord_7132138, baseEnd_7132138] using wordTrace_append hprefix tailTrace_7132138
  have hstable : (prefixWord ++ tailWord_7132138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132138).length < 2 ^ (prefixWord ++ tailWord_7132138).sum := by decide
  have hdescent : baseEnd_7132138 < baseStart_7132138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132178 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7132178 : Nat := 118140960795 + 7132178 * 2 ^ 59
def prefixEnd_7132178 : Nat := 4983230072969 + 3 ^ 40 * 7132178 * 2
def baseEnd_7132178 : Nat := 3662235427422701554474717

theorem tailTrace_7132178 : CollatzResearch.WordTrace tailWord_7132178 prefixEnd_7132178 3662235427422701554474717 := by
  unfold tailWord_7132178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65032975588836164967821297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173421268236896439914190125 65032975588836164967821297)
  ·
    refine ⟨48774731691627123725865973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65032975588836164967821297 48774731691627123725865973)
    ·
      refine ⟨4572631096090042849299935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48774731691627123725865973 4572631096090042849299935)
      ·
        refine ⟨6858946644135064273949903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572631096090042849299935 6858946644135064273949903)
        ·
          refine ⟨10288419966202596410924855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858946644135064273949903 10288419966202596410924855)
          ·
            refine ⟨15432629949303894616387283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10288419966202596410924855 15432629949303894616387283)
            ·
              refine ⟨23148944923955841924580925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15432629949303894616387283 23148944923955841924580925)
              ·
                refine ⟨8680854346483440721717847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23148944923955841924580925 8680854346483440721717847)
                ·
                  refine ⟨13021281519725161082576771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680854346483440721717847 13021281519725161082576771)
                  ·
                    refine ⟨19531922279587741623865157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13021281519725161082576771 19531922279587741623865157)
                    ·
                      refine ⟨3662235427422701554474717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19531922279587741623865157 3662235427422701554474717)
                      ·
                        rfl

theorem cell23_7132178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7132178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132178 prefixEnd_7132178 := by exact prefixLift 7132178
  have htrace : WordTrace (prefixWord ++ tailWord_7132178) baseStart_7132178 baseEnd_7132178 := by
    simpa [prefixWord, tailWord_7132178, baseEnd_7132178] using wordTrace_append hprefix tailTrace_7132178
  have hstable : (prefixWord ++ tailWord_7132178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132178).length < 2 ^ (prefixWord ++ tailWord_7132178).sum := by decide
  have hdescent : baseEnd_7132178 < baseStart_7132178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132181 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_7132181 : Nat := 118140960795 + 7132181 * 2 ^ 59
def prefixEnd_7132181 : Nat := 4983230072969 + 3 ^ 40 * 7132181 * 2
def baseEnd_7132181 : Nat := 3662236967864665042737203

theorem tailTrace_7132181 : CollatzResearch.WordTrace tailWord_7132181 prefixEnd_7132181 3662236967864665042737203 := by
  unfold tailWord_7132181
  simp only [CollatzResearch.WordTrace]
  refine ⟨260132011774333791383644397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173421341182889194255762931 260132011774333791383644397)
  ·
    refine ⟨97549504415375171768866649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260132011774333791383644397 97549504415375171768866649)
    ·
      refine ⟨73162128311531378826649987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97549504415375171768866649 73162128311531378826649987)
      ·
        refine ⟨109743192467297068239974981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73162128311531378826649987 109743192467297068239974981)
        ·
          refine ⟨20576848587618200294995309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109743192467297068239974981 20576848587618200294995309)
          ·
            refine ⟨7716318220356825110623241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20576848587618200294995309 7716318220356825110623241)
            ·
              refine ⟨5787238665267618832967431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716318220356825110623241 5787238665267618832967431)
              ·
                refine ⟨8680857997901428249451147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787238665267618832967431 8680857997901428249451147)
                ·
                  refine ⟨13021286996852142374176721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680857997901428249451147 13021286996852142374176721)
                  ·
                    refine ⟨9765965247639106780632541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13021286996852142374176721 9765965247639106780632541)
                    ·
                      refine ⟨3662236967864665042737203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765965247639106780632541 3662236967864665042737203)
                      ·
                        rfl

theorem cell23_7132181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_7132181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132181 prefixEnd_7132181 := by exact prefixLift 7132181
  have htrace : WordTrace (prefixWord ++ tailWord_7132181) baseStart_7132181 baseEnd_7132181 := by
    simpa [prefixWord, tailWord_7132181, baseEnd_7132181] using wordTrace_append hprefix tailTrace_7132181
  have hstable : (prefixWord ++ tailWord_7132181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132181).length < 2 ^ (prefixWord ++ tailWord_7132181).sum := by decide
  have hdescent : baseEnd_7132181 < baseStart_7132181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132194 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_7132194 : Nat := 118140960795 + 7132194 * 2 ^ 59
def prefixEnd_7132194 : Nat := 4983230072969 + 3 ^ 40 * 7132194 * 2
def baseEnd_7132194 : Nat := 3662243643113173491874643

theorem tailTrace_7132194 : CollatzResearch.WordTrace tailWord_7132194 prefixEnd_7132194 3662243643113173491874643 := by
  unfold tailWord_7132194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033121480821673650966909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173421657282191129735911757 65033121480821673650966909)
  ·
    refine ⟨24387420555308127619112591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65033121480821673650966909 24387420555308127619112591)
    ·
      refine ⟨36581130832962191428668887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24387420555308127619112591 36581130832962191428668887)
      ·
        refine ⟨54871696249443287143003331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36581130832962191428668887 54871696249443287143003331)
        ·
          refine ⟨82307544374164930714504997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54871696249443287143003331 82307544374164930714504997)
          ·
            refine ⟨15432664570155924508969687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82307544374164930714504997 15432664570155924508969687)
            ·
              refine ⟨23148996855233886763454531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15432664570155924508969687 23148996855233886763454531)
              ·
                refine ⟨34723495282850830145181797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23148996855233886763454531 34723495282850830145181797)
                ·
                  refine ⟨6510655365534530652221587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34723495282850830145181797 6510655365534530652221587)
                  ·
                    refine ⟨9765983048301795978332381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510655365534530652221587 9765983048301795978332381)
                    ·
                      refine ⟨3662243643113173491874643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9765983048301795978332381 3662243643113173491874643)
                      ·
                        rfl

theorem cell23_7132194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_7132194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132194 prefixEnd_7132194 := by exact prefixLift 7132194
  have htrace : WordTrace (prefixWord ++ tailWord_7132194) baseStart_7132194 baseEnd_7132194 := by
    simpa [prefixWord, tailWord_7132194, baseEnd_7132194] using wordTrace_append hprefix tailTrace_7132194
  have hstable : (prefixWord ++ tailWord_7132194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132194).length < 2 ^ (prefixWord ++ tailWord_7132194).sum := by decide
  have hdescent : baseEnd_7132194 < baseStart_7132194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132210 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_7132210 : Nat := 118140960795 + 7132210 * 2 ^ 59
def prefixEnd_7132210 : Nat := 4983230072969 + 3 ^ 40 * 7132210 * 2
def baseEnd_7132210 : Nat := 1220750619601215143091523

theorem tailTrace_7132210 : CollatzResearch.WordTrace tailWord_7132210 prefixEnd_7132210 1220750619601215143091523 := by
  unfold tailWord_7132210
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033267372807182334112521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173422046327485819557633389 65033267372807182334112521)
  ·
    refine ⟨48774950529605386750584391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65033267372807182334112521 48774950529605386750584391)
    ·
      refine ⟨73162425794408080125876587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48774950529605386750584391 73162425794408080125876587)
      ·
        refine ⟨109743638691612120188814881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73162425794408080125876587 109743638691612120188814881)
        ·
          refine ⟨82307729018709090141611161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109743638691612120188814881 82307729018709090141611161)
          ·
            refine ⟨61730796764031817606208371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82307729018709090141611161 61730796764031817606208371)
            ·
              refine ⟨92596195146047726409312557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61730796764031817606208371 92596195146047726409312557)
              ·
                refine ⟨34723573179767897403492209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92596195146047726409312557 34723573179767897403492209)
                ·
                  refine ⟨26042679884825923052619157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34723573179767897403492209 26042679884825923052619157)
                  ·
                    refine ⟨1220750619601215143091523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26042679884825923052619157 1220750619601215143091523)
                    ·
                      rfl

theorem cell23_7132210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_7132210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132210 prefixEnd_7132210 := by exact prefixLift 7132210
  have htrace : WordTrace (prefixWord ++ tailWord_7132210) baseStart_7132210 baseEnd_7132210 := by
    simpa [prefixWord, tailWord_7132210, baseEnd_7132210] using wordTrace_append hprefix tailTrace_7132210
  have hstable : (prefixWord ++ tailWord_7132210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132210).length < 2 ^ (prefixWord ++ tailWord_7132210).sum := by decide
  have hdescent : baseEnd_7132210 < baseStart_7132210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132221 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7132221 : Nat := 118140960795 + 7132221 * 2 ^ 59
def prefixEnd_7132221 : Nat := 4983230072969 + 3 ^ 40 * 7132221 * 2
def baseEnd_7132221 : Nat := 3662257507090844886237019

theorem tailTrace_7132221 : CollatzResearch.WordTrace tailWord_7132221 prefixEnd_7132221 3662257507090844886237019 := by
  unfold tailWord_7132221
  simp only [CollatzResearch.WordTrace]
  refine ⟨260133470694188878215100517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173422313796125918810067011 260133470694188878215100517)
  ·
    refine ⟨48775025755160414665331347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 260133470694188878215100517 48775025755160414665331347)
    ·
      refine ⟨73162538632740621997997021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48775025755160414665331347 73162538632740621997997021)
      ·
        refine ⟨27435951987277733249248883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73162538632740621997997021 27435951987277733249248883)
        ·
          refine ⟨41153927980916599873873325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27435951987277733249248883 41153927980916599873873325)
          ·
            refine ⟨15432722992843724952702497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41153927980916599873873325 15432722992843724952702497)
            ·
              refine ⟨11574542244632793714526873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15432722992843724952702497 11574542244632793714526873)
              ·
                refine ⟨8680906683474595285895155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11574542244632793714526873 8680906683474595285895155)
                ·
                  refine ⟨13021360025211892928842733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8680906683474595285895155 13021360025211892928842733)
                  ·
                    refine ⟨4883010009454459848316025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13021360025211892928842733 4883010009454459848316025)
                    ·
                      refine ⟨3662257507090844886237019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883010009454459848316025 3662257507090844886237019)
                      ·
                        rfl

theorem cell23_7132221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7132221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132221 prefixEnd_7132221 := by exact prefixLift 7132221
  have htrace : WordTrace (prefixWord ++ tailWord_7132221) baseStart_7132221 baseEnd_7132221 := by
    simpa [prefixWord, tailWord_7132221, baseEnd_7132221] using wordTrace_append hprefix tailTrace_7132221
  have hstable : (prefixWord ++ tailWord_7132221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132221).length < 2 ^ (prefixWord ++ tailWord_7132221).sum := by decide
  have hdescent : baseEnd_7132221 < baseStart_7132221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132234 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_7132234 : Nat := 118140960795 + 7132234 * 2 ^ 59
def prefixEnd_7132234 : Nat := 4983230072969 + 3 ^ 40 * 7132234 * 2
def baseEnd_7132234 : Nat := 3662264182339353335374459

theorem tailTrace_7132234 : CollatzResearch.WordTrace tailWord_7132234 prefixEnd_7132234 3662264182339353335374459 := by
  unfold tailWord_7132234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033486210785445358830939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173422629895427854290215837 65033486210785445358830939)
  ·
    refine ⟨97550229316178168038246409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65033486210785445358830939 97550229316178168038246409)
    ·
      refine ⟨73162671987133626028684807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97550229316178168038246409 73162671987133626028684807)
      ·
        refine ⟨109744007980700439043027211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73162671987133626028684807 109744007980700439043027211)
        ·
          refine ⟨164616011971050658564540817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109744007980700439043027211 164616011971050658564540817)
          ·
            refine ⟨123462008978287993923405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164616011971050658564540817 123462008978287993923405613)
            ·
              refine ⟨46298253366857997721277105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123462008978287993923405613 46298253366857997721277105)
              ·
                refine ⟨34723690025143498290957829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46298253366857997721277105 34723690025143498290957829)
                ·
                  refine ⟨6510691879714405929554593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34723690025143498290957829 6510691879714405929554593)
                  ·
                    refine ⟨4883018909785804447165945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6510691879714405929554593 4883018909785804447165945)
                    ·
                      refine ⟨3662264182339353335374459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883018909785804447165945 3662264182339353335374459)
                      ·
                        rfl

theorem cell23_7132234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_7132234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132234 prefixEnd_7132234 := by exact prefixLift 7132234
  have htrace : WordTrace (prefixWord ++ tailWord_7132234) baseStart_7132234 baseEnd_7132234 := by
    simpa [prefixWord, tailWord_7132234, baseEnd_7132234] using wordTrace_append hprefix tailTrace_7132234
  have hstable : (prefixWord ++ tailWord_7132234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132234).length < 2 ^ (prefixWord ++ tailWord_7132234).sum := by decide
  have hdescent : baseEnd_7132234 < baseStart_7132234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132237 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7132237 : Nat := 118140960795 + 7132237 * 2 ^ 59
def prefixEnd_7132237 : Nat := 4983230072969 + 3 ^ 40 * 7132237 * 2
def baseEnd_7132237 : Nat := 3662265722781316823636945

theorem tailTrace_7132237 : CollatzResearch.WordTrace tailWord_7132237 prefixEnd_7132237 3662265722781316823636945 := by
  unfold tailWord_7132237
  simp only [CollatzResearch.WordTrace]
  refine ⟨260134054262130912947682965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173422702841420608631788643 260134054262130912947682965)
  ·
    refine ⟨12193783793537386544422639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 260134054262130912947682965 12193783793537386544422639)
    ·
      refine ⟨18290675690306079816633959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12193783793537386544422639 18290675690306079816633959)
      ·
        refine ⟨27436013535459119724950939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18290675690306079816633959 27436013535459119724950939)
        ·
          refine ⟨41154020303188679587426409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27436013535459119724950939 41154020303188679587426409)
          ·
            refine ⟨30865515227391509690569807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41154020303188679587426409 30865515227391509690569807)
            ·
              refine ⟨46298272841087264535854711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30865515227391509690569807 46298272841087264535854711)
              ·
                refine ⟨69447409261630896803782067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46298272841087264535854711 69447409261630896803782067)
                ·
                  refine ⟨104171113892446345205673101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69447409261630896803782067 104171113892446345205673101)
                  ·
                    refine ⟨39064167709667379452127413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104171113892446345205673101 39064167709667379452127413)
                    ·
                      refine ⟨3662265722781316823636945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39064167709667379452127413 3662265722781316823636945)
                      ·
                        rfl

theorem cell23_7132237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7132237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132237 prefixEnd_7132237 := by exact prefixLift 7132237
  have htrace : WordTrace (prefixWord ++ tailWord_7132237) baseStart_7132237 baseEnd_7132237 := by
    simpa [prefixWord, tailWord_7132237, baseEnd_7132237] using wordTrace_append hprefix tailTrace_7132237
  have hstable : (prefixWord ++ tailWord_7132237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132237).length < 2 ^ (prefixWord ++ tailWord_7132237).sum := by decide
  have hdescent : baseEnd_7132237 < baseStart_7132237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132257 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 5]
def baseStart_7132257 : Nat := 118140960795 + 7132257 * 2 ^ 59
def prefixEnd_7132257 : Nat := 4983230072969 + 3 ^ 40 * 7132257 * 2
def baseEnd_7132257 : Nat := 406919554710489638376317

theorem tailTrace_7132257 : CollatzResearch.WordTrace tailWord_7132257 prefixEnd_7132257 406919554710489638376317 := by
  unfold tailWord_7132257
  simp only [CollatzResearch.WordTrace]
  refine ⟨260134783722058456363411025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173423189148038970908940683 260134783722058456363411025)
  ·
    refine ⟨195101087791543842272558269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260134783722058456363411025 195101087791543842272558269)
    ·
      refine ⟨73162907921828940852209351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195101087791543842272558269 73162907921828940852209351)
      ·
        refine ⟨109744361882743411278314027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73162907921828940852209351 109744361882743411278314027)
        ·
          refine ⟨164616542824115116917471041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109744361882743411278314027 164616542824115116917471041)
          ·
            refine ⟨123462407118086337688103281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164616542824115116917471041 123462407118086337688103281)
            ·
              refine ⟨92596805338564753266077461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123462407118086337688103281 92596805338564753266077461)
              ·
                refine ⟨4340475250245222809347381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92596805338564753266077461 4340475250245222809347381)
                ·
                  refine ⟨406919554710489638376317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340475250245222809347381 406919554710489638376317)
                  ·
                    rfl

theorem cell23_7132257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 5].length) (baseStart_7132257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132257 prefixEnd_7132257 := by exact prefixLift 7132257
  have htrace : WordTrace (prefixWord ++ tailWord_7132257) baseStart_7132257 baseEnd_7132257 := by
    simpa [prefixWord, tailWord_7132257, baseEnd_7132257] using wordTrace_append hprefix tailTrace_7132257
  have hstable : (prefixWord ++ tailWord_7132257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132257).length < 2 ^ (prefixWord ++ tailWord_7132257).sum := by decide
  have hdescent : baseEnd_7132257 < baseStart_7132257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132307 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4]
def baseStart_7132307 : Nat := 118140960795 + 7132307 * 2 ^ 59
def prefixEnd_7132307 : Nat := 4983230072969 + 3 ^ 40 * 7132307 * 2
def baseEnd_7132307 : Nat := 3662301666427131549761623

theorem tailTrace_7132307 : CollatzResearch.WordTrace tailWord_7132307 prefixEnd_7132307 3662301666427131549761623 := by
  unfold tailWord_7132307
  simp only [CollatzResearch.WordTrace]
  refine ⟨260136607371877314902731175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173424404914584876601820783 260136607371877314902731175)
  ·
    refine ⟨390204911057815972354096763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260136607371877314902731175 390204911057815972354096763)
    ·
      refine ⟨585307366586723958531145145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390204911057815972354096763 585307366586723958531145145)
      ·
        refine ⟨438980524940042968898358859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585307366586723958531145145 438980524940042968898358859)
        ·
          refine ⟨658470787410064453347538289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438980524940042968898358859 658470787410064453347538289)
          ·
            refine ⟨493853090557548340010653717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658470787410064453347538289 493853090557548340010653717)
            ·
              refine ⟨23149363619885078437999393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 493853090557548340010653717 23149363619885078437999393)
              ·
                refine ⟨17362022714913808828499545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23149363619885078437999393 17362022714913808828499545)
                ·
                  refine ⟨13021517036185356621374659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17362022714913808828499545 13021517036185356621374659)
                  ·
                    refine ⟨19532275554278034932061989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13021517036185356621374659 19532275554278034932061989)
                    ·
                      refine ⟨3662301666427131549761623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19532275554278034932061989 3662301666427131549761623)
                      ·
                        rfl

theorem cell23_7132307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_7132307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132307 prefixEnd_7132307 := by exact prefixLift 7132307
  have htrace : WordTrace (prefixWord ++ tailWord_7132307) baseStart_7132307 baseEnd_7132307 := by
    simpa [prefixWord, tailWord_7132307, baseEnd_7132307] using wordTrace_append hprefix tailTrace_7132307
  have hstable : (prefixWord ++ tailWord_7132307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132307).length < 2 ^ (prefixWord ++ tailWord_7132307).sum := by decide
  have hdescent : baseEnd_7132307 < baseStart_7132307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132324 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_7132324 : Nat := 118140960795 + 7132324 * 2 ^ 59
def prefixEnd_7132324 : Nat := 4983230072969 + 3 ^ 40 * 7132324 * 2
def baseEnd_7132324 : Nat := 3662310395598257983249045

theorem tailTrace_7132324 : CollatzResearch.WordTrace tailWord_7132324 prefixEnd_7132324 3662310395598257983249045 := by
  unfold tailWord_7132324
  simp only [CollatzResearch.WordTrace]
  refine ⟨130068613706407863403050013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173424818275210484537400017 130068613706407863403050013)
  ·
    refine ⟨48775730139902948776143755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130068613706407863403050013 48775730139902948776143755)
    ·
      refine ⟨73163595209854423164215633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48775730139902948776143755 73163595209854423164215633)
      ·
        refine ⟨54872696407390817373161725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73163595209854423164215633 54872696407390817373161725)
        ·
          refine ⟨20577261152771556514935647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54872696407390817373161725 20577261152771556514935647)
          ·
            refine ⟨30865891729157334772403471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20577261152771556514935647 30865891729157334772403471)
            ·
              refine ⟨46298837593736002158605207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30865891729157334772403471 46298837593736002158605207)
              ·
                refine ⟨69448256390604003237907811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46298837593736002158605207 69448256390604003237907811)
                ·
                  refine ⟨104172384585906004856861717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69448256390604003237907811 104172384585906004856861717)
                  ·
                    refine ⟨4883080527464343977665393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104172384585906004856861717 4883080527464343977665393)
                    ·
                      refine ⟨3662310395598257983249045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883080527464343977665393 3662310395598257983249045)
                      ·
                        rfl

theorem cell23_7132324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_7132324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132324 prefixEnd_7132324 := by exact prefixLift 7132324
  have htrace : WordTrace (prefixWord ++ tailWord_7132324) baseStart_7132324 baseEnd_7132324 := by
    simpa [prefixWord, tailWord_7132324, baseEnd_7132324] using wordTrace_append hprefix tailTrace_7132324
  have hstable : (prefixWord ++ tailWord_7132324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132324).length < 2 ^ (prefixWord ++ tailWord_7132324).sum := by decide
  have hdescent : baseEnd_7132324 < baseStart_7132324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132384 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2]
def baseStart_7132384 : Nat := 118140960795 + 7132384 * 2 ^ 59
def prefixEnd_7132384 : Nat := 4983230072969 + 3 ^ 40 * 7132384 * 2
def baseEnd_7132384 : Nat := 3662341204437527748498769

theorem tailTrace_7132384 : CollatzResearch.WordTrace tailWord_7132384 prefixEnd_7132384 3662341204437527748498769 := by
  unfold tailWord_7132384
  simp only [CollatzResearch.WordTrace]
  refine ⟨130069707896299178526642103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173426277195065571368856137 130069707896299178526642103)
  ·
    refine ⟨195104561844448767789963155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130069707896299178526642103 195104561844448767789963155)
    ·
      refine ⟨292656842766673151684944733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195104561844448767789963155 292656842766673151684944733)
      ·
        refine ⟨109746316037502431881854275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292656842766673151684944733 109746316037502431881854275)
        ·
          refine ⟨164619474056253647822781413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109746316037502431881854275 164619474056253647822781413)
          ·
            refine ⟨30866151385547558966771515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164619474056253647822781413 30866151385547558966771515)
            ·
              refine ⟨46299227078321338450157273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866151385547558966771515 46299227078321338450157273)
              ·
                refine ⟨34724420308741003837617955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46299227078321338450157273 34724420308741003837617955)
                ·
                  refine ⟨52086630463111505756426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34724420308741003837617955 52086630463111505756426933)
                  ·
                    refine ⟨4883121605916703664665025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52086630463111505756426933 4883121605916703664665025)
                    ·
                      refine ⟨3662341204437527748498769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883121605916703664665025 3662341204437527748498769)
                      ·
                        rfl

theorem cell23_7132384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_7132384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132384 prefixEnd_7132384 := by exact prefixLift 7132384
  have htrace : WordTrace (prefixWord ++ tailWord_7132384) baseStart_7132384 baseEnd_7132384 := by
    simpa [prefixWord, tailWord_7132384, baseEnd_7132384] using wordTrace_append hprefix tailTrace_7132384
  have hstable : (prefixWord ++ tailWord_7132384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132384).length < 2 ^ (prefixWord ++ tailWord_7132384).sum := by decide
  have hdescent : baseEnd_7132384 < baseStart_7132384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132394 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7132394 : Nat := 118140960795 + 7132394 * 2 ^ 59
def prefixEnd_7132394 : Nat := 4983230072969 + 3 ^ 40 * 7132394 * 2
def baseEnd_7132394 : Nat := 1220782113081357569791241

theorem tailTrace_7132394 : CollatzResearch.WordTrace tailWord_7132394 prefixEnd_7132394 1220782113081357569791241 := by
  unfold tailWord_7132394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65034945130640532190287059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173426520348374752507432157 65034945130640532190287059)
  ·
    refine ⟨97552417695960798285430589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65034945130640532190287059 97552417695960798285430589)
    ·
      refine ⟨36582156635985299357036471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97552417695960798285430589 36582156635985299357036471)
      ·
        refine ⟨54873234953977949035554707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36582156635985299357036471 54873234953977949035554707)
        ·
          refine ⟨82309852430966923553332061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54873234953977949035554707 82309852430966923553332061)
          ·
            refine ⟨30866194661612596332499523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82309852430966923553332061 30866194661612596332499523)
            ·
              refine ⟨46299291992418894498749285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866194661612596332499523 46299291992418894498749285)
              ·
                refine ⟨8681117248578542718515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46299291992418894498749285 8681117248578542718515491)
                ·
                  refine ⟨13021675872867814077773237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681117248578542718515491 13021675872867814077773237)
                  ·
                    refine ⟨1220782113081357569791241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13021675872867814077773237 1220782113081357569791241)
                    ·
                      rfl

theorem cell23_7132394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7132394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132394 prefixEnd_7132394 := by exact prefixLift 7132394
  have htrace : WordTrace (prefixWord ++ tailWord_7132394) baseStart_7132394 baseEnd_7132394 := by
    simpa [prefixWord, tailWord_7132394, baseEnd_7132394] using wordTrace_append hprefix tailTrace_7132394
  have hstable : (prefixWord ++ tailWord_7132394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132394).length < 2 ^ (prefixWord ++ tailWord_7132394).sum := by decide
  have hdescent : baseEnd_7132394 < baseStart_7132394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132427 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_7132427 : Nat := 118140960795 + 7132427 * 2 ^ 59
def prefixEnd_7132427 : Nat := 4983230072969 + 3 ^ 40 * 7132427 * 2
def baseEnd_7132427 : Nat := 3662363284105671080261071

theorem tailTrace_7132427 : CollatzResearch.WordTrace tailWord_7132427 prefixEnd_7132427 3662363284105671080261071 := by
  unfold tailWord_7132427
  simp only [CollatzResearch.WordTrace]
  refine ⟨260140984131442575397099535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173427322754295050264733023 260140984131442575397099535)
  ·
    refine ⟨390211476197163863095649303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260140984131442575397099535 390211476197163863095649303)
    ·
      refine ⟨585317214295745794643473955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390211476197163863095649303 585317214295745794643473955)
      ·
        refine ⟨877975821443618691965210933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585317214295745794643473955 877975821443618691965210933)
        ·
          refine ⟨82310233260339252371738525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 877975821443618691965210933 82310233260339252371738525)
          ·
            refine ⟨30866337472627219639401947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82310233260339252371738525 30866337472627219639401947)
            ·
              refine ⟨46299506208940829459102921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866337472627219639401947 46299506208940829459102921)
              ·
                refine ⟨34724629656705622094327191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46299506208940829459102921 34724629656705622094327191)
                ·
                  refine ⟨52086944485058433141490787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34724629656705622094327191 52086944485058433141490787)
                  ·
                    refine ⟨78130416727587649712236181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52086944485058433141490787 78130416727587649712236181)
                    ·
                      refine ⟨3662363284105671080261071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78130416727587649712236181 3662363284105671080261071)
                      ·
                        rfl

theorem cell23_7132427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_7132427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132427 prefixEnd_7132427 := by exact prefixLift 7132427
  have htrace : WordTrace (prefixWord ++ tailWord_7132427) baseStart_7132427 baseEnd_7132427 := by
    simpa [prefixWord, tailWord_7132427, baseEnd_7132427] using wordTrace_append hprefix tailTrace_7132427
  have hstable : (prefixWord ++ tailWord_7132427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132427).length < 2 ^ (prefixWord ++ tailWord_7132427).sum := by decide
  have hdescent : baseEnd_7132427 < baseStart_7132427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132448 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7132448 : Nat := 118140960795 + 7132448 * 2 ^ 59
def prefixEnd_7132448 : Nat := 4983230072969 + 3 ^ 40 * 7132448 * 2
def baseEnd_7132448 : Nat := 3662374067199415498098475

theorem tailTrace_7132448 : CollatzResearch.WordTrace tailWord_7132448 prefixEnd_7132448 3662374067199415498098475 := by
  unfold tailWord_7132448
  simp only [CollatzResearch.WordTrace]
  refine ⟨130070875032183247991806999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173427833376244330655742665 130070875032183247991806999)
  ·
    refine ⟨195106312548274871987710499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130070875032183247991806999 195106312548274871987710499)
    ·
      refine ⟨292659468822412307981565749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195106312548274871987710499 292659468822412307981565749)
      ·
        refine ⟨27436825202101153873271789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292659468822412307981565749 27436825202101153873271789)
        ·
          refine ⟨10288809450787932702476921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27436825202101153873271789 10288809450787932702476921)
          ·
            refine ⟨7716607088090949526857691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288809450787932702476921 7716607088090949526857691)
            ·
              refine ⟨11574910632136424290286537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716607088090949526857691 11574910632136424290286537)
              ·
                refine ⟨8681182974102318217714903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11574910632136424290286537 8681182974102318217714903)
                ·
                  refine ⟨13021774461153477326572355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681182974102318217714903 13021774461153477326572355)
                  ·
                    refine ⟨19532661691730215989858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13021774461153477326572355 19532661691730215989858533)
                    ·
                      refine ⟨3662374067199415498098475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19532661691730215989858533 3662374067199415498098475)
                      ·
                        rfl

theorem cell23_7132448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7132448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132448 prefixEnd_7132448 := by exact prefixLift 7132448
  have htrace : WordTrace (prefixWord ++ tailWord_7132448) baseStart_7132448 baseEnd_7132448 := by
    simpa [prefixWord, tailWord_7132448, baseEnd_7132448] using wordTrace_append hprefix tailTrace_7132448
  have hstable : (prefixWord ++ tailWord_7132448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132448).length < 2 ^ (prefixWord ++ tailWord_7132448).sum := by decide
  have hdescent : baseEnd_7132448 < baseStart_7132448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132451 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 3]
def baseStart_7132451 : Nat := 118140960795 + 7132451 * 2 ^ 59
def prefixEnd_7132451 : Nat := 4983230072969 + 3 ^ 40 * 7132451 * 2
def baseEnd_7132451 : Nat := 3662375607641378986360961

theorem tailTrace_7132451 : CollatzResearch.WordTrace tailWord_7132451 prefixEnd_7132451 3662375607641378986360961 := by
  unfold tailWord_7132451
  simp only [CollatzResearch.WordTrace]
  refine ⟨260141859483355627495973207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173427906322237084997315471 260141859483355627495973207)
  ·
    refine ⟨390212789225033441243959811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260141859483355627495973207 390212789225033441243959811)
    ·
      refine ⟨585319183837550161865939717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390212789225033441243959811 585319183837550161865939717)
      ·
        refine ⟨109747346969540655349863697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585319183837550161865939717 109747346969540655349863697)
        ·
          refine ⟨82310510227155491512397773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109747346969540655349863697 82310510227155491512397773)
          ·
            refine ⟨30866441335183309317149165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82310510227155491512397773 30866441335183309317149165)
            ·
              refine ⟨11574915500693740993930937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30866441335183309317149165 11574915500693740993930937)
              ·
                refine ⟨8681186625520305745448203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11574915500693740993930937 8681186625520305745448203)
                ·
                  refine ⟨13021779938280458618172305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681186625520305745448203 13021779938280458618172305)
                  ·
                    refine ⟨9766334953710343963629229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13021779938280458618172305 9766334953710343963629229)
                    ·
                      refine ⟨3662375607641378986360961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9766334953710343963629229 3662375607641378986360961)
                      ·
                        rfl

theorem cell23_7132451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_7132451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132451 prefixEnd_7132451 := by exact prefixLift 7132451
  have htrace : WordTrace (prefixWord ++ tailWord_7132451) baseStart_7132451 baseEnd_7132451 := by
    simpa [prefixWord, tailWord_7132451, baseEnd_7132451] using wordTrace_append hprefix tailTrace_7132451
  have hstable : (prefixWord ++ tailWord_7132451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132451).length < 2 ^ (prefixWord ++ tailWord_7132451).sum := by decide
  have hdescent : baseEnd_7132451 < baseStart_7132451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132461 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7132461 : Nat := 118140960795 + 7132461 * 2 ^ 59
def prefixEnd_7132461 : Nat := 4983230072969 + 3 ^ 40 * 7132461 * 2
def baseEnd_7132461 : Nat := 3662380742447923947235915

theorem tailTrace_7132461 : CollatzResearch.WordTrace tailWord_7132461 prefixEnd_7132461 3662380742447923947235915 := by
  unfold tailWord_7132461
  simp only [CollatzResearch.WordTrace]
  refine ⟨260142224213319399203837237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173428149475546266135891491 260142224213319399203837237)
  ·
    refine ⟨24388333519998693675359741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260142224213319399203837237 24388333519998693675359741)
    ·
      refine ⟨9145625069999510128259903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24388333519998693675359741 9145625069999510128259903)
      ·
        refine ⟨13718437604999265192389855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145625069999510128259903 13718437604999265192389855)
        ·
          refine ⟨20577656407498897788584783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718437604999265192389855 20577656407498897788584783)
          ·
            refine ⟨30866484611248346682877175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20577656407498897788584783 30866484611248346682877175)
            ·
              refine ⟨46299726916872520024315763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30866484611248346682877175 46299726916872520024315763)
              ·
                refine ⟨69449590375308780036473645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46299726916872520024315763 69449590375308780036473645)
                ·
                  refine ⟨26043596390740792513677617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69449590375308780036473645 26043596390740792513677617)
                  ·
                    refine ⟨19532697293055594385258213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26043596390740792513677617 19532697293055594385258213)
                    ·
                      refine ⟨3662380742447923947235915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19532697293055594385258213 3662380742447923947235915)
                      ·
                        rfl

theorem cell23_7132461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7132461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132461 prefixEnd_7132461 := by exact prefixLift 7132461
  have htrace : WordTrace (prefixWord ++ tailWord_7132461) baseStart_7132461 baseEnd_7132461 := by
    simpa [prefixWord, tailWord_7132461, baseEnd_7132461] using wordTrace_append hprefix tailTrace_7132461
  have hstable : (prefixWord ++ tailWord_7132461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132461).length < 2 ^ (prefixWord ++ tailWord_7132461).sum := by decide
  have hdescent : baseEnd_7132461 < baseStart_7132461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132464 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_7132464 : Nat := 118140960795 + 7132464 * 2 ^ 59
def prefixEnd_7132464 : Nat := 4983230072969 + 3 ^ 40 * 7132464 * 2
def baseEnd_7132464 : Nat := 3662382282889887435498401

theorem tailTrace_7132464 : CollatzResearch.WordTrace tailWord_7132464 prefixEnd_7132464 3662382282889887435498401 := by
  unfold tailWord_7132464
  simp only [CollatzResearch.WordTrace]
  refine ⟨130071166816154265358098223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173428222421539020477464297 130071166816154265358098223)
  ·
    refine ⟨195106750224231398037147335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130071166816154265358098223 195106750224231398037147335)
    ·
      refine ⟨292660125336347097055721003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195106750224231398037147335 292660125336347097055721003)
      ·
        refine ⟨438990188004520645583581505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292660125336347097055721003 438990188004520645583581505)
        ·
          refine ⟨329242641003390484187686129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438990188004520645583581505 329242641003390484187686129)
          ·
            refine ⟨246931980752542863140764597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329242641003390484187686129 246931980752542863140764597)
            ·
              refine ⟨23149873195550893419446681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246931980752542863140764597 23149873195550893419446681)
              ·
                refine ⟨17362404896663170064585011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23149873195550893419446681 17362404896663170064585011)
                ·
                  refine ⟨26043607344994755096877517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17362404896663170064585011 26043607344994755096877517)
                  ·
                    refine ⟨9766352754373033161329069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26043607344994755096877517 9766352754373033161329069)
                    ·
                      refine ⟨3662382282889887435498401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9766352754373033161329069 3662382282889887435498401)
                      ·
                        rfl

theorem cell23_7132464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_7132464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132464 prefixEnd_7132464 := by exact prefixLift 7132464
  have htrace : WordTrace (prefixWord ++ tailWord_7132464) baseStart_7132464 baseEnd_7132464 := by
    simpa [prefixWord, tailWord_7132464, baseEnd_7132464] using wordTrace_append hprefix tailTrace_7132464
  have hstable : (prefixWord ++ tailWord_7132464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132464).length < 2 ^ (prefixWord ++ tailWord_7132464).sum := by decide
  have hdescent : baseEnd_7132464 < baseStart_7132464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132514 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7132514 : Nat := 118140960795 + 7132514 * 2 ^ 59
def prefixEnd_7132514 : Nat := 4983230072969 + 3 ^ 40 * 7132514 * 2
def baseEnd_7132514 : Nat := 1220802652307537413291057

theorem tailTrace_7132514 : CollatzResearch.WordTrace tailWord_7132514 prefixEnd_7132514 1220802652307537413291057 := by
  unfold tailWord_7132514
  simp only [CollatzResearch.WordTrace]
  refine ⟨65036039320531847313879149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173429438188084926170344397 65036039320531847313879149)
  ·
    refine ⟨24388514745199442742704681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65036039320531847313879149 24388514745199442742704681)
    ·
      refine ⟨18291386058899582057028511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24388514745199442742704681 18291386058899582057028511)
      ·
        refine ⟨27437079088349373085542767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18291386058899582057028511 27437079088349373085542767)
        ·
          refine ⟨41155618632524059628314151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27437079088349373085542767 41155618632524059628314151)
          ·
            refine ⟨61733427948786089442471227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41155618632524059628314151 61733427948786089442471227)
            ·
              refine ⟨92600141923179134163706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61733427948786089442471227 92600141923179134163706841)
              ·
                refine ⟨69450106442384350622780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92600141923179134163706841 69450106442384350622780131)
                ·
                  refine ⟨104175159663576525934170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69450106442384350622780131 104175159663576525934170197)
                  ·
                    refine ⟨1220802652307537413291057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104175159663576525934170197 1220802652307537413291057)
                    ·
                      rfl

theorem cell23_7132514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7132514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132514 prefixEnd_7132514 := by exact prefixLift 7132514
  have htrace : WordTrace (prefixWord ++ tailWord_7132514) baseStart_7132514 baseEnd_7132514 := by
    simpa [prefixWord, tailWord_7132514, baseEnd_7132514] using wordTrace_append hprefix tailTrace_7132514
  have hstable : (prefixWord ++ tailWord_7132514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132514).length < 2 ^ (prefixWord ++ tailWord_7132514).sum := by decide
  have hdescent : baseEnd_7132514 < baseStart_7132514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7132525 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7132525 : Nat := 118140960795 + 7132525 * 2 ^ 59
def prefixEnd_7132525 : Nat := 4983230072969 + 3 ^ 40 * 7132525 * 2
def baseEnd_7132525 : Nat := 3662413605209811696835621

theorem tailTrace_7132525 : CollatzResearch.WordTrace tailWord_7132525 prefixEnd_7132525 3662413605209811696835621 := by
  unfold tailWord_7132525
  simp only [CollatzResearch.WordTrace]
  refine ⟨260144558485087538134167029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173429705656725025422778019 260144558485087538134167029)
  ·
    refine ⟨24388552357976956700078159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 260144558485087538134167029 24388552357976956700078159)
    ·
      refine ⟨36582828536965435050117239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24388552357976956700078159 36582828536965435050117239)
      ·
        refine ⟨54874242805448152575175859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36582828536965435050117239 54874242805448152575175859)
        ·
          refine ⟨82311364208172228862763789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54874242805448152575175859 82311364208172228862763789)
          ·
            refine ⟨30866761578064585823536421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82311364208172228862763789 30866761578064585823536421)
            ·
              refine ⟨5787517795887109841913079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30866761578064585823536421 5787517795887109841913079)
              ·
                refine ⟨8681276693830664762869619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787517795887109841913079 8681276693830664762869619)
                ·
                  refine ⟨13021915040745997144304429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8681276693830664762869619 13021915040745997144304429)
                  ·
                    refine ⟨4883218140279748929114161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13021915040745997144304429 4883218140279748929114161)
                    ·
                      refine ⟨3662413605209811696835621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4883218140279748929114161 3662413605209811696835621)
                      ·
                        rfl

theorem cell23_7132525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7132525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7132525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7132525 prefixEnd_7132525 := by exact prefixLift 7132525
  have htrace : WordTrace (prefixWord ++ tailWord_7132525) baseStart_7132525 baseEnd_7132525 := by
    simpa [prefixWord, tailWord_7132525, baseEnd_7132525] using wordTrace_append hprefix tailTrace_7132525
  have hstable : (prefixWord ++ tailWord_7132525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7132525).length < 2 ^ (prefixWord ++ tailWord_7132525).sum := by decide
  have hdescent : baseEnd_7132525 < baseStart_7132525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7132525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
