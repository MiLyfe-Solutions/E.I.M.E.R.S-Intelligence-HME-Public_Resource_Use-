import V185TrunkScan22Chunk329

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2944086 : List Nat := [5, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2944086 : Nat := 118140960795 + 2944086 * 2 ^ 59
def prefixEnd_2944086 : Nat := 4983230072969 + 3 ^ 40 * 2944086 * 2
def baseEnd_2944086 : Nat := 111980089346138776569289

theorem tailTrace_2944086 : CollatzResearch.WordTrace tailWord_2944086 prefixEnd_2944086 111980089346138776569289 := by
  unfold tailWord_2944086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711227375755419168948257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71586425341391137802114741 6711227375755419168948257)
  ·
    refine ⟨5033420531816564376711193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6711227375755419168948257 5033420531816564376711193)
    ·
      refine ⟨3775065398862423282533395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5033420531816564376711193 3775065398862423282533395)
      ·
        refine ⟨5662598098293634923800093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775065398862423282533395 5662598098293634923800093)
        ·
          refine ⟨2123474286860113096425035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5662598098293634923800093 2123474286860113096425035)
          ·
            refine ⟨3185211430290169644637553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123474286860113096425035 3185211430290169644637553)
            ·
              refine ⟨2388908572717627233478165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185211430290169644637553 2388908572717627233478165)
              ·
                refine ⟨111980089346138776569289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2388908572717627233478165 111980089346138776569289)
                ·
                  rfl

theorem cell22_2944086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2944086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944086 prefixEnd_2944086 := by exact prefixLift 2944086
  have htrace : WordTrace (prefixWord ++ tailWord_2944086) baseStart_2944086 baseEnd_2944086 := by
    simpa [prefixWord, tailWord_2944086, baseEnd_2944086] using wordTrace_append hprefix tailTrace_2944086
  have hstable : (prefixWord ++ tailWord_2944086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944086).length < 2 ^ (prefixWord ++ tailWord_2944086).sum := by decide
  have hdescent : baseEnd_2944086 < baseStart_2944086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944170 : List Nat := [3, 1, 5, 1, 1, 11]
def baseStart_2944170 : Nat := 118140960795 + 2944170 * 2 ^ 59
def prefixEnd_2944170 : Nat := 4983230072969 + 3 ^ 40 * 2944170 * 2
def baseEnd_2944170 : Nat := 12442587148541984815103

theorem tailTrace_2944170 : CollatzResearch.WordTrace tailWord_2944170 prefixEnd_2944170 12442587148541984815103 := by
  unfold tailWord_2944170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26845675435945597262307491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71588467829188259366153309 26845675435945597262307491)
  ·
    refine ⟨40268513153918395893461237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26845675435945597262307491 40268513153918395893461237)
    ·
      refine ⟨3775173108179849615011991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40268513153918395893461237 3775173108179849615011991)
      ·
        refine ⟨5662759662269774422517987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775173108179849615011991 5662759662269774422517987)
        ·
          refine ⟨8494139493404661633776981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662759662269774422517987 8494139493404661633776981)
          ·
            refine ⟨12442587148541984815103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8494139493404661633776981 12442587148541984815103)
            ·
              rfl

theorem cell22_2944170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 11].length) (baseStart_2944170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944170 prefixEnd_2944170 := by exact prefixLift 2944170
  have htrace : WordTrace (prefixWord ++ tailWord_2944170) baseStart_2944170 baseEnd_2944170 := by
    simpa [prefixWord, tailWord_2944170, baseEnd_2944170] using wordTrace_append hprefix tailTrace_2944170
  have hstable : (prefixWord ++ tailWord_2944170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944170).length < 2 ^ (prefixWord ++ tailWord_2944170).sum := by decide
  have hdescent : baseEnd_2944170 < baseStart_2944170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944183 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2944183 : Nat := 118140960795 + 2944183 * 2 ^ 59
def prefixEnd_2944183 : Nat := 4983230072969 + 3 ^ 40 * 2944183 * 2
def baseEnd_2944183 : Nat := 1007854009197573069448303

theorem tailTrace_2944183 : CollatzResearch.WordTrace tailWord_2944183 prefixEnd_2944183 1007854009197573069448303 := by
  unfold tailWord_2944183
  simp only [CollatzResearch.WordTrace]
  refine ⟨107383175892735292269453203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71588783928490194846302135 107383175892735292269453203)
  ·
    refine ⟨161074763839102938404179805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107383175892735292269453203 161074763839102938404179805)
    ·
      refine ⟨60403036439663601901567427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161074763839102938404179805 60403036439663601901567427)
      ·
        refine ⟨90604554659495402852351141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60403036439663601901567427 90604554659495402852351141)
        ·
          refine ⟨16988353998655388034815839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90604554659495402852351141 16988353998655388034815839)
          ·
            refine ⟨25482530997983082052223759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988353998655388034815839 25482530997983082052223759)
            ·
              refine ⟨38223796496974623078335639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25482530997983082052223759 38223796496974623078335639)
              ·
                refine ⟨57335694745461934617503459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38223796496974623078335639 57335694745461934617503459)
                ·
                  refine ⟨86003542118192901926255189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57335694745461934617503459 86003542118192901926255189)
                  ·
                    refine ⟨1007854009197573069448303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86003542118192901926255189 1007854009197573069448303)
                    ·
                      rfl

theorem cell22_2944183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2944183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944183 prefixEnd_2944183 := by exact prefixLift 2944183
  have htrace : WordTrace (prefixWord ++ tailWord_2944183) baseStart_2944183 baseEnd_2944183 := by
    simpa [prefixWord, tailWord_2944183, baseEnd_2944183] using wordTrace_append hprefix tailTrace_2944183
  have hstable : (prefixWord ++ tailWord_2944183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944183).length < 2 ^ (prefixWord ++ tailWord_2944183).sum := by decide
  have hdescent : baseEnd_2944183 < baseStart_2944183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944202 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_2944202 : Nat := 118140960795 + 2944202 * 2 ^ 59
def prefixEnd_2944202 : Nat := 4983230072969 + 3 ^ 40 * 2944202 * 2
def baseEnd_2944202 : Nat := 1007860513285863353223245

theorem tailTrace_2944202 : CollatzResearch.WordTrace tailWord_2944202 prefixEnd_2944202 1007860513285863353223245 := by
  unfold tailWord_2944202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26845967219916614628598715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71589245919777639009596573 26845967219916614628598715)
  ·
    refine ⟨40268950829874921942898073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26845967219916614628598715 40268950829874921942898073)
    ·
      refine ⟨30201713122406191457173555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40268950829874921942898073 30201713122406191457173555)
      ·
        refine ⟨45302569683609287185760333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30201713122406191457173555 45302569683609287185760333)
        ·
          refine ⟨16988463631353482694660125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45302569683609287185760333 16988463631353482694660125)
          ·
            refine ⟨6370673861757556010497547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16988463631353482694660125 6370673861757556010497547)
            ·
              refine ⟨9556010792636334015746321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370673861757556010497547 9556010792636334015746321)
              ·
                refine ⟨7167008094477250511809741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9556010792636334015746321 7167008094477250511809741)
                ·
                  refine ⟨2687628035428968941928653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7167008094477250511809741 2687628035428968941928653)
                  ·
                    refine ⟨1007860513285863353223245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687628035428968941928653 1007860513285863353223245)
                    ·
                      rfl

theorem cell22_2944202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_2944202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944202 prefixEnd_2944202 := by exact prefixLift 2944202
  have htrace : WordTrace (prefixWord ++ tailWord_2944202) baseStart_2944202 baseEnd_2944202 := by
    simpa [prefixWord, tailWord_2944202, baseEnd_2944202] using wordTrace_append hprefix tailTrace_2944202
  have hstable : (prefixWord ++ tailWord_2944202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944202).length < 2 ^ (prefixWord ++ tailWord_2944202).sum := by decide
  have hdescent : baseEnd_2944202 < baseStart_2944202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944292 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2944292 : Nat := 118140960795 + 2944292 * 2 ^ 59
def prefixEnd_2944292 : Nat := 4983230072969 + 3 ^ 40 * 2944292 * 2
def baseEnd_2944292 : Nat := 1007891322125133118472969

theorem tailTrace_2944292 : CollatzResearch.WordTrace tailWord_2944292 prefixEnd_2944292 1007891322125133118472969 := by
  unfold tailWord_2944292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53693575724670201942585565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71591434299560269256780753 53693575724670201942585565)
  ·
    refine ⟨20135090896751325728469587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53693575724670201942585565 20135090896751325728469587)
    ·
      refine ⟨30202636345126988592704381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20135090896751325728469587 30202636345126988592704381)
      ·
        refine ⟨11325988629422620722264143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30202636345126988592704381 11325988629422620722264143)
        ·
          refine ⟨16988982944133931083396215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325988629422620722264143 16988982944133931083396215)
          ·
            refine ⟨25483474416200896625094323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988982944133931083396215 25483474416200896625094323)
            ·
              refine ⟨38225211624301344937641485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25483474416200896625094323 38225211624301344937641485)
              ·
                refine ⟨14334454359113004351615557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38225211624301344937641485 14334454359113004351615557)
                ·
                  refine ⟨2687710192333688315927917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14334454359113004351615557 2687710192333688315927917)
                  ·
                    refine ⟨1007891322125133118472969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687710192333688315927917 1007891322125133118472969)
                    ·
                      rfl

theorem cell22_2944292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2944292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944292 prefixEnd_2944292 := by exact prefixLift 2944292
  have htrace : WordTrace (prefixWord ++ tailWord_2944292) baseStart_2944292 baseEnd_2944292 := by
    simpa [prefixWord, tailWord_2944292, baseEnd_2944292] using wordTrace_append hprefix tailTrace_2944292
  have hstable : (prefixWord ++ tailWord_2944292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944292).length < 2 ^ (prefixWord ++ tailWord_2944292).sum := by decide
  have hdescent : baseEnd_2944292 < baseStart_2944292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944305 : List Nat := [1, 2, 2, 3, 3, 1, 1, 9]
def baseStart_2944305 : Nat := 118140960795 + 2944305 * 2 ^ 59
def prefixEnd_2944305 : Nat := 4983230072969 + 3 ^ 40 * 2944305 * 2
def baseEnd_2944305 : Nat := 111988419143422824210881

theorem tailTrace_2944305 : CollatzResearch.WordTrace tailWord_2944305 prefixEnd_2944305 111988419143422824210881 := by
  unfold tailWord_2944305
  simp only [CollatzResearch.WordTrace]
  refine ⟨107387625598293307105394369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71591750398862204736929579 107387625598293307105394369)
  ·
    refine ⟨80540719198719980329045777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107387625598293307105394369 80540719198719980329045777)
    ·
      refine ⟨60405539399039985246784333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80540719198719980329045777 60405539399039985246784333)
      ·
        refine ⟨22652077274639994467544125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60405539399039985246784333 22652077274639994467544125)
        ·
          refine ⟨8494528977989997925329047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22652077274639994467544125 8494528977989997925329047)
          ·
            refine ⟨12741793466984996887993571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494528977989997925329047 12741793466984996887993571)
            ·
              refine ⟨19112690200477495331990357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12741793466984996887993571 19112690200477495331990357)
              ·
                refine ⟨111988419143422824210881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19112690200477495331990357 111988419143422824210881)
                ·
                  rfl

theorem cell22_2944305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 9].length) (baseStart_2944305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944305 prefixEnd_2944305 := by exact prefixLift 2944305
  have htrace : WordTrace (prefixWord ++ tailWord_2944305) baseStart_2944305 baseEnd_2944305 := by
    simpa [prefixWord, tailWord_2944305, baseEnd_2944305] using wordTrace_append hprefix tailTrace_2944305
  have hstable : (prefixWord ++ tailWord_2944305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944305).length < 2 ^ (prefixWord ++ tailWord_2944305).sum := by decide
  have hdescent : baseEnd_2944305 < baseStart_2944305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944309 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2944309 : Nat := 118140960795 + 2944309 * 2 ^ 59
def prefixEnd_2944309 : Nat := 4983230072969 + 3 ^ 40 * 2944309 * 2
def baseEnd_2944309 : Nat := 1007897141572550740797917

theorem tailTrace_2944309 : CollatzResearch.WordTrace tailWord_2944309 prefixEnd_2944309 1007897141572550740797917 := by
  unfold tailWord_2944309
  simp only [CollatzResearch.WordTrace]
  refine ⟨107387771490278815788539981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71591847660185877192359987 107387771490278815788539981)
  ·
    refine ⟨40270414308854555920702493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107387771490278815788539981 40270414308854555920702493)
    ·
      refine ⟨15101405365820458470263435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40270414308854555920702493 15101405365820458470263435)
      ·
        refine ⟨22652108048730687705395153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101405365820458470263435 22652108048730687705395153)
        ·
          refine ⟨16989081036548015779046365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22652108048730687705395153 16989081036548015779046365)
          ·
            refine ⟨6370905388705505917142387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16989081036548015779046365 6370905388705505917142387)
            ·
              refine ⟨9556358083058258875713581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370905388705505917142387 9556358083058258875713581)
              ·
                refine ⟨3583634281146847078392593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9556358083058258875713581 3583634281146847078392593)
                ·
                  refine ⟨2687725710860135308794445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583634281146847078392593 2687725710860135308794445)
                  ·
                    refine ⟨1007897141572550740797917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687725710860135308794445 1007897141572550740797917)
                    ·
                      rfl

theorem cell22_2944309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2944309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944309 prefixEnd_2944309 := by exact prefixLift 2944309
  have htrace : WordTrace (prefixWord ++ tailWord_2944309) baseStart_2944309 baseEnd_2944309 := by
    simpa [prefixWord, tailWord_2944309, baseEnd_2944309] using wordTrace_append hprefix tailTrace_2944309
  have hstable : (prefixWord ++ tailWord_2944309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944309).length < 2 ^ (prefixWord ++ tailWord_2944309).sum := by decide
  have hdescent : baseEnd_2944309 < baseStart_2944309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944324 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2944324 : Nat := 118140960795 + 2944324 * 2 ^ 59
def prefixEnd_2944324 : Nat := 4983230072969 + 3 ^ 40 * 2944324 * 2
def baseEnd_2944324 : Nat := 1007902276379095701672871

theorem tailTrace_2944324 : CollatzResearch.WordTrace tailWord_2944324 prefixEnd_2944324 1007902276379095701672871 := by
  unfold tailWord_2944324
  simp only [CollatzResearch.WordTrace]
  refine ⟨53694159292612236675168013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71592212390149648900224017 53694159292612236675168013)
  ·
    refine ⟨20135309734729588753188005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53694159292612236675168013 20135309734729588753188005)
    ·
      refine ⟨3775370575261797891222751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20135309734729588753188005 3775370575261797891222751)
      ·
        refine ⟨5663055862892696836834127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775370575261797891222751 5663055862892696836834127)
        ·
          refine ⟨8494583794339045255251191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663055862892696836834127 8494583794339045255251191)
          ·
            refine ⟨12741875691508567882876787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494583794339045255251191 12741875691508567882876787)
            ·
              refine ⟨19112813537262851824315181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12741875691508567882876787 19112813537262851824315181)
              ·
                refine ⟨7167305076473569434118193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19112813537262851824315181 7167305076473569434118193)
                ·
                  refine ⟨5375478807355177075588645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167305076473569434118193 5375478807355177075588645)
                  ·
                    refine ⟨1007902276379095701672871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375478807355177075588645 1007902276379095701672871)
                    ·
                      rfl

theorem cell22_2944324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2944324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944324 prefixEnd_2944324 := by exact prefixLift 2944324
  have htrace : WordTrace (prefixWord ++ tailWord_2944324) baseStart_2944324 baseEnd_2944324 := by
    simpa [prefixWord, tailWord_2944324, baseEnd_2944324] using wordTrace_append hprefix tailTrace_2944324
  have hstable : (prefixWord ++ tailWord_2944324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944324).length < 2 ^ (prefixWord ++ tailWord_2944324).sum := by decide
  have hdescent : baseEnd_2944324 < baseStart_2944324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944354 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2944354 : Nat := 118140960795 + 2944354 * 2 ^ 59
def prefixEnd_2944354 : Nat := 4983230072969 + 3 ^ 40 * 2944354 * 2
def baseEnd_2944354 : Nat := 1007912545992185623422779

theorem tailTrace_2944354 : CollatzResearch.WordTrace tailWord_2944354 prefixEnd_2944354 1007912545992185623422779 := by
  unfold tailWord_2944354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26847353193778947118482029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71592941850077192315952077 26847353193778947118482029)
  ·
    refine ⟨10067757447667105169430761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26847353193778947118482029 10067757447667105169430761)
    ·
      refine ⟨7550818085750328877073071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10067757447667105169430761 7550818085750328877073071)
      ·
        refine ⟨11326227128625493315609607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550818085750328877073071 11326227128625493315609607)
        ·
          refine ⟨16989340692938239973414411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326227128625493315609607 16989340692938239973414411)
          ·
            refine ⟨25484011039407359960121617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16989340692938239973414411 25484011039407359960121617)
            ·
              refine ⟨19113008279555519970091213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25484011039407359960121617 19113008279555519970091213)
              ·
                refine ⟨7167378104833319988784205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19113008279555519970091213 7167378104833319988784205)
                ·
                  refine ⟨2687766789312494995794077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7167378104833319988784205 2687766789312494995794077)
                  ·
                    refine ⟨1007912545992185623422779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687766789312494995794077 1007912545992185623422779)
                    ·
                      rfl

theorem cell22_2944354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2944354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944354 prefixEnd_2944354 := by exact prefixLift 2944354
  have htrace : WordTrace (prefixWord ++ tailWord_2944354) baseStart_2944354 baseEnd_2944354 := by
    simpa [prefixWord, tailWord_2944354, baseEnd_2944354] using wordTrace_append hprefix tailTrace_2944354
  have hstable : (prefixWord ++ tailWord_2944354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944354).length < 2 ^ (prefixWord ++ tailWord_2944354).sum := by decide
  have hdescent : baseEnd_2944354 < baseStart_2944354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944395 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 8]
def baseStart_2944395 : Nat := 118140960795 + 2944395 * 2 ^ 59
def prefixEnd_2944395 : Nat := 4983230072969 + 3 ^ 40 * 2944395 * 2
def baseEnd_2944395 : Nat := 335975527043358394382551

theorem tailTrace_2944395 : CollatzResearch.WordTrace tailWord_2944395 prefixEnd_2944395 335975527043358394382551 := by
  unfold tailWord_2944395
  simp only [CollatzResearch.WordTrace]
  refine ⟨107390908167967252476170639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71593938778644834984113759 107390908167967252476170639)
  ·
    refine ⟨161086362251950878714255959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107390908167967252476170639 161086362251950878714255959)
    ·
      refine ⟨241629543377926318071383939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161086362251950878714255959 241629543377926318071383939)
      ·
        refine ⟨362444315066889477107075909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241629543377926318071383939 362444315066889477107075909)
        ·
          refine ⟨67958309075041776957576733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362444315066889477107075909 67958309075041776957576733)
          ·
            refine ⟨25484365903140666359091275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67958309075041776957576733 25484365903140666359091275)
            ·
              refine ⟨38226548854710999538636913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25484365903140666359091275 38226548854710999538636913)
              ·
                refine ⟨28669911641033249653977685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38226548854710999538636913 28669911641033249653977685)
                ·
                  refine ⟨335975527043358394382551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28669911641033249653977685 335975527043358394382551)
                  ·
                    rfl

theorem cell22_2944395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_2944395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944395 prefixEnd_2944395 := by exact prefixLift 2944395
  have htrace : WordTrace (prefixWord ++ tailWord_2944395) baseStart_2944395 baseEnd_2944395 := by
    simpa [prefixWord, tailWord_2944395, baseEnd_2944395] using wordTrace_append hprefix tailTrace_2944395
  have hstable : (prefixWord ++ tailWord_2944395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944395).length < 2 ^ (prefixWord ++ tailWord_2944395).sum := by decide
  have hdescent : baseEnd_2944395 < baseStart_2944395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944429 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2944429 : Nat := 118140960795 + 2944429 * 2 ^ 59
def prefixEnd_2944429 : Nat := 4983230072969 + 3 ^ 40 * 2944429 * 2
def baseEnd_2944429 : Nat := 335979406674970142599183

theorem tailTrace_2944429 : CollatzResearch.WordTrace tailWord_2944429 prefixEnd_2944429 335979406674970142599183 := by
  unfold tailWord_2944429
  simp only [CollatzResearch.WordTrace]
  refine ⟨107392148249844076282908341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71594765499896050855272227 107392148249844076282908341)
  ·
    refine ⟨10068013898422882151522657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107392148249844076282908341 10068013898422882151522657)
    ·
      refine ⟨7551010423817161613641993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10068013898422882151522657 7551010423817161613641993)
      ·
        refine ⟨5663257817862871210231495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7551010423817161613641993 5663257817862871210231495)
        ·
          refine ⟨8494886726794306815347243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663257817862871210231495 8494886726794306815347243)
          ·
            refine ⟨12742330090191460223020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494886726794306815347243 12742330090191460223020865)
            ·
              refine ⟨9556747567643595167265649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742330090191460223020865 9556747567643595167265649)
              ·
                refine ⟨7167560675732696375449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9556747567643595167265649 7167560675732696375449237)
                ·
                  refine ⟨335979406674970142599183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7167560675732696375449237 335979406674970142599183)
                  ·
                    rfl

theorem cell22_2944429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2944429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944429 prefixEnd_2944429 := by exact prefixLift 2944429
  have htrace : WordTrace (prefixWord ++ tailWord_2944429) baseStart_2944429 baseEnd_2944429 := by
    simpa [prefixWord, tailWord_2944429, baseEnd_2944429] using wordTrace_append hprefix tailTrace_2944429
  have hstable : (prefixWord ++ tailWord_2944429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944429).length < 2 ^ (prefixWord ++ tailWord_2944429).sum := by decide
  have hdescent : baseEnd_2944429 < baseStart_2944429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944506 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_2944506 : Nat := 118140960795 + 2944506 * 2 ^ 59
def prefixEnd_2944506 : Nat := 4983230072969 + 3 ^ 40 * 2944506 * 2
def baseEnd_2944506 : Nat := 1007964578698507893622313

theorem tailTrace_2944506 : CollatzResearch.WordTrace tailWord_2944506 prefixEnd_2944506 1007964578698507893622313 := by
  unfold tailWord_2944506
  simp only [CollatzResearch.WordTrace]
  refine ⟨26848739167641279608365343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71596637780376745622307581 26848739167641279608365343)
  ·
    refine ⟨40273108751461919412548015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26848739167641279608365343 40273108751461919412548015)
    ·
      refine ⟨60409663127192879118822023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40273108751461919412548015 60409663127192879118822023)
      ·
        refine ⟨90614494690789318678233035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60409663127192879118822023 90614494690789318678233035)
        ·
          refine ⟨135921742036183978017349553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90614494690789318678233035 135921742036183978017349553)
          ·
            refine ⟨101941306527137983513012165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135921742036183978017349553 101941306527137983513012165)
            ·
              refine ⟨19113994973838371908689781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101941306527137983513012165 19113994973838371908689781)
              ·
                refine ⟨1791937028797347366439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19113994973838371908689781 1791937028797347366439667)
                ·
                  refine ⟨2687905543196021049659501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791937028797347366439667 2687905543196021049659501)
                  ·
                    refine ⟨1007964578698507893622313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687905543196021049659501 1007964578698507893622313)
                    ·
                      rfl

theorem cell22_2944506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_2944506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944506 prefixEnd_2944506 := by exact prefixLift 2944506
  have htrace : WordTrace (prefixWord ++ tailWord_2944506) baseStart_2944506 baseEnd_2944506 := by
    simpa [prefixWord, tailWord_2944506, baseEnd_2944506] using wordTrace_append hprefix tailTrace_2944506
  have hstable : (prefixWord ++ tailWord_2944506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944506).length < 2 ^ (prefixWord ++ tailWord_2944506).sum := by decide
  have hdescent : baseEnd_2944506 < baseStart_2944506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944517 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2944517 : Nat := 118140960795 + 2944517 * 2 ^ 59
def prefixEnd_2944517 : Nat := 4983230072969 + 3 ^ 40 * 2944517 * 2
def baseEnd_2944517 : Nat := 1007968344223307531597279

theorem tailTrace_2944517 : CollatzResearch.WordTrace tailWord_2944517 prefixEnd_2944517 1007968344223307531597279 := by
  unfold tailWord_2944517
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395357873525267312111805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71596905249016844874741203 107395357873525267312111805)
  ·
    refine ⟨40273259202571975242041927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107395357873525267312111805 40273259202571975242041927)
    ·
      refine ⟨60409888803857962863062891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40273259202571975242041927 60409888803857962863062891)
      ·
        refine ⟨90614833205786944294594337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60409888803857962863062891 90614833205786944294594337)
        ·
          refine ⟨67961124904340208220945753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90614833205786944294594337 67961124904340208220945753)
          ·
            refine ⟨50970843678255156165709315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67961124904340208220945753 50970843678255156165709315)
            ·
              refine ⟨76456265517382734248563973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50970843678255156165709315 76456265517382734248563973)
              ·
                refine ⟨14335549784509262671605745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76456265517382734248563973 14335549784509262671605745)
                ·
                  refine ⟨10751662338381947003704309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14335549784509262671605745 10751662338381947003704309)
                  ·
                    refine ⟨1007968344223307531597279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10751662338381947003704309 1007968344223307531597279)
                    ·
                      rfl

theorem cell22_2944517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2944517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944517 prefixEnd_2944517 := by exact prefixLift 2944517
  have htrace : WordTrace (prefixWord ++ tailWord_2944517) baseStart_2944517 baseEnd_2944517 := by
    simpa [prefixWord, tailWord_2944517, baseEnd_2944517] using wordTrace_append hprefix tailTrace_2944517
  have hstable : (prefixWord ++ tailWord_2944517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944517).length < 2 ^ (prefixWord ++ tailWord_2944517).sum := by decide
  have hdescent : baseEnd_2944517 < baseStart_2944517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944519 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 5]
def baseStart_2944519 : Nat := 118140960795 + 2944519 * 2 ^ 59
def prefixEnd_2944519 : Nat := 4983230072969 + 3 ^ 40 * 2944519 * 2
def baseEnd_2944519 : Nat := 335989676288060064349091

theorem tailTrace_2944519 : CollatzResearch.WordTrace tailWord_2944519 prefixEnd_2944519 335989676288060064349091 := by
  unfold tailWord_2944519
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395430819518021653684611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71596953879678681102456407 107395430819518021653684611)
  ·
    refine ⟨161093146229277032480526917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107395430819518021653684611 161093146229277032480526917)
    ·
      refine ⟨30204964917989443590098797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161093146229277032480526917 30204964917989443590098797)
      ·
        refine ⟨11326861844246041346287049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30204964917989443590098797 11326861844246041346287049)
        ·
          refine ⟨8495146383184531009715287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11326861844246041346287049 8495146383184531009715287)
          ·
            refine ⟨12742719574776796514572931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495146383184531009715287 12742719574776796514572931)
            ·
              refine ⟨19114079362165194771859397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12742719574776796514572931 19114079362165194771859397)
              ·
                refine ⟨3583889880405974019723637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19114079362165194771859397 3583889880405974019723637)
                ·
                  refine ⟨335989676288060064349091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3583889880405974019723637 335989676288060064349091)
                  ·
                    rfl

theorem cell22_2944519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].length) (baseStart_2944519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944519 prefixEnd_2944519 := by exact prefixLift 2944519
  have htrace : WordTrace (prefixWord ++ tailWord_2944519) baseStart_2944519 baseEnd_2944519 := by
    simpa [prefixWord, tailWord_2944519, baseEnd_2944519] using wordTrace_append hprefix tailTrace_2944519
  have hstable : (prefixWord ++ tailWord_2944519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944519).length < 2 ^ (prefixWord ++ tailWord_2944519).sum := by decide
  have hdescent : baseEnd_2944519 < baseStart_2944519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944523 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 1, 3]
def baseStart_2944523 : Nat := 118140960795 + 2944523 * 2 ^ 59
def prefixEnd_2944523 : Nat := 4983230072969 + 3 ^ 40 * 2944523 * 2
def baseEnd_2944523 : Nat := 1007970398145925515947261

theorem tailTrace_2944523 : CollatzResearch.WordTrace tailWord_2944523 prefixEnd_2944523 1007970398145925515947261 := by
  unfold tailWord_2944523
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395576711503530336830223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71597051141002353557886815 107395576711503530336830223)
  ·
    refine ⟨161093365067255295505245335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107395576711503530336830223 161093365067255295505245335)
    ·
      refine ⟨241640047600882943257868003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161093365067255295505245335 241640047600882943257868003)
      ·
        refine ⟨362460071401324414886802005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241640047600882943257868003 362460071401324414886802005)
        ·
          refine ⟨4247578961734270486954711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 362460071401324414886802005 4247578961734270486954711)
          ·
            refine ⟨6371368442601405730432067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247578961734270486954711 6371368442601405730432067)
            ·
              refine ⟨9557052663902108595648101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371368442601405730432067 9557052663902108595648101)
              ·
                refine ⟨1791947374481645361684019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9557052663902108595648101 1791947374481645361684019)
                ·
                  refine ⟨2687921061722468042526029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791947374481645361684019 2687921061722468042526029)
                  ·
                    refine ⟨1007970398145925515947261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687921061722468042526029 1007970398145925515947261)
                    ·
                      rfl

theorem cell22_2944523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 3].length) (baseStart_2944523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944523 prefixEnd_2944523 := by exact prefixLift 2944523
  have htrace : WordTrace (prefixWord ++ tailWord_2944523) baseStart_2944523 baseEnd_2944523 := by
    simpa [prefixWord, tailWord_2944523, baseEnd_2944523] using wordTrace_append hprefix tailTrace_2944523
  have hstable : (prefixWord ++ tailWord_2944523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944523).length < 2 ^ (prefixWord ++ tailWord_2944523).sum := by decide
  have hdescent : baseEnd_2944523 < baseStart_2944523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944525 : List Nat := [1, 7, 1, 1, 3, 1, 1, 7]
def baseStart_2944525 : Nat := 118140960795 + 2944525 * 2 ^ 59
def prefixEnd_2944525 : Nat := 4983230072969 + 3 ^ 40 * 2944525 * 2
def baseEnd_2944525 : Nat := 111996786976310908599695

theorem tailTrace_2944525 : CollatzResearch.WordTrace tailWord_2944525 prefixEnd_2944525 111996786976310908599695 := by
  unfold tailWord_2944525
  simp only [CollatzResearch.WordTrace]
  refine ⟨107395649657496284678403029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71597099771664189785602019 107395649657496284678403029)
  ·
    refine ⟨2517085538847569172150071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107395649657496284678403029 2517085538847569172150071)
    ·
      refine ⟨3775628308271353758225107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517085538847569172150071 3775628308271353758225107)
      ·
        refine ⟨5663442462407030637337661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775628308271353758225107 5663442462407030637337661)
        ·
          refine ⟨2123790923402636489001623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5663442462407030637337661 2123790923402636489001623)
          ·
            refine ⟨3185686385103954733502435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123790923402636489001623 3185686385103954733502435)
            ·
              refine ⟨4778529577655932100253653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185686385103954733502435 4778529577655932100253653)
              ·
                refine ⟨111996786976310908599695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4778529577655932100253653 111996786976310908599695)
                ·
                  rfl

theorem cell22_2944525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 7].length) (baseStart_2944525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944525 prefixEnd_2944525 := by exact prefixLift 2944525
  have htrace : WordTrace (prefixWord ++ tailWord_2944525) baseStart_2944525 baseEnd_2944525 := by
    simpa [prefixWord, tailWord_2944525, baseEnd_2944525] using wordTrace_append hprefix tailTrace_2944525
  have hstable : (prefixWord ++ tailWord_2944525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944525).length < 2 ^ (prefixWord ++ tailWord_2944525).sum := by decide
  have hdescent : baseEnd_2944525 < baseStart_2944525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944549 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2944549 : Nat := 118140960795 + 2944549 * 2 ^ 59
def prefixEnd_2944549 : Nat := 4983230072969 + 3 ^ 40 * 2944549 * 2
def baseEnd_2944549 : Nat := 1007979298477270114797181

theorem tailTrace_2944549 : CollatzResearch.WordTrace tailWord_2944549 prefixEnd_2944549 1007979298477270114797181 := by
  unfold tailWord_2944549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107396525009409336777276701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71597683339606224518184467 107396525009409336777276701)
  ·
    refine ⟨40273696878528501291478763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107396525009409336777276701 40273696878528501291478763)
    ·
      refine ⟨60410545317792751937218145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40273696878528501291478763 60410545317792751937218145)
      ·
        refine ⟨45307908988344563952913609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60410545317792751937218145 45307908988344563952913609)
        ·
          refine ⟨33980931741258422964685207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45307908988344563952913609 33980931741258422964685207)
          ·
            refine ⟨50971397611887634447027811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33980931741258422964685207 50971397611887634447027811)
            ·
              refine ⟨76457096417831451670541717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50971397611887634447027811 76457096417831451670541717)
              ·
                refine ⟨3583926394585849297056643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76457096417831451670541717 3583926394585849297056643)
                ·
                  refine ⟨5375889591878773945584965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583926394585849297056643 5375889591878773945584965)
                  ·
                    refine ⟨1007979298477270114797181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5375889591878773945584965 1007979298477270114797181)
                    ·
                      rfl

theorem cell22_2944549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2944549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944549 prefixEnd_2944549 := by exact prefixLift 2944549
  have htrace : WordTrace (prefixWord ++ tailWord_2944549) baseStart_2944549 baseEnd_2944549 := by
    simpa [prefixWord, tailWord_2944549, baseEnd_2944549] using wordTrace_append hprefix tailTrace_2944549
  have hstable : (prefixWord ++ tailWord_2944549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944549).length < 2 ^ (prefixWord ++ tailWord_2944549).sum := by decide
  have hdescent : baseEnd_2944549 < baseStart_2944549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944592 : List Nat := [2, 1, 1, 1, 1, 3, 4, 9]
def baseStart_2944592 : Nat := 118140960795 + 2944592 * 2 ^ 59
def prefixEnd_2944592 : Nat := 4983230072969 + 3 ^ 40 * 2944592 * 2
def baseEnd_2944592 : Nat := 111999335361781370663561

theorem tailTrace_2944592 : CollatzResearch.WordTrace tailWord_2944592 prefixEnd_2944592 111999335361781370663561 := by
  unfold tailWord_2944592
  simp only [CollatzResearch.WordTrace]
  refine ⟨53699046674126777560546015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71598728898835703414061353 53699046674126777560546015)
  ·
    refine ⟨80548570011190166340819023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53699046674126777560546015 80548570011190166340819023)
    ·
      refine ⟨120822855016785249511228535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80548570011190166340819023 120822855016785249511228535)
      ·
        refine ⟨181234282525177874266842803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120822855016785249511228535 181234282525177874266842803)
        ·
          refine ⟨271851423787766811400264205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181234282525177874266842803 271851423787766811400264205)
          ·
            refine ⟨101944283920412554275099077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271851423787766811400264205 101944283920412554275099077)
            ·
              refine ⟨19114553235077353926581077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101944283920412554275099077 19114553235077353926581077)
              ·
                refine ⟨111999335361781370663561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19114553235077353926581077 111999335361781370663561)
                ·
                  rfl

theorem cell22_2944592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_2944592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944592 prefixEnd_2944592 := by exact prefixLift 2944592
  have htrace : WordTrace (prefixWord ++ tailWord_2944592) baseStart_2944592 baseEnd_2944592 := by
    simpa [prefixWord, tailWord_2944592, baseEnd_2944592] using wordTrace_append hprefix tailTrace_2944592
  have hstable : (prefixWord ++ tailWord_2944592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944592).length < 2 ^ (prefixWord ++ tailWord_2944592).sum := by decide
  have hdescent : baseEnd_2944592 < baseStart_2944592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944594 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2944594 : Nat := 118140960795 + 2944594 * 2 ^ 59
def prefixEnd_2944594 : Nat := 4983230072969 + 3 ^ 40 * 2944594 * 2
def baseEnd_2944594 : Nat := 1007994702896904997422043

theorem tailTrace_2944594 : CollatzResearch.WordTrace tailWord_2944594 prefixEnd_2944594 1007994702896904997422043 := by
  unfold tailWord_2944594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26849541573561577365666209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71598777529497539641776557 26849541573561577365666209)
  ·
    refine ⟨20137156180171183024249657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26849541573561577365666209 20137156180171183024249657)
    ·
      refine ⟨15102867135128387268187243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20137156180171183024249657 15102867135128387268187243)
      ·
        refine ⟨22654300702692580902280865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15102867135128387268187243 22654300702692580902280865)
        ·
          refine ⟨16990725527019435676710649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22654300702692580902280865 16990725527019435676710649)
          ·
            refine ⟨12743044145264576757532987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16990725527019435676710649 12743044145264576757532987)
            ·
              refine ⟨19114566217896865136299481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743044145264576757532987 19114566217896865136299481)
              ·
                refine ⟨14335924663422648852224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19114566217896865136299481 14335924663422648852224611)
                ·
                  refine ⟨21503886995133973278336917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14335924663422648852224611 21503886995133973278336917)
                  ·
                    refine ⟨1007994702896904997422043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21503886995133973278336917 1007994702896904997422043)
                    ·
                      rfl

theorem cell22_2944594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2944594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944594 prefixEnd_2944594 := by exact prefixLift 2944594
  have htrace : WordTrace (prefixWord ++ tailWord_2944594) baseStart_2944594 baseEnd_2944594 := by
    simpa [prefixWord, tailWord_2944594, baseEnd_2944594] using wordTrace_append hprefix tailTrace_2944594
  have hstable : (prefixWord ++ tailWord_2944594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944594).length < 2 ^ (prefixWord ++ tailWord_2944594).sum := by decide
  have hdescent : baseEnd_2944594 < baseStart_2944594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944669 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2944669 : Nat := 118140960795 + 2944669 * 2 ^ 59
def prefixEnd_2944669 : Nat := 4983230072969 + 3 ^ 40 * 2944669 * 2
def baseEnd_2944669 : Nat := 1008020376929629801796813

theorem tailTrace_2944669 : CollatzResearch.WordTrace tailWord_2944669 prefixEnd_2944669 1008020376929629801796813 := by
  unfold tailWord_2944669
  simp only [CollatzResearch.WordTrace]
  refine ⟨107400901768974597271645061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71600601179316398181096707 107400901768974597271645061)
  ·
    refine ⟨20137669081682736988433449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107400901768974597271645061 20137669081682736988433449)
    ·
      refine ⟨15103251811262052741325087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20137669081682736988433449 15103251811262052741325087)
      ·
        refine ⟨22654877716893079111987631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15103251811262052741325087 22654877716893079111987631)
        ·
          refine ⟨33982316575339618667981447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22654877716893079111987631 33982316575339618667981447)
          ·
            refine ⟨50973474863009428001972171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33982316575339618667981447 50973474863009428001972171)
            ·
              refine ⟨76460212294514142002958257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50973474863009428001972171 76460212294514142002958257)
              ·
                refine ⟨57345159220885606502218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76460212294514142002958257 57345159220885606502218693)
                ·
                  refine ⟨10752217353916051219166005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57345159220885606502218693 10752217353916051219166005)
                  ·
                    refine ⟨1008020376929629801796813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10752217353916051219166005 1008020376929629801796813)
                    ·
                      rfl

theorem cell22_2944669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2944669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944669 prefixEnd_2944669 := by exact prefixLift 2944669
  have htrace : WordTrace (prefixWord ++ tailWord_2944669) baseStart_2944669 baseEnd_2944669 := by
    simpa [prefixWord, tailWord_2944669, baseEnd_2944669] using wordTrace_append hprefix tailTrace_2944669
  have hstable : (prefixWord ++ tailWord_2944669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944669).length < 2 ^ (prefixWord ++ tailWord_2944669).sum := by decide
  have hdescent : baseEnd_2944669 < baseStart_2944669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944746 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2944746 : Nat := 118140960795 + 2944746 * 2 ^ 59
def prefixEnd_2944746 : Nat := 4983230072969 + 3 ^ 40 * 2944746 * 2
def baseEnd_2944746 : Nat := 1008046735603227267621577

theorem tailTrace_2944746 : CollatzResearch.WordTrace tailWord_2944746 prefixEnd_2944746 1008046735603227267621577 := by
  unfold tailWord_2944746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26850927547423909855549523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71602473459797092948132061 26850927547423909855549523)
  ·
    refine ⟨40276391321135864783324285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26850927547423909855549523 40276391321135864783324285)
    ·
      refine ⟨15103646745425949293746607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40276391321135864783324285 15103646745425949293746607)
      ·
        refine ⟨22655470118138923940619911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15103646745425949293746607 22655470118138923940619911)
        ·
          refine ⟨33983205177208385910929867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22655470118138923940619911 33983205177208385910929867)
          ·
            refine ⟨50974807765812578866394801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33983205177208385910929867 50974807765812578866394801)
            ·
              refine ⟨38231105824359434149796101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50974807765812578866394801 38231105824359434149796101)
              ·
                refine ⟨7168332342067393903086769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38231105824359434149796101 7168332342067393903086769)
                ·
                  refine ⟨5376249256550545427315077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168332342067393903086769 5376249256550545427315077)
                  ·
                    refine ⟨1008046735603227267621577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376249256550545427315077 1008046735603227267621577)
                    ·
                      rfl

theorem cell22_2944746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2944746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944746 prefixEnd_2944746 := by exact prefixLift 2944746
  have htrace : WordTrace (prefixWord ++ tailWord_2944746) baseStart_2944746 baseEnd_2944746 := by
    simpa [prefixWord, tailWord_2944746, baseEnd_2944746] using wordTrace_append hprefix tailTrace_2944746
  have hstable : (prefixWord ++ tailWord_2944746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944746).length < 2 ^ (prefixWord ++ tailWord_2944746).sum := by decide
  have hdescent : baseEnd_2944746 < baseStart_2944746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944748 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_2944748 : Nat := 118140960795 + 2944748 * 2 ^ 59
def prefixEnd_2944748 : Nat := 4983230072969 + 3 ^ 40 * 2944748 * 2
def baseEnd_2944748 : Nat := 1008047420244099929071571

theorem tailTrace_2944748 : CollatzResearch.WordTrace tailWord_2944748 prefixEnd_2944748 1008047420244099929071571 := by
  unfold tailWord_2944748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53701891567844196881885449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71602522090458929175847265 53701891567844196881885449)
  ·
    refine ⟨40276418675883147661414087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53701891567844196881885449 40276418675883147661414087)
    ·
      refine ⟨60414628013824721492121131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40276418675883147661414087 60414628013824721492121131)
      ·
        refine ⟨90621942020737082238181697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60414628013824721492121131 90621942020737082238181697)
        ·
          refine ⟨67966456515552811678636273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90621942020737082238181697 67966456515552811678636273)
          ·
            refine ⟨50974842386664608758977205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67966456515552811678636273 50974842386664608758977205)
            ·
              refine ⟨4778891473749807071154113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50974842386664608758977205 4778891473749807071154113)
              ·
                refine ⟨3584168605312355303365585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778891473749807071154113 3584168605312355303365585)
                ·
                  refine ⟨2688126453984266477524189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584168605312355303365585 2688126453984266477524189)
                  ·
                    refine ⟨1008047420244099929071571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688126453984266477524189 1008047420244099929071571)
                    ·
                      rfl

theorem cell22_2944748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_2944748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944748 prefixEnd_2944748 := by exact prefixLift 2944748
  have htrace : WordTrace (prefixWord ++ tailWord_2944748) baseStart_2944748 baseEnd_2944748 := by
    simpa [prefixWord, tailWord_2944748, baseEnd_2944748] using wordTrace_append hprefix tailTrace_2944748
  have hstable : (prefixWord ++ tailWord_2944748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944748).length < 2 ^ (prefixWord ++ tailWord_2944748).sum := by decide
  have hdescent : baseEnd_2944748 < baseStart_2944748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944778 : List Nat := [3, 1, 2, 2, 1, 5, 2, 6]
def baseStart_2944778 : Nat := 118140960795 + 2944778 * 2 ^ 59
def prefixEnd_2944778 : Nat := 4983230072969 + 3 ^ 40 * 2944778 * 2
def baseEnd_2944778 : Nat := 112006409984132205646831

theorem tailTrace_2944778 : CollatzResearch.WordTrace tailWord_2944778 prefixEnd_2944778 112006409984132205646831 := by
  unfold tailWord_2944778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851219331394927221840747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71603251550386472591575325 26851219331394927221840747)
  ·
    refine ⟨40276828997092390832761121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851219331394927221840747 40276828997092390832761121)
    ·
      refine ⟨30207621747819293124570841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40276828997092390832761121 30207621747819293124570841)
      ·
        refine ⟨22655716310864469843428131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30207621747819293124570841 22655716310864469843428131)
        ·
          refine ⟨33983574466296704765142197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22655716310864469843428131 33983574466296704765142197)
          ·
            refine ⟨3185960106215316071732081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33983574466296704765142197 3185960106215316071732081)
            ·
              refine ⟨2389470079661487053799061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185960106215316071732081 2389470079661487053799061)
              ·
                refine ⟨112006409984132205646831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2389470079661487053799061 112006409984132205646831)
                ·
                  rfl

theorem cell22_2944778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_2944778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944778 prefixEnd_2944778 := by exact prefixLift 2944778
  have htrace : WordTrace (prefixWord ++ tailWord_2944778) baseStart_2944778 baseEnd_2944778 := by
    simpa [prefixWord, tailWord_2944778, baseEnd_2944778] using wordTrace_append hprefix tailTrace_2944778
  have hstable : (prefixWord ++ tailWord_2944778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944778).length < 2 ^ (prefixWord ++ tailWord_2944778).sum := by decide
  have hdescent : baseEnd_2944778 < baseStart_2944778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944881 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2944881 : Nat := 118140960795 + 2944881 * 2 ^ 59
def prefixEnd_2944881 : Nat := 4983230072969 + 3 ^ 40 * 2944881 * 2
def baseEnd_2944881 : Nat := 1008092948862131915496163

theorem tailTrace_2944881 : CollatzResearch.WordTrace tailWord_2944881 prefixEnd_2944881 1008092948862131915496163 := by
  unfold tailWord_2944881
  simp only [CollatzResearch.WordTrace]
  refine ⟨107408634044206557478362497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71605756029471038318908331 107408634044206557478362497)
  ·
    refine ⟨80556475533154918108771873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107408634044206557478362497 80556475533154918108771873)
    ·
      refine ⟨60417356649866188581578905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80556475533154918108771873 60417356649866188581578905)
      ·
        refine ⟨45313017487399641436184179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60417356649866188581578905 45313017487399641436184179)
        ·
          refine ⟨67969526231099462154276269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45313017487399641436184179 67969526231099462154276269)
          ·
            refine ⟨25488572336662298307853601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67969526231099462154276269 25488572336662298307853601)
            ·
              refine ⟨19116429252496723730890201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25488572336662298307853601 19116429252496723730890201)
              ·
                refine ⟨14337321939372542798167651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116429252496723730890201 14337321939372542798167651)
                ·
                  refine ⟨21505982909058814197251477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14337321939372542798167651 21505982909058814197251477)
                  ·
                    refine ⟨1008092948862131915496163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21505982909058814197251477 1008092948862131915496163)
                    ·
                      rfl

theorem cell22_2944881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2944881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944881 prefixEnd_2944881 := by exact prefixLift 2944881
  have htrace : WordTrace (prefixWord ++ tailWord_2944881) baseStart_2944881 baseEnd_2944881 := by
    simpa [prefixWord, tailWord_2944881, baseEnd_2944881] using wordTrace_append hprefix tailTrace_2944881
  have hstable : (prefixWord ++ tailWord_2944881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944881).length < 2 ^ (prefixWord ++ tailWord_2944881).sum := by decide
  have hdescent : baseEnd_2944881 < baseStart_2944881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944904 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_2944904 : Nat := 118140960795 + 2944904 * 2 ^ 59
def prefixEnd_2944904 : Nat := 4983230072969 + 3 ^ 40 * 2944904 * 2
def baseEnd_2944904 : Nat := 1008100822232167522171093

theorem tailTrace_2944904 : CollatzResearch.WordTrace tailWord_2944904 prefixEnd_2944904 1008100822232167522171093 := by
  unfold tailWord_2944904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53704736461561616203224883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71606315282082154937633177 53704736461561616203224883)
  ·
    refine ⟨80557104692342424304837325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53704736461561616203224883 80557104692342424304837325)
    ·
      refine ⟨30208914259628409114313997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80557104692342424304837325 30208914259628409114313997)
      ·
        refine ⟨11328342847360653417867749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30208914259628409114313997 11328342847360653417867749)
        ·
          refine ⟨2124064283880122515850203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11328342847360653417867749 2124064283880122515850203)
          ·
            refine ⟨3186096425820183773775305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124064283880122515850203 3186096425820183773775305)
            ·
              refine ⟨2389572319365137830331479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186096425820183773775305 2389572319365137830331479)
              ·
                refine ⟨3584358479047706745497219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389572319365137830331479 3584358479047706745497219)
                ·
                  refine ⟨5376537718571560118245829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584358479047706745497219 5376537718571560118245829)
                  ·
                    refine ⟨1008100822232167522171093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376537718571560118245829 1008100822232167522171093)
                    ·
                      rfl

theorem cell22_2944904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_2944904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944904 prefixEnd_2944904 := by exact prefixLift 2944904
  have htrace : WordTrace (prefixWord ++ tailWord_2944904) baseStart_2944904 baseEnd_2944904 := by
    simpa [prefixWord, tailWord_2944904, baseEnd_2944904] using wordTrace_append hprefix tailTrace_2944904
  have hstable : (prefixWord ++ tailWord_2944904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944904).length < 2 ^ (prefixWord ++ tailWord_2944904).sum := by decide
  have hdescent : baseEnd_2944904 < baseStart_2944904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944945 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_2944945 : Nat := 118140960795 + 2944945 * 2 ^ 59
def prefixEnd_2944945 : Nat := 4983230072969 + 3 ^ 40 * 2944945 * 2
def baseEnd_2944945 : Nat := 1008114857370057081895967

theorem tailTrace_2944945 : CollatzResearch.WordTrace tailWord_2944945 prefixEnd_2944945 1008114857370057081895967 := by
  unfold tailWord_2944945
  simp only [CollatzResearch.WordTrace]
  refine ⟨107410968315974696408692289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71607312210649797605794859 107410968315974696408692289)
  ·
    refine ⟨80558226236981022306519217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107410968315974696408692289 80558226236981022306519217)
    ·
      refine ⟨60418669677735766729889413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80558226236981022306519217 60418669677735766729889413)
      ·
        refine ⟨11328500564575456261854265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60418669677735766729889413 11328500564575456261854265)
        ·
          refine ⟨8496375423431592196390699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11328500564575456261854265 8496375423431592196390699)
          ·
            refine ⟨12744563135147388294586049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496375423431592196390699 12744563135147388294586049)
            ·
              refine ⟨9558422351360541220939537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12744563135147388294586049 9558422351360541220939537)
              ·
                refine ⟨7168816763520405915704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9558422351360541220939537 7168816763520405915704653)
                ·
                  refine ⟨2688306286320152218389245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7168816763520405915704653 2688306286320152218389245)
                  ·
                    refine ⟨1008114857370057081895967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688306286320152218389245 1008114857370057081895967)
                    ·
                      rfl

theorem cell22_2944945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_2944945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944945 prefixEnd_2944945 := by exact prefixLift 2944945
  have htrace : WordTrace (prefixWord ++ tailWord_2944945) baseStart_2944945 baseEnd_2944945 := by
    simpa [prefixWord, tailWord_2944945, baseEnd_2944945] using wordTrace_append hprefix tailTrace_2944945
  have hstable : (prefixWord ++ tailWord_2944945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944945).length < 2 ^ (prefixWord ++ tailWord_2944945).sum := by decide
  have hdescent : baseEnd_2944945 < baseStart_2944945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944958 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2944958 : Nat := 118140960795 + 2944958 * 2 ^ 59
def prefixEnd_2944958 : Nat := 4983230072969 + 3 ^ 40 * 2944958 * 2
def baseEnd_2944958 : Nat := 336039769178576460440309

theorem tailTrace_2944958 : CollatzResearch.WordTrace tailWord_2944958 prefixEnd_2944958 336039769178576460440309 := by
  unfold tailWord_2944958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426430308115949953614441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71607628309951733085943685 13426430308115949953614441)
  ·
    refine ⟨10069822731086962465210831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13426430308115949953614441 10069822731086962465210831)
    ·
      refine ⟨15104734096630443697816247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10069822731086962465210831 15104734096630443697816247)
      ·
        refine ⟨22657101144945665546724371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15104734096630443697816247 22657101144945665546724371)
        ·
          refine ⟨33985651717418498320086557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22657101144945665546724371 33985651717418498320086557)
          ·
            refine ⟨12744619394031936870032459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33985651717418498320086557 12744619394031936870032459)
            ·
              refine ⟨19116929091047905305048689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744619394031936870032459 19116929091047905305048689)
              ·
                refine ⟨14337696818285928978786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116929091047905305048689 14337696818285928978786517)
                ·
                  refine ⟨336039769178576460440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14337696818285928978786517 336039769178576460440309)
                  ·
                    rfl

theorem cell22_2944958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2944958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944958 prefixEnd_2944958 := by exact prefixLift 2944958
  have htrace : WordTrace (prefixWord ++ tailWord_2944958) baseStart_2944958 baseEnd_2944958 := by
    simpa [prefixWord, tailWord_2944958, baseEnd_2944958] using wordTrace_append hprefix tailTrace_2944958
  have hstable : (prefixWord ++ tailWord_2944958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944958).length < 2 ^ (prefixWord ++ tailWord_2944958).sum := by decide
  have hdescent : baseEnd_2944958 < baseStart_2944958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945020 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_2945020 : Nat := 118140960795 + 2945020 * 2 ^ 59
def prefixEnd_2945020 : Nat := 4983230072969 + 3 ^ 40 * 2945020 * 2
def baseEnd_2945020 : Nat := 336046843800927295423579

theorem tailTrace_2945020 : CollatzResearch.WordTrace tailWord_2945020 prefixEnd_2945020 336046843800927295423579 := by
  unfold tailWord_2945020
  simp only [CollatzResearch.WordTrace]
  refine ⟨53706851895351492108836257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71609135860468656145115009 53706851895351492108836257)
  ·
    refine ⟨40280138921513619081627193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53706851895351492108836257 40280138921513619081627193)
    ·
      refine ⟨30210104191135214311220395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40280138921513619081627193 30210104191135214311220395)
      ·
        refine ⟨45315156286702821466830593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30210104191135214311220395 45315156286702821466830593)
        ·
          refine ⟨33986367215027116100122945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45315156286702821466830593 33986367215027116100122945)
          ·
            refine ⟨25489775411270337075092209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33986367215027116100122945 25489775411270337075092209)
            ·
              refine ⟨19117331558452752806319157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25489775411270337075092209 19117331558452752806319157)
              ·
                refine ⟨1792249833604945575592421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19117331558452752806319157 1792249833604945575592421)
                ·
                  refine ⟨336046843800927295423579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792249833604945575592421 336046843800927295423579)
                  ·
                    rfl

theorem cell22_2945020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_2945020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945020 prefixEnd_2945020 := by exact prefixLift 2945020
  have htrace : WordTrace (prefixWord ++ tailWord_2945020) baseStart_2945020 baseEnd_2945020 := by
    simpa [prefixWord, tailWord_2945020, baseEnd_2945020] using wordTrace_append hprefix tailTrace_2945020
  have hstable : (prefixWord ++ tailWord_2945020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945020).length < 2 ^ (prefixWord ++ tailWord_2945020).sum := by decide
  have hdescent : baseEnd_2945020 < baseStart_2945020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945030 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2945030 : Nat := 118140960795 + 2945030 * 2 ^ 59
def prefixEnd_2945030 : Nat := 4983230072969 + 3 ^ 40 * 2945030 * 2
def baseEnd_2945030 : Nat := 1008143954607145193520707

theorem tailTrace_2945030 : CollatzResearch.WordTrace tailWord_2945030 prefixEnd_2945030 1008143954607145193520707 := by
  unfold tailWord_2945030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356689641270836122673017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71609379013777837283691029 3356689641270836122673017)
  ·
    refine ⟨2517517230953127092004763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3356689641270836122673017 2517517230953127092004763)
    ·
      refine ⟨3776275846429690638007145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517517230953127092004763 3776275846429690638007145)
      ·
        refine ⟨2832206884822267978505359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3776275846429690638007145 2832206884822267978505359)
        ·
          refine ⟨4248310327233401967758039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832206884822267978505359 4248310327233401967758039)
          ·
            refine ⟨6372465490850102951637059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248310327233401967758039 6372465490850102951637059)
            ·
              refine ⟨9558698236275154427455589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6372465490850102951637059 9558698236275154427455589)
              ·
                refine ⟨1792255919301591455147923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9558698236275154427455589 1792255919301591455147923)
                ·
                  refine ⟨2688383878952387182721885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792255919301591455147923 2688383878952387182721885)
                  ·
                    refine ⟨1008143954607145193520707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688383878952387182721885 1008143954607145193520707)
                    ·
                      rfl

theorem cell22_2945030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2945030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945030 prefixEnd_2945030 := by exact prefixLift 2945030
  have htrace : WordTrace (prefixWord ++ tailWord_2945030) baseStart_2945030 baseEnd_2945030 := by
    simpa [prefixWord, tailWord_2945030, baseEnd_2945030] using wordTrace_append hprefix tailTrace_2945030
  have hstable : (prefixWord ++ tailWord_2945030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945030).length < 2 ^ (prefixWord ++ tailWord_2945030).sum := by decide
  have hdescent : baseEnd_2945030 < baseStart_2945030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945052 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2945052 : Nat := 118140960795 + 2945052 * 2 ^ 59
def prefixEnd_2945052 : Nat := 4983230072969 + 3 ^ 40 * 2945052 * 2
def baseEnd_2945052 : Nat := 1008151485656744469470639

theorem tailTrace_2945052 : CollatzResearch.WordTrace tailWord_2945052 prefixEnd_2945052 1008151485656744469470639 := by
  unfold tailWord_2945052
  simp only [CollatzResearch.WordTrace]
  refine ⟨53707435463293526841418705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71609913951058035788558273 53707435463293526841418705)
  ·
    refine ⟨40280576597470145131064029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53707435463293526841418705 40280576597470145131064029)
    ·
      refine ⟨15105216224051304424149011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40280576597470145131064029 15105216224051304424149011)
      ·
        refine ⟨22657824336076956636223517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15105216224051304424149011 22657824336076956636223517)
        ·
          refine ⟨8496684126028858738583819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22657824336076956636223517 8496684126028858738583819)
          ·
            refine ⟨12745026189043288107875729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8496684126028858738583819 12745026189043288107875729)
            ·
              refine ⟨9558769641782466080906797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12745026189043288107875729 9558769641782466080906797)
              ·
                refine ⟨3584538615668424780340049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9558769641782466080906797 3584538615668424780340049)
                ·
                  refine ⟨2688403961751318585255037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584538615668424780340049 2688403961751318585255037)
                  ·
                    refine ⟨1008151485656744469470639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688403961751318585255037 1008151485656744469470639)
                    ·
                      rfl

theorem cell22_2945052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2945052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945052 prefixEnd_2945052 := by exact prefixLift 2945052
  have htrace : WordTrace (prefixWord ++ tailWord_2945052) baseStart_2945052 baseEnd_2945052 := by
    simpa [prefixWord, tailWord_2945052, baseEnd_2945052] using wordTrace_append hprefix tailTrace_2945052
  have hstable : (prefixWord ++ tailWord_2945052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945052).length < 2 ^ (prefixWord ++ tailWord_2945052).sum := by decide
  have hdescent : baseEnd_2945052 < baseStart_2945052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945086 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2945086 : Nat := 118140960795 + 2945086 * 2 ^ 59
def prefixEnd_2945086 : Nat := 4983230072969 + 3 ^ 40 * 2945086 * 2
def baseEnd_2945086 : Nat := 1008163124551579714120535

theorem tailTrace_2945086 : CollatzResearch.WordTrace tailWord_2945086 prefixEnd_2945086 1008163124551579714120535 := by
  unfold tailWord_2945086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13427013876057984686196889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71610740672309251659716741 13427013876057984686196889)
  ·
    refine ⟨10070260407043488514647667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13427013876057984686196889 10070260407043488514647667)
    ·
      refine ⟨15105390610565232771971501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10070260407043488514647667 15105390610565232771971501)
      ·
        refine ⟨5664521478961962289489313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15105390610565232771971501 5664521478961962289489313)
        ·
          refine ⟨4248391109221471717116985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5664521478961962289489313 4248391109221471717116985)
          ·
            refine ⟨3186293331916103787837739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248391109221471717116985 3186293331916103787837739)
            ·
              refine ⟨4779439997874155681756609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186293331916103787837739 4779439997874155681756609)
              ·
                refine ⟨3584579998405616761317457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4779439997874155681756609 3584579998405616761317457)
                ·
                  refine ⟨2688434998804212570988093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584579998405616761317457 2688434998804212570988093)
                  ·
                    refine ⟨1008163124551579714120535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688434998804212570988093 1008163124551579714120535)
                    ·
                      rfl

theorem cell22_2945086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2945086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945086 prefixEnd_2945086 := by exact prefixLift 2945086
  have htrace : WordTrace (prefixWord ++ tailWord_2945086) baseStart_2945086 baseEnd_2945086 := by
    simpa [prefixWord, tailWord_2945086, baseEnd_2945086] using wordTrace_append hprefix tailTrace_2945086
  have hstable : (prefixWord ++ tailWord_2945086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945086).length < 2 ^ (prefixWord ++ tailWord_2945086).sum := by decide
  have hdescent : baseEnd_2945086 < baseStart_2945086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945097 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 1, 3]
def baseStart_2945097 : Nat := 118140960795 + 2945097 * 2 ^ 59
def prefixEnd_2945097 : Nat := 4983230072969 + 3 ^ 40 * 2945097 * 2
def baseEnd_2945097 : Nat := 1008166890076379352095501

theorem tailTrace_2945097 : CollatzResearch.WordTrace tailWord_2945097 prefixEnd_2945097 1008166890076379352095501 := by
  unfold tailWord_2945097
  simp only [CollatzResearch.WordTrace]
  refine ⟨107416512211424026368225545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71611008140949350912150363 107416512211424026368225545)
  ·
    refine ⟨80562384158568019776169159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107416512211424026368225545 80562384158568019776169159)
    ·
      refine ⟨120843576237852029664253739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80562384158568019776169159 120843576237852029664253739)
      ·
        refine ⟨181265364356778044496380609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120843576237852029664253739 181265364356778044496380609)
        ·
          refine ⟨135949023267583533372285457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181265364356778044496380609 135949023267583533372285457)
          ·
            refine ⟨101961767450687650029214093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135949023267583533372285457 101961767450687650029214093)
            ·
              refine ⟨38235662794007868760955285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101961767450687650029214093 38235662794007868760955285)
              ·
                refine ⟨1792296693469118848169779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38235662794007868760955285 1792296693469118848169779)
                ·
                  refine ⟨2688445040203678272254669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792296693469118848169779 2688445040203678272254669)
                  ·
                    refine ⟨1008166890076379352095501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688445040203678272254669 1008166890076379352095501)
                    ·
                      rfl

theorem cell22_2945097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_2945097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945097 prefixEnd_2945097 := by exact prefixLift 2945097
  have htrace : WordTrace (prefixWord ++ tailWord_2945097) baseStart_2945097 baseEnd_2945097 := by
    simpa [prefixWord, tailWord_2945097, baseEnd_2945097] using wordTrace_append hprefix tailTrace_2945097
  have hstable : (prefixWord ++ tailWord_2945097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945097).length < 2 ^ (prefixWord ++ tailWord_2945097).sum := by decide
  have hdescent : baseEnd_2945097 < baseStart_2945097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945155 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 6]
def baseStart_2945155 : Nat := 118140960795 + 2945155 * 2 ^ 59
def prefixEnd_2945155 : Nat := 4983230072969 + 3 ^ 40 * 2945155 * 2
def baseEnd_2945155 : Nat := 336062248220562178048441

theorem tailTrace_2945155 : CollatzResearch.WordTrace tailWord_2945155 prefixEnd_2945155 336062248220562178048441 := by
  unfold tailWord_2945155
  simp only [CollatzResearch.WordTrace]
  refine ⟨107418627645213902273836919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71612418430142601515891279 107418627645213902273836919)
  ·
    refine ⟨161127941467820853410755379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107418627645213902273836919 161127941467820853410755379)
    ·
      refine ⟨241691912201731280116133069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161127941467820853410755379 241691912201731280116133069)
      ·
        refine ⟨90634467075649230043549901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241691912201731280116133069 90634467075649230043549901)
        ·
          refine ⟨33987925153368461266331213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90634467075649230043549901 33987925153368461266331213)
          ·
            refine ⟨12745471932513172974874205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33987925153368461266331213 12745471932513172974874205)
            ·
              refine ⟨4779551974692439865577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12745471932513172974874205 4779551974692439865577827)
              ·
                refine ⟨7169327962038659798366741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779551974692439865577827 7169327962038659798366741)
                ·
                  refine ⟨336062248220562178048441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7169327962038659798366741 336062248220562178048441)
                  ·
                    rfl

theorem cell22_2945155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_2945155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945155 prefixEnd_2945155 := by exact prefixLift 2945155
  have htrace : WordTrace (prefixWord ++ tailWord_2945155) baseStart_2945155 baseEnd_2945155 := by
    simpa [prefixWord, tailWord_2945155, baseEnd_2945155] using wordTrace_append hprefix tailTrace_2945155
  have hstable : (prefixWord ++ tailWord_2945155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945155).length < 2 ^ (prefixWord ++ tailWord_2945155).sum := by decide
  have hdescent : baseEnd_2945155 < baseStart_2945155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945191 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2945191 : Nat := 118140960795 + 2945191 * 2 ^ 59
def prefixEnd_2945191 : Nat := 4983230072969 + 3 ^ 40 * 2945191 * 2
def baseEnd_2945191 : Nat := 1008199068197394440245213

theorem tailTrace_2945191 : CollatzResearch.WordTrace tailWord_2945191 prefixEnd_2945191 1008199068197394440245213 := by
  unfold tailWord_2945191
  simp only [CollatzResearch.WordTrace]
  refine ⟨107419940673083480422147427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71613293782055653614764951 107419940673083480422147427)
  ·
    refine ⟨161129911009625220633221141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107419940673083480422147427 161129911009625220633221141)
    ·
      refine ⟨7552964578576182217182241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161129911009625220633221141 7552964578576182217182241)
      ·
        refine ⟨5664723433932136662886681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7552964578576182217182241 5664723433932136662886681)
        ·
          refine ⟨4248542575449102497165011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5664723433932136662886681 4248542575449102497165011)
          ·
            refine ⟨6372813863173653745747517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248542575449102497165011 6372813863173653745747517)
            ·
              refine ⟨2389805198690120154655319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6372813863173653745747517 2389805198690120154655319)
              ·
                refine ⟨3584707798035180231982979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389805198690120154655319 3584707798035180231982979)
                ·
                  refine ⟨5377061697052770347974469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584707798035180231982979 5377061697052770347974469)
                  ·
                    refine ⟨1008199068197394440245213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5377061697052770347974469 1008199068197394440245213)
                    ·
                      rfl

theorem cell22_2945191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2945191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945191 prefixEnd_2945191 := by exact prefixLift 2945191
  have htrace : WordTrace (prefixWord ++ tailWord_2945191) baseStart_2945191 baseEnd_2945191 := by
    simpa [prefixWord, tailWord_2945191, baseEnd_2945191] using wordTrace_append hprefix tailTrace_2945191
  have hstable : (prefixWord ++ tailWord_2945191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945191).length < 2 ^ (prefixWord ++ tailWord_2945191).sum := by decide
  have hdescent : baseEnd_2945191 < baseStart_2945191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945260 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2945260 : Nat := 118140960795 + 2945260 * 2 ^ 59
def prefixEnd_2945260 : Nat := 4983230072969 + 3 ^ 40 * 2945260 * 2
def baseEnd_2945260 : Nat := 1008222688307501260270001

theorem tailTrace_2945260 : CollatzResearch.WordTrace tailWord_2945260 prefixEnd_2945260 1008222688307501260270001 := by
  unfold tailWord_2945260
  simp only [CollatzResearch.WordTrace]
  refine ⟨53711228654916752603204617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71614971539889003470939489 53711228654916752603204617)
  ·
    refine ⟨40283421491187564452403463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53711228654916752603204617 40283421491187564452403463)
    ·
      refine ⟨60425132236781346678605195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40283421491187564452403463 60425132236781346678605195)
      ·
        refine ⟨90637698355172020017907793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60425132236781346678605195 90637698355172020017907793)
        ·
          refine ⟨67978273766379015013430845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90637698355172020017907793 67978273766379015013430845)
          ·
            refine ⟨25491852662392130630036567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67978273766379015013430845 25491852662392130630036567)
            ·
              refine ⟨38237778993588195945054851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25491852662392130630036567 38237778993588195945054851)
              ·
                refine ⟨57356668490382293917582277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38237778993588195945054851 57356668490382293917582277)
                ·
                  refine ⟨10754375341946680109546677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57356668490382293917582277 10754375341946680109546677)
                  ·
                    refine ⟨1008222688307501260270001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10754375341946680109546677 1008222688307501260270001)
                    ·
                      rfl

theorem cell22_2945260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2945260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945260 prefixEnd_2945260 := by exact prefixLift 2945260
  have htrace : WordTrace (prefixWord ++ tailWord_2945260) baseStart_2945260 baseEnd_2945260 := by
    simpa [prefixWord, tailWord_2945260, baseEnd_2945260] using wordTrace_append hprefix tailTrace_2945260
  have hstable : (prefixWord ++ tailWord_2945260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945260).length < 2 ^ (prefixWord ++ tailWord_2945260).sum := by decide
  have hdescent : baseEnd_2945260 < baseStart_2945260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945266 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_2945266 : Nat := 118140960795 + 2945266 * 2 ^ 59
def prefixEnd_2945266 : Nat := 4983230072969 + 3 ^ 40 * 2945266 * 2
def baseEnd_2945266 : Nat := 1008224742230119244619983

theorem tailTrace_2945266 : CollatzResearch.WordTrace tailWord_2945266 prefixEnd_2945266 1008224742230119244619983 := by
  unfold tailWord_2945266
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855669036952942057781913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71615117431874512154085101 26855669036952942057781913)
  ·
    refine ⟨20141751777714706543336435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26855669036952942057781913 20141751777714706543336435)
    ·
      refine ⟨30212627666572059815004653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20141751777714706543336435 30212627666572059815004653)
      ·
        refine ⟨11329735374964522430626745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30212627666572059815004653 11329735374964522430626745)
        ·
          refine ⟨8497301531223391822970059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11329735374964522430626745 8497301531223391822970059)
          ·
            refine ⟨12745952296835087734455089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497301531223391822970059 12745952296835087734455089)
            ·
              refine ⟨9559464222626315800841317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12745952296835087734455089 9559464222626315800841317)
              ·
                refine ⟨1792399541742434212657747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9559464222626315800841317 1792399541742434212657747)
                ·
                  refine ⟨2688599312613651318986621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792399541742434212657747 2688599312613651318986621)
                  ·
                    refine ⟨1008224742230119244619983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688599312613651318986621 1008224742230119244619983)
                    ·
                      rfl

theorem cell22_2945266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_2945266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945266 prefixEnd_2945266 := by exact prefixLift 2945266
  have htrace : WordTrace (prefixWord ++ tailWord_2945266) baseStart_2945266 baseEnd_2945266 := by
    simpa [prefixWord, tailWord_2945266, baseEnd_2945266] using wordTrace_append hprefix tailTrace_2945266
  have hstable : (prefixWord ++ tailWord_2945266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945266).length < 2 ^ (prefixWord ++ tailWord_2945266).sum := by decide
  have hdescent : baseEnd_2945266 < baseStart_2945266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945412 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2945412 : Nat := 118140960795 + 2945412 * 2 ^ 59
def prefixEnd_2945412 : Nat := 4983230072969 + 3 ^ 40 * 2945412 * 2
def baseEnd_2945412 : Nat := 1008274721013823530469535

theorem tailTrace_2945412 : CollatzResearch.WordTrace tailWord_2945412 prefixEnd_2945412 1008274721013823530469535 := by
  unfold tailWord_2945412
  simp only [CollatzResearch.WordTrace]
  refine ⟨53714000602641417582971245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71618667470188556777294993 53714000602641417582971245)
  ·
    refine ⟨20142750225990531593614217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53714000602641417582971245 20142750225990531593614217)
    ·
      refine ⟨15107062669492898695210663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20142750225990531593614217 15107062669492898695210663)
      ·
        refine ⟨22660594004239348042815995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15107062669492898695210663 22660594004239348042815995)
        ·
          refine ⟨33990891006359022064223993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22660594004239348042815995 33990891006359022064223993)
          ·
            refine ⟨25493168254769266548167995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33990891006359022064223993 25493168254769266548167995)
            ·
              refine ⟨38239752382153899822251993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25493168254769266548167995 38239752382153899822251993)
              ·
                refine ⟨28679814286615424866688995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38239752382153899822251993 28679814286615424866688995)
                ·
                  refine ⟨43019721429923137300033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28679814286615424866688995 43019721429923137300033493)
                  ·
                    refine ⟨1008274721013823530469535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43019721429923137300033493 1008274721013823530469535)
                    ·
                      rfl

theorem cell22_2945412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2945412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945412 prefixEnd_2945412 := by exact prefixLift 2945412
  have htrace : WordTrace (prefixWord ++ tailWord_2945412) baseStart_2945412 baseEnd_2945412 := by
    simpa [prefixWord, tailWord_2945412, baseEnd_2945412] using wordTrace_append hprefix tailTrace_2945412
  have hstable : (prefixWord ++ tailWord_2945412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945412).length < 2 ^ (prefixWord ++ tailWord_2945412).sum := by decide
  have hdescent : baseEnd_2945412 < baseStart_2945412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945448 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_2945448 : Nat := 118140960795 + 2945448 * 2 ^ 59
def prefixEnd_2945448 : Nat := 4983230072969 + 3 ^ 40 * 2945448 * 2
def baseEnd_2945448 : Nat := 336095681516510478856475

theorem tailTrace_2945448 : CollatzResearch.WordTrace tailWord_2945448 prefixEnd_2945448 336095681516510478856475 := by
  unfold tailWord_2945448
  simp only [CollatzResearch.WordTrace]
  refine ⟨53714657116576206657126499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71619542822101608876168665 53714657116576206657126499)
  ·
    refine ⟨80571985674864309985689749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53714657116576206657126499 80571985674864309985689749)
    ·
      refine ⟨3776811828509264530579207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80571985674864309985689749 3776811828509264530579207)
      ·
        refine ⟨5665217742763896795868811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776811828509264530579207 5665217742763896795868811)
        ·
          refine ⟨8497826614145845193803217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665217742763896795868811 8497826614145845193803217)
          ·
            refine ⟨6373369960609383895352413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8497826614145845193803217 6373369960609383895352413)
            ·
              refine ⟨2390013735228518960757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6373369960609383895352413 2390013735228518960757155)
              ·
                refine ⟨3585020602842778441135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390013735228518960757155 3585020602842778441135733)
                ·
                  refine ⟨336095681516510478856475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3585020602842778441135733 336095681516510478856475)
                  ·
                    rfl

theorem cell22_2945448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_2945448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945448 prefixEnd_2945448 := by exact prefixLift 2945448
  have htrace : WordTrace (prefixWord ++ tailWord_2945448) baseStart_2945448 baseEnd_2945448 := by
    simpa [prefixWord, tailWord_2945448, baseEnd_2945448] using wordTrace_append hprefix tailTrace_2945448
  have hstable : (prefixWord ++ tailWord_2945448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945448).length < 2 ^ (prefixWord ++ tailWord_2945448).sum := by decide
  have hdescent : baseEnd_2945448 < baseStart_2945448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945493 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 4]
def baseStart_2945493 : Nat := 118140960795 + 2945493 * 2 ^ 59
def prefixEnd_2945493 : Nat := 4983230072969 + 3 ^ 40 * 2945493 * 2
def baseEnd_2945493 : Nat := 336100816323055439731429

theorem tailTrace_2945493 : CollatzResearch.WordTrace tailWord_2945493 prefixEnd_2945493 336100816323055439731429 := by
  unfold tailWord_2945493
  simp only [CollatzResearch.WordTrace]
  refine ⟨107430955517989385999641133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71620637011992923999760755 107430955517989385999641133)
  ·
    refine ⟨40286608319246019749865425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107430955517989385999641133 40286608319246019749865425)
    ·
      refine ⟨30214956239434514812399069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40286608319246019749865425 30214956239434514812399069)
      ·
        refine ⟨11330608589787943054649651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30214956239434514812399069 11330608589787943054649651)
        ·
          refine ⟨16995912884681914581974477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330608589787943054649651 16995912884681914581974477)
          ·
            refine ⟨6373467331755717968240429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16995912884681914581974477 6373467331755717968240429)
            ·
              refine ⟨2390050249408394238090161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6373467331755717968240429 2390050249408394238090161)
              ·
                refine ⟨1792537687056295678567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390050249408394238090161 1792537687056295678567621)
                ·
                  refine ⟨336100816323055439731429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792537687056295678567621 336100816323055439731429)
                  ·
                    rfl

theorem cell22_2945493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_2945493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945493 prefixEnd_2945493 := by exact prefixLift 2945493
  have htrace : WordTrace (prefixWord ++ tailWord_2945493) baseStart_2945493 baseEnd_2945493 := by
    simpa [prefixWord, tailWord_2945493, baseEnd_2945493] using wordTrace_append hprefix tailTrace_2945493
  have hstable : (prefixWord ++ tailWord_2945493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945493).length < 2 ^ (prefixWord ++ tailWord_2945493).sum := by decide
  have hdescent : baseEnd_2945493 < baseStart_2945493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945519 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 5, 3]
def baseStart_2945519 : Nat := 118140960795 + 2945519 * 2 ^ 59
def prefixEnd_2945519 : Nat := 4983230072969 + 3 ^ 40 * 2945519 * 2
def baseEnd_2945519 : Nat := 1008311349300510918044207

theorem tailTrace_2945519 : CollatzResearch.WordTrace tailWord_2945519 prefixEnd_2945519 1008311349300510918044207 := by
  unfold tailWord_2945519
  simp only [CollatzResearch.WordTrace]
  refine ⟨107431903815895192440087611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71621269210596794960058407 107431903815895192440087611)
  ·
    refine ⟨161147855723842788660131417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107431903815895192440087611 161147855723842788660131417)
    ·
      refine ⟨120860891792882091495098563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161147855723842788660131417 120860891792882091495098563)
      ·
        refine ⟨181291337689323137242647845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120860891792882091495098563 181291337689323137242647845)
        ·
          refine ⟨33992125816748088232996471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181291337689323137242647845 33992125816748088232996471)
          ·
            refine ⟨50988188725122132349494707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33992125816748088232996471 50988188725122132349494707)
            ·
              refine ⟨76482283087683198524242061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50988188725122132349494707 76482283087683198524242061)
              ·
                refine ⟨28680856157881199446590773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76482283087683198524242061 28680856157881199446590773)
                ·
                  refine ⟨2688830264801362448117885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28680856157881199446590773 2688830264801362448117885)
                  ·
                    refine ⟨1008311349300510918044207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688830264801362448117885 1008311349300510918044207)
                    ·
                      rfl

theorem cell22_2945519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_2945519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945519 prefixEnd_2945519 := by exact prefixLift 2945519
  have htrace : WordTrace (prefixWord ++ tailWord_2945519) baseStart_2945519 baseEnd_2945519 := by
    simpa [prefixWord, tailWord_2945519, baseEnd_2945519] using wordTrace_append hprefix tailTrace_2945519
  have hstable : (prefixWord ++ tailWord_2945519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945519).length < 2 ^ (prefixWord ++ tailWord_2945519).sum := by decide
  have hdescent : baseEnd_2945519 < baseStart_2945519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945542 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2945542 : Nat := 118140960795 + 2945542 * 2 ^ 59
def prefixEnd_2945542 : Nat := 4983230072969 + 3 ^ 40 * 2945542 * 2
def baseEnd_2945542 : Nat := 1008319222670546524719137

theorem tailTrace_2945542 : CollatzResearch.WordTrace tailWord_2945542 prefixEnd_2945542 1008319222670546524719137 := by
  unfold tailWord_2945542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357273209212870855255465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71621828463207911578783253 3357273209212870855255465)
  ·
    refine ⟨2517954906909653141441599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357273209212870855255465 2517954906909653141441599)
    ·
      refine ⟨3776932360364479712162399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517954906909653141441599 3776932360364479712162399)
      ·
        refine ⟨5665398540546719568243599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776932360364479712162399 5665398540546719568243599)
        ·
          refine ⟨8498097810820079352365399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665398540546719568243599 8498097810820079352365399)
          ·
            refine ⟨12747146716230119028548099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8498097810820079352365399 12747146716230119028548099)
            ·
              refine ⟨19120720074345178542822149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747146716230119028548099 19120720074345178542822149)
              ·
                refine ⟨3585135013939720976779153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19120720074345178542822149 3585135013939720976779153)
                ·
                  refine ⟨2688851260454790732584365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585135013939720976779153 2688851260454790732584365)
                  ·
                    refine ⟨1008319222670546524719137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688851260454790732584365 1008319222670546524719137)
                    ·
                      rfl

theorem cell22_2945542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2945542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945542 prefixEnd_2945542 := by exact prefixLift 2945542
  have htrace : WordTrace (prefixWord ++ tailWord_2945542) baseStart_2945542 baseEnd_2945542 := by
    simpa [prefixWord, tailWord_2945542, baseEnd_2945542] using wordTrace_append hprefix tailTrace_2945542
  have hstable : (prefixWord ++ tailWord_2945542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945542).length < 2 ^ (prefixWord ++ tailWord_2945542).sum := by decide
  have hdescent : baseEnd_2945542 < baseStart_2945542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945564 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2945564 : Nat := 118140960795 + 2945564 * 2 ^ 59
def prefixEnd_2945564 : Nat := 4983230072969 + 3 ^ 40 * 2945564 * 2
def baseEnd_2945564 : Nat := 1008326753720145800669069

theorem tailTrace_2945564 : CollatzResearch.WordTrace tailWord_2945564 prefixEnd_2945564 1008326753720145800669069 := by
  unfold tailWord_2945564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53716772550366082562737873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71622363400488110083650497 53716772550366082562737873)
  ·
    refine ⟨40287579412774561922053405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53716772550366082562737873 40287579412774561922053405)
    ·
      refine ⟨15107842279790460720770027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40287579412774561922053405 15107842279790460720770027)
      ·
        refine ⟨22661763419685691081155041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15107842279790460720770027 22661763419685691081155041)
        ·
          refine ⟨16996322564764268310866281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661763419685691081155041 16996322564764268310866281)
          ·
            refine ⟨12747241923573201233149711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16996322564764268310866281 12747241923573201233149711)
            ·
              refine ⟨19120862885359801849724567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747241923573201233149711 19120862885359801849724567)
              ·
                refine ⟨28681294328039702774586851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19120862885359801849724567 28681294328039702774586851)
                ·
                  refine ⟨43021941492059554161880277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28681294328039702774586851 43021941492059554161880277)
                  ·
                    refine ⟨1008326753720145800669069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43021941492059554161880277 1008326753720145800669069)
                    ·
                      rfl

theorem cell22_2945564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2945564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945564 prefixEnd_2945564 := by exact prefixLift 2945564
  have htrace : WordTrace (prefixWord ++ tailWord_2945564) baseStart_2945564 baseEnd_2945564 := by
    simpa [prefixWord, tailWord_2945564, baseEnd_2945564] using wordTrace_append hprefix tailTrace_2945564
  have hstable : (prefixWord ++ tailWord_2945564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945564).length < 2 ^ (prefixWord ++ tailWord_2945564).sum := by decide
  have hdescent : baseEnd_2945564 < baseStart_2945564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945611 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 4]
def baseStart_2945611 : Nat := 118140960795 + 2945611 * 2 ^ 59
def prefixEnd_2945611 : Nat := 4983230072969 + 3 ^ 40 * 2945611 * 2
def baseEnd_2945611 : Nat := 336114280926884448247975

theorem tailTrace_2945611 : CollatzResearch.WordTrace tailWord_2945611 prefixEnd_2945611 336114280926884448247975 := by
  unfold tailWord_2945611
  simp only [CollatzResearch.WordTrace]
  refine ⟨107435259331561892152436687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71623506221041261434957791 107435259331561892152436687)
  ·
    refine ⟨161152888997342838228655031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107435259331561892152436687 161152888997342838228655031)
    ·
      refine ⟨241729333496014257342982547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161152888997342838228655031 241729333496014257342982547)
      ·
        refine ⟨362594000244021386014473821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241729333496014257342982547 362594000244021386014473821)
        ·
          refine ⟨135972750091508019755427683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362594000244021386014473821 135972750091508019755427683)
          ·
            refine ⟨203959125137262029633141525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135972750091508019755427683 203959125137262029633141525)
            ·
              refine ⟨9560583990809157639053509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203959125137262029633141525 9560583990809157639053509)
              ·
                refine ⟨1792609498276717057322533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9560583990809157639053509 1792609498276717057322533)
                ·
                  refine ⟨336114280926884448247975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792609498276717057322533 336114280926884448247975)
                  ·
                    rfl

theorem cell22_2945611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 4].length) (baseStart_2945611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945611 prefixEnd_2945611 := by exact prefixLift 2945611
  have htrace : WordTrace (prefixWord ++ tailWord_2945611) baseStart_2945611 baseEnd_2945611 := by
    simpa [prefixWord, tailWord_2945611, baseEnd_2945611] using wordTrace_append hprefix tailTrace_2945611
  have hstable : (prefixWord ++ tailWord_2945611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945611).length < 2 ^ (prefixWord ++ tailWord_2945611).sum := by decide
  have hdescent : baseEnd_2945611 < baseStart_2945611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945624 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2945624 : Nat := 118140960795 + 2945624 * 2 ^ 59
def prefixEnd_2945624 : Nat := 4983230072969 + 3 ^ 40 * 2945624 * 2
def baseEnd_2945624 : Nat := 1008347292946325644168885

theorem tailTrace_2945624 : CollatzResearch.WordTrace tailWord_2945624 prefixEnd_2945624 1008347292946325644168885 := by
  unfold tailWord_2945624
  simp only [CollatzResearch.WordTrace]
  refine ⟨53717866740257397686329963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71623822320343196915106617 53717866740257397686329963)
  ·
    refine ⟨80576800110386096529494945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53717866740257397686329963 80576800110386096529494945)
    ·
      refine ⟨60432600082789572397121209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80576800110386096529494945 60432600082789572397121209)
      ·
        refine ⟨45324450062092179297840907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60432600082789572397121209 45324450062092179297840907)
        ·
          refine ⟨67986675093138268946761361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45324450062092179297840907 67986675093138268946761361)
          ·
            refine ⟨50990006319853701710071021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67986675093138268946761361 50990006319853701710071021)
            ·
              refine ⟨19121252369945138141276633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50990006319853701710071021 19121252369945138141276633)
              ·
                refine ⟨14340939277458853605957475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19121252369945138141276633 14340939277458853605957475)
                ·
                  refine ⟨21511408916188280408936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14340939277458853605957475 21511408916188280408936213)
                  ·
                    refine ⟨1008347292946325644168885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21511408916188280408936213 1008347292946325644168885)
                    ·
                      rfl

theorem cell22_2945624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2945624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945624 prefixEnd_2945624 := by exact prefixLift 2945624
  have htrace : WordTrace (prefixWord ++ tailWord_2945624) baseStart_2945624 baseEnd_2945624 := by
    simpa [prefixWord, tailWord_2945624, baseEnd_2945624] using wordTrace_append hprefix tailTrace_2945624
  have hstable : (prefixWord ++ tailWord_2945624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945624).length < 2 ^ (prefixWord ++ tailWord_2945624).sum := by decide
  have hdescent : baseEnd_2945624 < baseStart_2945624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945645 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2945645 : Nat := 118140960795 + 2945645 * 2 ^ 59
def prefixEnd_2945645 : Nat := 4983230072969 + 3 ^ 40 * 2945645 * 2
def baseEnd_2945645 : Nat := 336118160558496196464607

theorem tailTrace_2945645 : CollatzResearch.WordTrace tailWord_2945645 prefixEnd_2945645 336118160558496196464607 := by
  unfold tailWord_2945645
  simp only [CollatzResearch.WordTrace]
  refine ⟨107436499413438715959174389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71624332942292477306116259 107436499413438715959174389)
  ·
    refine ⟨10072171820009879621172599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107436499413438715959174389 10072171820009879621172599)
    ·
      refine ⟨15108257730014819431758899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10072171820009879621172599 15108257730014819431758899)
      ·
        refine ⟨22662386595022229147638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15108257730014819431758899 22662386595022229147638349)
        ·
          refine ⟨8498394973133335930364381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22662386595022229147638349 8498394973133335930364381)
          ·
            refine ⟨3186898114925000973886643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8498394973133335930364381 3186898114925000973886643)
            ·
              refine ⟨4780347172387501460829965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186898114925000973886643 4780347172387501460829965)
              ·
                refine ⟨1792630189645313047811237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4780347172387501460829965 1792630189645313047811237)
                ·
                  refine ⟨336118160558496196464607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792630189645313047811237 336118160558496196464607)
                  ·
                    rfl

theorem cell22_2945645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2945645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945645 prefixEnd_2945645 := by exact prefixLift 2945645
  have htrace : WordTrace (prefixWord ++ tailWord_2945645) baseStart_2945645 baseEnd_2945645 := by
    simpa [prefixWord, tailWord_2945645, baseEnd_2945645] using wordTrace_append hprefix tailTrace_2945645
  have hstable : (prefixWord ++ tailWord_2945645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945645).length < 2 ^ (prefixWord ++ tailWord_2945645).sum := by decide
  have hdescent : baseEnd_2945645 < baseStart_2945645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945699 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_2945699 : Nat := 118140960795 + 2945699 * 2 ^ 59
def prefixEnd_2945699 : Nat := 4983230072969 + 3 ^ 40 * 2945699 * 2
def baseEnd_2945699 : Nat := 1008372966979050448543655

theorem tailTrace_2945699 : CollatzResearch.WordTrace tailWord_2945699 prefixEnd_2945699 1008372966979050448543655 := by
  unfold tailWord_2945699
  simp only [CollatzResearch.WordTrace]
  refine ⟨107438468955243083181640151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71625645970162055454426767 107438468955243083181640151)
  ·
    refine ⟨161157703432864624772460227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107438468955243083181640151 161157703432864624772460227)
    ·
      refine ⟨241736555149296937158690341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161157703432864624772460227 241736555149296937158690341)
      ·
        refine ⟨45325604090493175717254439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241736555149296937158690341 45325604090493175717254439)
        ·
          refine ⟨67988406135739763575881659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45325604090493175717254439 67988406135739763575881659)
          ·
            refine ⟨101982609203609645363822489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67988406135739763575881659 101982609203609645363822489)
            ·
              refine ⟨76486956902707234022866867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101982609203609645363822489 76486956902707234022866867)
              ·
                refine ⟨114730435354060851034300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76486956902707234022866867 114730435354060851034300301)
                ·
                  refine ⟨43023913257772819137862613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114730435354060851034300301 43023913257772819137862613)
                  ·
                    refine ⟨1008372966979050448543655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43023913257772819137862613 1008372966979050448543655)
                    ·
                      rfl

theorem cell22_2945699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_2945699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945699 prefixEnd_2945699 := by exact prefixLift 2945699
  have htrace : WordTrace (prefixWord ++ tailWord_2945699) baseStart_2945699 baseEnd_2945699 := by
    simpa [prefixWord, tailWord_2945699, baseEnd_2945699] using wordTrace_append hprefix tailTrace_2945699
  have hstable : (prefixWord ++ tailWord_2945699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945699).length < 2 ^ (prefixWord ++ tailWord_2945699).sum := by decide
  have hdescent : baseEnd_2945699 < baseStart_2945699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945765 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_2945765 : Nat := 118140960795 + 2945765 * 2 ^ 59
def prefixEnd_2945765 : Nat := 4983230072969 + 3 ^ 40 * 2945765 * 2
def baseEnd_2945765 : Nat := 1008395560127848276393453

theorem tailTrace_2945765 : CollatzResearch.WordTrace tailWord_2945765 prefixEnd_2945765 1008395560127848276393453 := by
  unfold tailWord_2945765
  simp only [CollatzResearch.WordTrace]
  refine ⟨107440876173003976453542749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71627250782002650969028499 107440876173003976453542749)
  ·
    refine ⟨40290328564876491170078531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107440876173003976453542749 40290328564876491170078531)
    ·
      refine ⟨60435492847314736755117797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40290328564876491170078531 60435492847314736755117797)
      ·
        refine ⟨11331654908871513141584587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60435492847314736755117797 11331654908871513141584587)
        ·
          refine ⟨16997482363307269712376881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331654908871513141584587 16997482363307269712376881)
          ·
            refine ⟨12748111772480452284282661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16997482363307269712376881 12748111772480452284282661)
            ·
              refine ⟨2390270957340084803302999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12748111772480452284282661 2390270957340084803302999)
              ·
                refine ⟨3585406436010127204954499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390270957340084803302999 3585406436010127204954499)
                ·
                  refine ⟨5378109654015190807431749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585406436010127204954499 5378109654015190807431749)
                  ·
                    refine ⟨1008395560127848276393453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378109654015190807431749 1008395560127848276393453)
                    ·
                      rfl

theorem cell22_2945765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_2945765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945765 prefixEnd_2945765 := by exact prefixLift 2945765
  have htrace : WordTrace (prefixWord ++ tailWord_2945765) baseStart_2945765 baseEnd_2945765 := by
    simpa [prefixWord, tailWord_2945765, baseEnd_2945765] using wordTrace_append hprefix tailTrace_2945765
  have hstable : (prefixWord ++ tailWord_2945765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945765).length < 2 ^ (prefixWord ++ tailWord_2945765).sum := by decide
  have hdescent : baseEnd_2945765 < baseStart_2945765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945776 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_2945776 : Nat := 118140960795 + 2945776 * 2 ^ 59
def prefixEnd_2945776 : Nat := 4983230072969 + 3 ^ 40 * 2945776 * 2
def baseEnd_2945776 : Nat := 1008399325652647914368419

theorem tailTrace_2945776 : CollatzResearch.WordTrace tailWord_2945776 prefixEnd_2945776 1008399325652647914368419 := by
  unfold tailWord_2945776
  simp only [CollatzResearch.WordTrace]
  refine ⟨53720638687982062666096591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71627518250642750221462121 53720638687982062666096591)
  ·
    refine ⟨80580958031973093999144887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53720638687982062666096591 80580958031973093999144887)
    ·
      refine ⟨120871437047959640998717331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80580958031973093999144887 120871437047959640998717331)
      ·
        refine ⟨181307155571939461498075997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120871437047959640998717331 181307155571939461498075997)
        ·
          refine ⟨67990183339477298061778499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181307155571939461498075997 67990183339477298061778499)
          ·
            refine ⟨101985275009215947092667749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67990183339477298061778499 101985275009215947092667749)
            ·
              refine ⟨19122239064227990079875203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101985275009215947092667749 19122239064227990079875203)
              ·
                refine ⟨28683358596341985119812805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19122239064227990079875203 28683358596341985119812805)
                ·
                  refine ⟨5378129736814122209964901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28683358596341985119812805 5378129736814122209964901)
                  ·
                    refine ⟨1008399325652647914368419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378129736814122209964901 1008399325652647914368419)
                    ·
                      rfl

theorem cell22_2945776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_2945776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945776 prefixEnd_2945776 := by exact prefixLift 2945776
  have htrace : WordTrace (prefixWord ++ tailWord_2945776) baseStart_2945776 baseEnd_2945776 := by
    simpa [prefixWord, tailWord_2945776, baseEnd_2945776] using wordTrace_append hprefix tailTrace_2945776
  have hstable : (prefixWord ++ tailWord_2945776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945776).length < 2 ^ (prefixWord ++ tailWord_2945776).sum := by decide
  have hdescent : baseEnd_2945776 < baseStart_2945776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945806 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2945806 : Nat := 118140960795 + 2945806 * 2 ^ 59
def prefixEnd_2945806 : Nat := 4983230072969 + 3 ^ 40 * 2945806 * 2
def baseEnd_2945806 : Nat := 1008409595265737836118327

theorem tailTrace_2945806 : CollatzResearch.WordTrace tailWord_2945806 prefixEnd_2945806 1008409595265737836118327 := by
  unfold tailWord_2945806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430296445731930056973159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71628247710570293637190181 13430296445731930056973159)
  ·
    refine ⟨20145444668597895085459739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13430296445731930056973159 20145444668597895085459739)
    ·
      refine ⟨30218167002896842628189609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20145444668597895085459739 30218167002896842628189609)
      ·
        refine ⟨22663625252172631971142207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30218167002896842628189609 22663625252172631971142207)
        ·
          refine ⟨33995437878258947956713311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22663625252172631971142207 33995437878258947956713311)
          ·
            refine ⟨50993156817388421935069967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33995437878258947956713311 50993156817388421935069967)
            ·
              refine ⟨76489735226082632902604951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50993156817388421935069967 76489735226082632902604951)
              ·
                refine ⟨114734602839123949353907427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76489735226082632902604951 114734602839123949353907427)
                ·
                  refine ⟨172101904258685924030861141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114734602839123949353907427 172101904258685924030861141)
                  ·
                    refine ⟨1008409595265737836118327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172101904258685924030861141 1008409595265737836118327)
                    ·
                      rfl

theorem cell22_2945806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2945806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945806 prefixEnd_2945806 := by exact prefixLift 2945806
  have htrace : WordTrace (prefixWord ++ tailWord_2945806) baseStart_2945806 baseEnd_2945806 := by
    simpa [prefixWord, tailWord_2945806, baseEnd_2945806] using wordTrace_append hprefix tailTrace_2945806
  have hstable : (prefixWord ++ tailWord_2945806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945806).length < 2 ^ (prefixWord ++ tailWord_2945806).sum := by decide
  have hdescent : baseEnd_2945806 < baseStart_2945806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945836 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_2945836 : Nat := 118140960795 + 2945836 * 2 ^ 59
def prefixEnd_2945836 : Nat := 4983230072969 + 3 ^ 40 * 2945836 * 2
def baseEnd_2945836 : Nat := 336139954959609252622745

theorem tailTrace_2945836 : CollatzResearch.WordTrace tailWord_2945836 prefixEnd_2945836 336139954959609252622745 := by
  unfold tailWord_2945836
  simp only [CollatzResearch.WordTrace]
  refine ⟨53721732877873377789688681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71628977170497837052918241 53721732877873377789688681)
  ·
    refine ⟨40291299658405033342266511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53721732877873377789688681 40291299658405033342266511)
    ·
      refine ⟨60436949487607550013399767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40291299658405033342266511 60436949487607550013399767)
      ·
        refine ⟨90655424231411325020099651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60436949487607550013399767 90655424231411325020099651)
        ·
          refine ⟨135983136347116987530149477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90655424231411325020099651 135983136347116987530149477)
          ·
            refine ⟨25496838065084435161903027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135983136347116987530149477 25496838065084435161903027)
            ·
              refine ⟨38245257097626652742854541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25496838065084435161903027 38245257097626652742854541)
              ·
                refine ⟨14341971411609994778570453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38245257097626652742854541 14341971411609994778570453)
                ·
                  refine ⟨336139954959609252622745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14341971411609994778570453 336139954959609252622745)
                  ·
                    rfl

theorem cell22_2945836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_2945836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945836 prefixEnd_2945836 := by exact prefixLift 2945836
  have htrace : WordTrace (prefixWord ++ tailWord_2945836) baseStart_2945836 baseEnd_2945836 := by
    simpa [prefixWord, tailWord_2945836, baseEnd_2945836] using wordTrace_append hprefix tailTrace_2945836
  have hstable : (prefixWord ++ tailWord_2945836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945836).length < 2 ^ (prefixWord ++ tailWord_2945836).sum := by decide
  have hdescent : baseEnd_2945836 < baseStart_2945836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945840 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_2945840 : Nat := 118140960795 + 2945840 * 2 ^ 59
def prefixEnd_2945840 : Nat := 4983230072969 + 3 ^ 40 * 2945840 * 2
def baseEnd_2945840 : Nat := 1008421234160573080768223

theorem tailTrace_2945840 : CollatzResearch.WordTrace tailWord_2945840 prefixEnd_2945840 1008421234160573080768223 := by
  unfold tailWord_2945840
  simp only [CollatzResearch.WordTrace]
  refine ⟨53721805823866132131261487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71629074431821509508348649 53721805823866132131261487)
  ·
    refine ⟨80582708735799198196892231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53721805823866132131261487 80582708735799198196892231)
    ·
      refine ⟨120874063103698797295338347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80582708735799198196892231 120874063103698797295338347)
      ·
        refine ⟨181311094655548195943007521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120874063103698797295338347 181311094655548195943007521)
        ·
          refine ⟨135983320991661146957255641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181311094655548195943007521 135983320991661146957255641)
          ·
            refine ⟨101987490743745860217941731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135983320991661146957255641 101987490743745860217941731)
            ·
              refine ⟨152981236115618790326912597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101987490743745860217941731 152981236115618790326912597)
              ·
                refine ⟨1792748860729907699143507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 152981236115618790326912597 1792748860729907699143507)
                ·
                  refine ⟨2689123291094861548715261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792748860729907699143507 2689123291094861548715261)
                  ·
                    refine ⟨1008421234160573080768223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689123291094861548715261 1008421234160573080768223)
                    ·
                      rfl

theorem cell22_2945840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_2945840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945840 prefixEnd_2945840 := by exact prefixLift 2945840
  have htrace : WordTrace (prefixWord ++ tailWord_2945840) baseStart_2945840 baseEnd_2945840 := by
    simpa [prefixWord, tailWord_2945840, baseEnd_2945840] using wordTrace_append hprefix tailTrace_2945840
  have hstable : (prefixWord ++ tailWord_2945840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945840).length < 2 ^ (prefixWord ++ tailWord_2945840).sum := by decide
  have hdescent : baseEnd_2945840 < baseStart_2945840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945846 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2945846 : Nat := 118140960795 + 2945846 * 2 ^ 59
def prefixEnd_2945846 : Nat := 4983230072969 + 3 ^ 40 * 2945846 * 2
def baseEnd_2945846 : Nat := 1008423288083191065118205

theorem tailTrace_2945846 : CollatzResearch.WordTrace tailWord_2945846 prefixEnd_2945846 1008423288083191065118205 := by
  unfold tailWord_2945846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715239405356907955452587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71629220323807018191494261 6715239405356907955452587)
  ·
    refine ⟨10072859108035361933178881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715239405356907955452587 10072859108035361933178881)
    ·
      refine ⟨7554644331026521449884161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10072859108035361933178881 7554644331026521449884161)
      ·
        refine ⟨5665983248269891087413121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7554644331026521449884161 5665983248269891087413121)
        ·
          refine ⟨4249487436202418315559841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5665983248269891087413121 4249487436202418315559841)
          ·
            refine ⟨3187115577151813736669881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4249487436202418315559841 3187115577151813736669881)
            ·
              refine ⟨2390336682863860302502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187115577151813736669881 2390336682863860302502411)
              ·
                refine ⟨3585505024295790453753617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390336682863860302502411 3585505024295790453753617)
                ·
                  refine ⟨2689128768221842840315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585505024295790453753617 2689128768221842840315213)
                  ·
                    refine ⟨1008423288083191065118205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689128768221842840315213 1008423288083191065118205)
                    ·
                      rfl

theorem cell22_2945846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2945846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945846 prefixEnd_2945846 := by exact prefixLift 2945846
  have htrace : WordTrace (prefixWord ++ tailWord_2945846) baseStart_2945846 baseEnd_2945846 := by
    simpa [prefixWord, tailWord_2945846, baseEnd_2945846] using wordTrace_append hprefix tailTrace_2945846
  have hstable : (prefixWord ++ tailWord_2945846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945846).length < 2 ^ (prefixWord ++ tailWord_2945846).sum := by decide
  have hdescent : baseEnd_2945846 < baseStart_2945846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945913 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_2945913 : Nat := 118140960795 + 2945913 * 2 ^ 59
def prefixEnd_2945913 : Nat := 4983230072969 + 3 ^ 40 * 2945913 * 2
def baseEnd_2945913 : Nat := 1008446223552425223692999

theorem tailTrace_2945913 : CollatzResearch.WordTrace tailWord_2945913 prefixEnd_2945913 1008446223552425223692999 := by
  unfold tailWord_2945913
  simp only [CollatzResearch.WordTrace]
  refine ⟨107446274176467797729930393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71630849450978531819953595 107446274176467797729930393)
  ·
    refine ⟨80584705632350848297447795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107446274176467797729930393 80584705632350848297447795)
    ·
      refine ⟨120877058448526272446171693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80584705632350848297447795 120877058448526272446171693)
      ·
        refine ⟨45328896918197352167314385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120877058448526272446171693 45328896918197352167314385)
        ·
          refine ⟨33996672688648014125485789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45328896918197352167314385 33996672688648014125485789)
          ·
            refine ⟨12748752258243005297057171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33996672688648014125485789 12748752258243005297057171)
            ·
              refine ⟨19123128387364507945585757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12748752258243005297057171 19123128387364507945585757)
              ·
                refine ⟨7171173145261690479594659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19123128387364507945585757 7171173145261690479594659)
                ·
                  refine ⟨10756759717892535719391989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171173145261690479594659 10756759717892535719391989)
                  ·
                    refine ⟨1008446223552425223692999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10756759717892535719391989 1008446223552425223692999)
                    ·
                      rfl

theorem cell22_2945913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_2945913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945913 prefixEnd_2945913 := by exact prefixLift 2945913
  have htrace : WordTrace (prefixWord ++ tailWord_2945913) baseStart_2945913 baseEnd_2945913 := by
    simpa [prefixWord, tailWord_2945913, baseEnd_2945913] using wordTrace_append hprefix tailTrace_2945913
  have hstable : (prefixWord ++ tailWord_2945913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945913).length < 2 ^ (prefixWord ++ tailWord_2945913).sum := by decide
  have hdescent : baseEnd_2945913 < baseStart_2945913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945930 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_2945930 : Nat := 118140960795 + 2945930 * 2 ^ 59
def prefixEnd_2945930 : Nat := 4983230072969 + 3 ^ 40 * 2945930 * 2
def baseEnd_2945930 : Nat := 1008452042999842846017947

theorem tailTrace_2945930 : CollatzResearch.WordTrace tailWord_2945930 prefixEnd_2945930 1008452042999842846017947 := by
  unfold tailWord_2945930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26861723554351552408324811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71631262811604139755532829 26861723554351552408324811)
  ·
    refine ⟨40292585331527328612487217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26861723554351552408324811 40292585331527328612487217)
    ·
      refine ⟨30219438998645496459365413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40292585331527328612487217 30219438998645496459365413)
      ·
        refine ⟨5666144812246030586131015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30219438998645496459365413 5666144812246030586131015)
        ·
          refine ⟨8499217218369045879196523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5666144812246030586131015 8499217218369045879196523)
          ·
            refine ⟨12748825827553568818794785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499217218369045879196523 12748825827553568818794785)
            ·
              refine ⟨9561619370665176614096089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12748825827553568818794785 9561619370665176614096089)
              ·
                refine ⟨7171214527998882460572067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9561619370665176614096089 7171214527998882460572067)
                ·
                  refine ⟨10756821791998323690858101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171214527998882460572067 10756821791998323690858101)
                  ·
                    refine ⟨1008452042999842846017947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10756821791998323690858101 1008452042999842846017947)
                    ·
                      rfl

theorem cell22_2945930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_2945930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945930 prefixEnd_2945930 := by exact prefixLift 2945930
  have htrace : WordTrace (prefixWord ++ tailWord_2945930) baseStart_2945930 baseEnd_2945930 := by
    simpa [prefixWord, tailWord_2945930, baseEnd_2945930] using wordTrace_append hprefix tailTrace_2945930
  have hstable : (prefixWord ++ tailWord_2945930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945930).length < 2 ^ (prefixWord ++ tailWord_2945930).sum := by decide
  have hdescent : baseEnd_2945930 < baseStart_2945930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945975 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 3, 3]
def baseStart_2945975 : Nat := 118140960795 + 2945975 * 2 ^ 59
def prefixEnd_2945975 : Nat := 4983230072969 + 3 ^ 40 * 2945975 * 2
def baseEnd_2945975 : Nat := 1008467447419477728642809

theorem tailTrace_2945975 : CollatzResearch.WordTrace tailWord_2945975 prefixEnd_2945975 1008467447419477728642809 := by
  unfold tailWord_2945975
  simp only [CollatzResearch.WordTrace]
  refine ⟨107448535502243182318687379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71632357001495454879124919 107448535502243182318687379)
  ·
    refine ⟨161172803253364773478031069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107448535502243182318687379 161172803253364773478031069)
    ·
      refine ⟨60439801220011790054261651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161172803253364773478031069 60439801220011790054261651)
      ·
        refine ⟨90659701830017685081392477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60439801220011790054261651 90659701830017685081392477)
        ·
          refine ⟨33997388186256631905522179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90659701830017685081392477 33997388186256631905522179)
          ·
            refine ⟨50996082279384947858283269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33997388186256631905522179 50996082279384947858283269)
            ·
              refine ⟨9561765427384677723428113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50996082279384947858283269 9561765427384677723428113)
              ·
                refine ⟨7171324070538508292571085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9561765427384677723428113 7171324070538508292571085)
                ·
                  refine ⟨2689246526451940609714157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7171324070538508292571085 2689246526451940609714157)
                  ·
                    refine ⟨1008467447419477728642809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689246526451940609714157 1008467447419477728642809)
                    ·
                      rfl

theorem cell22_2945975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_2945975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2945975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2945975 prefixEnd_2945975 := by exact prefixLift 2945975
  have htrace : WordTrace (prefixWord ++ tailWord_2945975) baseStart_2945975 baseEnd_2945975 := by
    simpa [prefixWord, tailWord_2945975, baseEnd_2945975] using wordTrace_append hprefix tailTrace_2945975
  have hstable : (prefixWord ++ tailWord_2945975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945975).length < 2 ^ (prefixWord ++ tailWord_2945975).sum := by decide
  have hdescent : baseEnd_2945975 < baseStart_2945975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_2946065 : Nat := 118140960795 + 2946065 * 2 ^ 59
def prefixEnd_2946065 : Nat := 4983230072969 + 3 ^ 40 * 2946065 * 2
def baseEnd_2946065 : Nat := 1008498256258747493892533

theorem tailTrace_2946065 : CollatzResearch.WordTrace tailWord_2946065 prefixEnd_2946065 1008498256258747493892533 := by
  unfold tailWord_2946065
  simp only [CollatzResearch.WordTrace]
  refine ⟨107451818071917127689463649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71634545381278085126309099 107451818071917127689463649)
  ·
    refine ⟨80588863553937845767097737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107451818071917127689463649 80588863553937845767097737)
    ·
      refine ⟨60441647665453384325323303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80588863553937845767097737 60441647665453384325323303)
      ·
        refine ⟨90662471498180076487984955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60441647665453384325323303 90662471498180076487984955)
        ·
          refine ⟨135993707247270114731977433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90662471498180076487984955 135993707247270114731977433)
          ·
            refine ⟨101995280435452586048983075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135993707247270114731977433 101995280435452586048983075)
            ·
              refine ⟨152992920653178879073474613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101995280435452586048983075 152992920653178879073474613)
              ·
                refine ⟨14343086311235519913138245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152992920653178879073474613 14343086311235519913138245)
                ·
                  refine ⟨2689328683356659983713421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14343086311235519913138245 2689328683356659983713421)
                  ·
                    refine ⟨1008498256258747493892533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689328683356659983713421 1008498256258747493892533)
                    ·
                      rfl

theorem cell22_2946065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_2946065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946065 prefixEnd_2946065 := by exact prefixLift 2946065
  have htrace : WordTrace (prefixWord ++ tailWord_2946065) baseStart_2946065 baseEnd_2946065 := by
    simpa [prefixWord, tailWord_2946065, baseEnd_2946065] using wordTrace_append hprefix tailTrace_2946065
  have hstable : (prefixWord ++ tailWord_2946065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946065).length < 2 ^ (prefixWord ++ tailWord_2946065).sum := by decide
  have hdescent : baseEnd_2946065 < baseStart_2946065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946082 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2946082 : Nat := 118140960795 + 2946082 * 2 ^ 59
def prefixEnd_2946082 : Nat := 4983230072969 + 3 ^ 40 * 2946082 * 2
def baseEnd_2946082 : Nat := 1008504075706165116217481

theorem tailTrace_2946082 : CollatzResearch.WordTrace tailWord_2946082 prefixEnd_2946082 1008504075706165116217481 := by
  unfold tailWord_2946082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26863109528213884898208125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71634958741903693061888333 26863109528213884898208125)
  ·
    refine ⟨10073666073080206836828047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26863109528213884898208125 10073666073080206836828047)
    ·
      refine ⟨15110499109620310255242071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10073666073080206836828047 15110499109620310255242071)
      ·
        refine ⟨22665748664430465382863107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15110499109620310255242071 22665748664430465382863107)
        ·
          refine ⟨33998622996645698074294661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22665748664430465382863107 33998622996645698074294661)
          ·
            refine ⟨6374741811871068388930249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33998622996645698074294661 6374741811871068388930249)
            ·
              refine ⟨4781056358903301291697687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6374741811871068388930249 4781056358903301291697687)
              ·
                refine ⟨7171584538354951937546531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781056358903301291697687 7171584538354951937546531)
                ·
                  refine ⟨10757376807532427906319797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171584538354951937546531 10757376807532427906319797)
                  ·
                    refine ⟨1008504075706165116217481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10757376807532427906319797 1008504075706165116217481)
                    ·
                      rfl

theorem cell22_2946082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2946082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946082 prefixEnd_2946082 := by exact prefixLift 2946082
  have htrace : WordTrace (prefixWord ++ tailWord_2946082) baseStart_2946082 baseEnd_2946082 := by
    simpa [prefixWord, tailWord_2946082, baseEnd_2946082] using wordTrace_append hprefix tailTrace_2946082
  have hstable : (prefixWord ++ tailWord_2946082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946082).length < 2 ^ (prefixWord ++ tailWord_2946082).sum := by decide
  have hdescent : baseEnd_2946082 < baseStart_2946082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946204 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2946204 : Nat := 118140960795 + 2946204 * 2 ^ 59
def prefixEnd_2946204 : Nat := 4983230072969 + 3 ^ 40 * 2946204 * 2
def baseEnd_2946204 : Nat := 1008545838799397464667107

theorem tailTrace_2946204 : CollatzResearch.WordTrace tailWord_2946204 prefixEnd_2946204 1008545838799397464667107 := by
  unfold tailWord_2946204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53728443909206777214386833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71637925212275702952515777 53728443909206777214386833)
  ·
    refine ⟨40296332931905082910790125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53728443909206777214386833 40296332931905082910790125)
    ·
      refine ⟨15111124849464406091546297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40296332931905082910790125 15111124849464406091546297)
      ·
        refine ⟨11333343637098304568659723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15111124849464406091546297 11333343637098304568659723)
        ·
          refine ⟨17000015455647456852989585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11333343637098304568659723 17000015455647456852989585)
          ·
            refine ⟨12750011591735592639742189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17000015455647456852989585 12750011591735592639742189)
            ·
              refine ⟨4781254346900847239903321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12750011591735592639742189 4781254346900847239903321)
              ·
                refine ⟨3585940760175635429927491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781254346900847239903321 3585940760175635429927491)
                ·
                  refine ⟨5378911140263453144891237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585940760175635429927491 5378911140263453144891237)
                  ·
                    refine ⟨1008545838799397464667107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5378911140263453144891237 1008545838799397464667107)
                    ·
                      rfl

theorem cell22_2946204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2946204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946204 prefixEnd_2946204 := by exact prefixLift 2946204
  have htrace : WordTrace (prefixWord ++ tailWord_2946204) baseStart_2946204 baseEnd_2946204 := by
    simpa [prefixWord, tailWord_2946204, baseEnd_2946204] using wordTrace_append hprefix tailTrace_2946204
  have hstable : (prefixWord ++ tailWord_2946204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946204).length < 2 ^ (prefixWord ++ tailWord_2946204).sum := by decide
  have hdescent : baseEnd_2946204 < baseStart_2946204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946236 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_2946236 : Nat := 118140960795 + 2946236 * 2 ^ 59
def prefixEnd_2946236 : Nat := 4983230072969 + 3 ^ 40 * 2946236 * 2
def baseEnd_2946236 : Nat := 336185597684453349289003

theorem tailTrace_2946236 : CollatzResearch.WordTrace tailWord_2946236 prefixEnd_2946236 336185597684453349289003 := by
  unfold tailWord_2946236
  simp only [CollatzResearch.WordTrace]
  refine ⟨53729027477148811946969281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71638703302865082595959041 53729027477148811946969281)
  ·
    refine ⟨40296770607861608960226961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53729027477148811946969281 40296770607861608960226961)
    ·
      refine ⟨30222577955896206720170221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40296770607861608960226961 30222577955896206720170221)
      ·
        refine ⟨11333466733461077520063833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30222577955896206720170221 11333466733461077520063833)
        ·
          refine ⟨8500100050095808140047875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11333466733461077520063833 8500100050095808140047875)
          ·
            refine ⟨12750150075143712210071813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8500100050095808140047875 12750150075143712210071813)
            ·
              refine ⟨2390653139089446039388465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12750150075143712210071813 2390653139089446039388465)
              ·
                refine ⟨1792989854317084529541349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390653139089446039388465 1792989854317084529541349)
                ·
                  refine ⟨336185597684453349289003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792989854317084529541349 336185597684453349289003)
                  ·
                    rfl

theorem cell22_2946236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_2946236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946236 prefixEnd_2946236 := by exact prefixLift 2946236
  have htrace : WordTrace (prefixWord ++ tailWord_2946236) baseStart_2946236 baseEnd_2946236 := by
    simpa [prefixWord, tailWord_2946236, baseEnd_2946236] using wordTrace_append hprefix tailTrace_2946236
  have hstable : (prefixWord ++ tailWord_2946236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946236).length < 2 ^ (prefixWord ++ tailWord_2946236).sum := by decide
  have hdescent : baseEnd_2946236 < baseStart_2946236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2946245 : Nat := 118140960795 + 2946245 * 2 ^ 59
def prefixEnd_2946245 : Nat := 4983230072969 + 3 ^ 40 * 2946245 * 2
def baseEnd_2946245 : Nat := 1008559873937287024391981

theorem tailTrace_2946245 : CollatzResearch.WordTrace tailWord_2946245 prefixEnd_2946245 1008559873937287024391981 := by
  unfold tailWord_2946245
  simp only [CollatzResearch.WordTrace]
  refine ⟨107458383211265018431016189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71638922140843345620677459 107458383211265018431016189)
  ·
    refine ⟨40296893704224381911631071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107458383211265018431016189 40296893704224381911631071)
    ·
      refine ⟨60445340556336572867446607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40296893704224381911631071 60445340556336572867446607)
      ·
        refine ⟨90668010834504859301169911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60445340556336572867446607 90668010834504859301169911)
        ·
          refine ⟨136002016251757288951754867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90668010834504859301169911 136002016251757288951754867)
          ·
            refine ⟨204003024377635933427632301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136002016251757288951754867 204003024377635933427632301)
            ·
              refine ⟨76501134141613475035362113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204003024377635933427632301 76501134141613475035362113)
              ·
                refine ⟨57375850606210106276521585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76501134141613475035362113 57375850606210106276521585)
                ·
                  refine ⟨43031887954657579707391189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57375850606210106276521585 43031887954657579707391189)
                  ·
                    refine ⟨1008559873937287024391981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43031887954657579707391189 1008559873937287024391981)
                    ·
                      rfl

theorem cell22_2946245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2946245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946245 prefixEnd_2946245 := by exact prefixLift 2946245
  have htrace : WordTrace (prefixWord ++ tailWord_2946245) baseStart_2946245 baseEnd_2946245 := by
    simpa [prefixWord, tailWord_2946245, baseEnd_2946245] using wordTrace_append hprefix tailTrace_2946245
  have hstable : (prefixWord ++ tailWord_2946245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946245).length < 2 ^ (prefixWord ++ tailWord_2946245).sum := by decide
  have hdescent : baseEnd_2946245 < baseStart_2946245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946264 : List Nat := [2, 1, 2, 2, 5, 1, 3, 6]
def baseStart_2946264 : Nat := 118140960795 + 2946264 * 2 ^ 59
def prefixEnd_2946264 : Nat := 4983230072969 + 3 ^ 40 * 2946264 * 2
def baseEnd_2946264 : Nat := 112062930891730812018547

theorem tailTrace_2946264 : CollatzResearch.WordTrace tailWord_2946264 prefixEnd_2946264 112062930891730812018547 := by
  unfold tailWord_2946264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53729538099098092337978923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71639384132130789783971897 53729538099098092337978923)
  ·
    refine ⟨80594307148647138506968385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53729538099098092337978923 80594307148647138506968385)
    ·
      refine ⟨60445730361485353880226289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80594307148647138506968385 60445730361485353880226289)
      ·
        refine ⟨45334297771114015410169717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60445730361485353880226289 45334297771114015410169717)
        ·
          refine ⟨4250090416041938944703411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45334297771114015410169717 4250090416041938944703411)
          ·
            refine ⟨6375135624062908417055117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250090416041938944703411 6375135624062908417055117)
            ·
              refine ⟨2390675859023590656395669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6375135624062908417055117 2390675859023590656395669)
              ·
                refine ⟨112062930891730812018547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2390675859023590656395669 112062930891730812018547)
                ·
                  rfl

theorem cell22_2946264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_2946264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946264 prefixEnd_2946264 := by exact prefixLift 2946264
  have htrace : WordTrace (prefixWord ++ tailWord_2946264) baseStart_2946264 baseEnd_2946264 := by
    simpa [prefixWord, tailWord_2946264, baseEnd_2946264] using wordTrace_append hprefix tailTrace_2946264
  have hstable : (prefixWord ++ tailWord_2946264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946264).length < 2 ^ (prefixWord ++ tailWord_2946264).sum := by decide
  have hdescent : baseEnd_2946264 < baseStart_2946264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946307 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_2946307 : Nat := 118140960795 + 2946307 * 2 ^ 59
def prefixEnd_2946307 : Nat := 4983230072969 + 3 ^ 40 * 2946307 * 2
def baseEnd_2946307 : Nat := 1008581097804339529341791

theorem tailTrace_2946307 : CollatzResearch.WordTrace tailWord_2946307 prefixEnd_2946307 1008581097804339529341791 := by
  unfold tailWord_2946307
  simp only [CollatzResearch.WordTrace]
  refine ⟨107460644537040403019773175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71640429691360268679848783 107460644537040403019773175)
  ·
    refine ⟨161190966805560604529659763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107460644537040403019773175 161190966805560604529659763)
    ·
      refine ⟨241786450208340906794489645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161190966805560604529659763 241786450208340906794489645)
      ·
        refine ⟨90669918828127840047933617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241786450208340906794489645 90669918828127840047933617)
        ·
          refine ⟨68002439121095880035950213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90669918828127840047933617 68002439121095880035950213)
          ·
            refine ⟨12750457335205477506740665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68002439121095880035950213 12750457335205477506740665)
            ·
              refine ⟨9562843001404108130055499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12750457335205477506740665 9562843001404108130055499)
              ·
                refine ⟨14344264502106162195083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9562843001404108130055499 14344264502106162195083249)
                ·
                  refine ⟨10758198376579621646312437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14344264502106162195083249 10758198376579621646312437)
                  ·
                    refine ⟨1008581097804339529341791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10758198376579621646312437 1008581097804339529341791)
                    ·
                      rfl

theorem cell22_2946307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_2946307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946307 prefixEnd_2946307 := by exact prefixLift 2946307
  have htrace : WordTrace (prefixWord ++ tailWord_2946307) baseStart_2946307 baseEnd_2946307 := by
    simpa [prefixWord, tailWord_2946307, baseEnd_2946307] using wordTrace_append hprefix tailTrace_2946307
  have hstable : (prefixWord ++ tailWord_2946307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946307).length < 2 ^ (prefixWord ++ tailWord_2946307).sum := by decide
  have hdescent : baseEnd_2946307 < baseStart_2946307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946309 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 5]
def baseStart_2946309 : Nat := 118140960795 + 2946309 * 2 ^ 59
def prefixEnd_2946309 : Nat := 4983230072969 + 3 ^ 40 * 2946309 * 2
def baseEnd_2946309 : Nat := 336193927481737396930595

theorem tailTrace_2946309 : CollatzResearch.WordTrace tailWord_2946309 prefixEnd_2946309 336193927481737396930595 := by
  unfold tailWord_2946309
  simp only [CollatzResearch.WordTrace]
  refine ⟨107460717483033157361345981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71640478322022104907563987 107460717483033157361345981)
  ·
    refine ⟨40297769056137434010504743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107460717483033157361345981 40297769056137434010504743)
    ·
      refine ⟨60446653584206151015757115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40297769056137434010504743 60446653584206151015757115)
      ·
        refine ⟨90669980376309226523635673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60446653584206151015757115 90669980376309226523635673)
        ·
          refine ⟨68002485282231919892726755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90669980376309226523635673 68002485282231919892726755)
          ·
            refine ⟨102003727923347879839090133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68002485282231919892726755 102003727923347879839090133)
            ·
              refine ⟨2390712373203465933728675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102003727923347879839090133 2390712373203465933728675)
              ·
                refine ⟨3586068559805198900593013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390712373203465933728675 3586068559805198900593013)
                ·
                  refine ⟨336193927481737396930595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3586068559805198900593013 336193927481737396930595)
                  ·
                    rfl

theorem cell22_2946309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_2946309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946309 prefixEnd_2946309 := by exact prefixLift 2946309
  have htrace : WordTrace (prefixWord ++ tailWord_2946309) baseStart_2946309 baseEnd_2946309 := by
    simpa [prefixWord, tailWord_2946309, baseEnd_2946309] using wordTrace_append hprefix tailTrace_2946309
  have hstable : (prefixWord ++ tailWord_2946309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946309).length < 2 ^ (prefixWord ++ tailWord_2946309).sum := by decide
  have hdescent : baseEnd_2946309 < baseStart_2946309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946339 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 1, 4]
def baseStart_2946339 : Nat := 118140960795 + 2946339 * 2 ^ 59
def prefixEnd_2946339 : Nat := 4983230072969 + 3 ^ 40 * 2946339 * 2
def baseEnd_2946339 : Nat := 1008592052058302112541693

theorem tailTrace_2946339 : CollatzResearch.WordTrace tailWord_2946339 prefixEnd_2946339 1008592052058302112541693 := by
  unfold tailWord_2946339
  simp only [CollatzResearch.WordTrace]
  refine ⟨107461811672924472484938071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71641207781949648323292047 107461811672924472484938071)
  ·
    refine ⟨161192717509386708727407107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107461811672924472484938071 161192717509386708727407107)
    ·
      refine ⟨241789076264080063091110661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161192717509386708727407107 241789076264080063091110661)
      ·
        refine ⟨45335451799515011829583249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241789076264080063091110661 45335451799515011829583249)
        ·
          refine ⟨34001588849636258872187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45335451799515011829583249 34001588849636258872187437)
          ·
            refine ⟨12750595818613597077070289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34001588849636258872187437 12750595818613597077070289)
            ·
              refine ⟨9562946863960197807802717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12750595818613597077070289 9562946863960197807802717)
              ·
                refine ⟨3586105073985074177926019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9562946863960197807802717 3586105073985074177926019)
                ·
                  refine ⟨5379157610977611266889029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586105073985074177926019 5379157610977611266889029)
                  ·
                    refine ⟨1008592052058302112541693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379157610977611266889029 1008592052058302112541693)
                    ·
                      rfl

theorem cell22_2946339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_2946339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946339 prefixEnd_2946339 := by exact prefixLift 2946339
  have htrace : WordTrace (prefixWord ++ tailWord_2946339) baseStart_2946339 baseEnd_2946339 := by
    simpa [prefixWord, tailWord_2946339, baseEnd_2946339] using wordTrace_append hprefix tailTrace_2946339
  have hstable : (prefixWord ++ tailWord_2946339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946339).length < 2 ^ (prefixWord ++ tailWord_2946339).sum := by decide
  have hdescent : baseEnd_2946339 < baseStart_2946339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946354 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2946354 : Nat := 118140960795 + 2946354 * 2 ^ 59
def prefixEnd_2946354 : Nat := 4983230072969 + 3 ^ 40 * 2946354 * 2
def baseEnd_2946354 : Nat := 336199062288282357805549

theorem tailTrace_2946354 : CollatzResearch.WordTrace tailWord_2946354 prefixEnd_2946354 336199062288282357805549 := by
  unfold tailWord_2946354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26865589691967532511683529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71641572511913420031156077 26865589691967532511683529)
  ·
    refine ⟨20149192268975649383762647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26865589691967532511683529 20149192268975649383762647)
    ·
      refine ⟨30223788403463474075643971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20149192268975649383762647 30223788403463474075643971)
      ·
        refine ⟨45335682605195211113465957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30223788403463474075643971 45335682605195211113465957)
        ·
          refine ⟨8500440488474102083774867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45335682605195211113465957 8500440488474102083774867)
          ·
            refine ⟨12750660732711153125662301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8500440488474102083774867 12750660732711153125662301)
            ·
              refine ⟨4781497774766682422123363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12750660732711153125662301 4781497774766682422123363)
              ·
                refine ⟨7172246662150023633185045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781497774766682422123363 7172246662150023633185045)
                ·
                  refine ⟨336199062288282357805549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7172246662150023633185045 336199062288282357805549)
                  ·
                    rfl

theorem cell22_2946354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2946354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946354 prefixEnd_2946354 := by exact prefixLift 2946354
  have htrace : WordTrace (prefixWord ++ tailWord_2946354) baseStart_2946354 baseEnd_2946354 := by
    simpa [prefixWord, tailWord_2946354, baseEnd_2946354] using wordTrace_append hprefix tailTrace_2946354
  have hstable : (prefixWord ++ tailWord_2946354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946354).length < 2 ^ (prefixWord ++ tailWord_2946354).sum := by decide
  have hdescent : baseEnd_2946354 < baseStart_2946354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946382 : List Nat := [4, 1, 1, 1, 1, 1, 3, 10]
def baseStart_2946382 : Nat := 118140960795 + 2946382 * 2 ^ 59
def prefixEnd_2946382 : Nat := 4983230072969 + 3 ^ 40 * 2946382 * 2
def baseEnd_2946382 : Nat := 112067419093007148190729

theorem tailTrace_2946382 : CollatzResearch.WordTrace tailWord_2946382 prefixEnd_2946382 112067419093007148190729 := by
  unfold tailWord_2946382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432922501471086353594175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71642253341179127219168933 13432922501471086353594175)
  ·
    refine ⟨20149383752206629530391263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13432922501471086353594175 20149383752206629530391263)
    ·
      refine ⟨30224075628309944295586895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20149383752206629530391263 30224075628309944295586895)
      ·
        refine ⟨45336113442464916443380343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30224075628309944295586895 45336113442464916443380343)
        ·
          refine ⟨68004170163697374665070515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45336113442464916443380343 68004170163697374665070515)
          ·
            refine ⟨102006255245546061997605773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68004170163697374665070515 102006255245546061997605773)
            ·
              refine ⟨38252345717079773249102165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102006255245546061997605773 38252345717079773249102165)
              ·
                refine ⟨112067419093007148190729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38252345717079773249102165 112067419093007148190729)
                ·
                  rfl

theorem cell22_2946382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_2946382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946382 prefixEnd_2946382 := by exact prefixLift 2946382
  have htrace : WordTrace (prefixWord ++ tailWord_2946382) baseStart_2946382 baseEnd_2946382 := by
    simpa [prefixWord, tailWord_2946382, baseEnd_2946382] using wordTrace_append hprefix tailTrace_2946382
  have hstable : (prefixWord ++ tailWord_2946382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946382).length < 2 ^ (prefixWord ++ tailWord_2946382).sum := by decide
  have hdescent : baseEnd_2946382 < baseStart_2946382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946384 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_2946384 : Nat := 118140960795 + 2946384 * 2 ^ 59
def prefixEnd_2946384 : Nat := 4983230072969 + 3 ^ 40 * 2946384 * 2
def baseEnd_2946384 : Nat := 1008607456477936995166555

theorem tailTrace_2946384 : CollatzResearch.WordTrace tailWord_2946384 prefixEnd_2946384 1008607456477936995166555 := by
  unfold tailWord_2946384
  simp only [CollatzResearch.WordTrace]
  refine ⟨53731726478880722585163103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71642301971840963446884137 53731726478880722585163103)
  ·
    refine ⟨80597589718321083877744655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53731726478880722585163103 80597589718321083877744655)
    ·
      refine ⟨120896384577481625816616983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80597589718321083877744655 120896384577481625816616983)
      ·
        refine ⟨181344576866222438724925475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120896384577481625816616983 181344576866222438724925475)
        ·
          refine ⟨272016865299333658087388213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181344576866222438724925475 272016865299333658087388213)
          ·
            refine ⟨25501581121812530445692645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272016865299333658087388213 25501581121812530445692645)
            ·
              refine ⟨4781546460339849458567371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25501581121812530445692645 4781546460339849458567371)
              ·
                refine ⟨7172319690509774187851057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781546460339849458567371 7172319690509774187851057)
                ·
                  refine ⟨5379239767882330640888293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172319690509774187851057 5379239767882330640888293)
                  ·
                    refine ⟨1008607456477936995166555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379239767882330640888293 1008607456477936995166555)
                    ·
                      rfl

theorem cell22_2946384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_2946384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946384 prefixEnd_2946384 := by exact prefixLift 2946384
  have htrace : WordTrace (prefixWord ++ tailWord_2946384) baseStart_2946384 baseEnd_2946384 := by
    simpa [prefixWord, tailWord_2946384, baseEnd_2946384] using wordTrace_append hprefix tailTrace_2946384
  have hstable : (prefixWord ++ tailWord_2946384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946384).length < 2 ^ (prefixWord ++ tailWord_2946384).sum := by decide
  have hdescent : baseEnd_2946384 < baseStart_2946384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946461 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2946461 : Nat := 118140960795 + 2946461 * 2 ^ 59
def prefixEnd_2946461 : Nat := 4983230072969 + 3 ^ 40 * 2946461 * 2
def baseEnd_2946461 : Nat := 336211271717178153663773

theorem tailTrace_2946461 : CollatzResearch.WordTrace tailWord_2946461 prefixEnd_2946461 336211271717178153663773 := by
  unfold tailWord_2946461
  simp only [CollatzResearch.WordTrace]
  refine ⟨107466261378482487320879237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71644174252321658213919491 107466261378482487320879237)
  ·
    refine ⟨20149924008465466372664857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107466261378482487320879237 20149924008465466372664857)
    ·
      refine ⟨15112443006349099779498643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20149924008465466372664857 15112443006349099779498643)
      ·
        refine ⟨22668664509523649669247965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15112443006349099779498643 22668664509523649669247965)
        ·
          refine ⟨8500749191071368625967987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22668664509523649669247965 8500749191071368625967987)
          ·
            refine ⟨12751123786607052938951981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8500749191071368625967987 12751123786607052938951981)
            ·
              refine ⟨4781671419977644852106993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12751123786607052938951981 4781671419977644852106993)
              ·
                refine ⟨3586253564983233639080245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781671419977644852106993 3586253564983233639080245)
                ·
                  refine ⟨336211271717178153663773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3586253564983233639080245 336211271717178153663773)
                  ·
                    rfl

theorem cell22_2946461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2946461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946461 prefixEnd_2946461 := by exact prefixLift 2946461
  have htrace : WordTrace (prefixWord ++ tailWord_2946461) baseStart_2946461 baseEnd_2946461 := by
    simpa [prefixWord, tailWord_2946461, baseEnd_2946461] using wordTrace_append hprefix tailTrace_2946461
  have hstable : (prefixWord ++ tailWord_2946461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946461).length < 2 ^ (prefixWord ++ tailWord_2946461).sum := by decide
  have hdescent : baseEnd_2946461 < baseStart_2946461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946504 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2946504 : Nat := 118140960795 + 2946504 * 2 ^ 59
def prefixEnd_2946504 : Nat := 4983230072969 + 3 ^ 40 * 2946504 * 2
def baseEnd_2946504 : Nat := 1008648534930296682166187

theorem tailTrace_2946504 : CollatzResearch.WordTrace tailWord_2946504 prefixEnd_2946504 1008648534930296682166187 := by
  unfold tailWord_2946504
  simp only [CollatzResearch.WordTrace]
  refine ⟨53733914858663352832347283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71645219811551137109796377 53733914858663352832347283)
  ·
    refine ⟨80600872287995029248520925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53733914858663352832347283 80600872287995029248520925)
    ·
      refine ⟨30225327107998135968195347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80600872287995029248520925 30225327107998135968195347)
      ·
        refine ⟨45337990661997203952293021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30225327107998135968195347 45337990661997203952293021)
        ·
          refine ⟨17001746498248951482109883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45337990661997203952293021 17001746498248951482109883)
          ·
            refine ⟨25502619747373427223164825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17001746498248951482109883 25502619747373427223164825)
            ·
              refine ⟨19126964810530070417373619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25502619747373427223164825 19126964810530070417373619)
              ·
                refine ⟨28690447215795105626060429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19126964810530070417373619 28690447215795105626060429)
                ·
                  refine ⟨10758917705923164609772661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28690447215795105626060429 10758917705923164609772661)
                  ·
                    refine ⟨1008648534930296682166187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10758917705923164609772661 1008648534930296682166187)
                    ·
                      rfl

theorem cell22_2946504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2946504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946504 prefixEnd_2946504 := by exact prefixLift 2946504
  have htrace : WordTrace (prefixWord ++ tailWord_2946504) baseStart_2946504 baseEnd_2946504 := by
    simpa [prefixWord, tailWord_2946504, baseEnd_2946504] using wordTrace_append hprefix tailTrace_2946504
  have hstable : (prefixWord ++ tailWord_2946504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946504).length < 2 ^ (prefixWord ++ tailWord_2946504).sum := by decide
  have hdescent : baseEnd_2946504 < baseStart_2946504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946521 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_2946521 : Nat := 118140960795 + 2946521 * 2 ^ 59
def prefixEnd_2946521 : Nat := 4983230072969 + 3 ^ 40 * 2946521 * 2
def baseEnd_2946521 : Nat := 1008654354377714304491135

theorem tailTrace_2946521 : CollatzResearch.WordTrace tailWord_2946521 prefixEnd_2946521 1008654354377714304491135 := by
  unfold tailWord_2946521
  simp only [CollatzResearch.WordTrace]
  refine ⟨107468449758265117568063417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71645633172176745045375611 107468449758265117568063417)
  ·
    refine ⟨80601337318698838176047563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107468449758265117568063417 80601337318698838176047563)
    ·
      refine ⟨120902005978048257264071345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80601337318698838176047563 120902005978048257264071345)
      ·
        refine ⟨90676504483536192948053509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120902005978048257264071345 90676504483536192948053509)
        ·
          refine ⟨17001844590663036177760033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90676504483536192948053509 17001844590663036177760033)
          ·
            refine ⟨12751383442997277133320025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17001844590663036177760033 12751383442997277133320025)
            ·
              refine ⟨9563537582247957849990019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12751383442997277133320025 9563537582247957849990019)
              ·
                refine ⟨14345306373371936774985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563537582247957849990019 14345306373371936774985029)
                ·
                  refine ⟨2689744945007238145309693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14345306373371936774985029 2689744945007238145309693)
                  ·
                    refine ⟨1008654354377714304491135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689744945007238145309693 1008654354377714304491135)
                    ·
                      rfl

theorem cell22_2946521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_2946521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946521 prefixEnd_2946521 := by exact prefixLift 2946521
  have htrace : WordTrace (prefixWord ++ tailWord_2946521) baseStart_2946521 baseEnd_2946521 := by
    simpa [prefixWord, tailWord_2946521, baseEnd_2946521] using wordTrace_append hprefix tailTrace_2946521
  have hstable : (prefixWord ++ tailWord_2946521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946521).length < 2 ^ (prefixWord ++ tailWord_2946521).sum := by decide
  have hdescent : baseEnd_2946521 < baseStart_2946521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946600 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2946600 : Nat := 118140960795 + 2946600 * 2 ^ 59
def prefixEnd_2946600 : Nat := 4983230072969 + 3 ^ 40 * 2946600 * 2
def baseEnd_2946600 : Nat := 1008681397692184431765893

theorem tailTrace_2946600 : CollatzResearch.WordTrace tailWord_2946600 prefixEnd_2946600 1008681397692184431765893 := by
  unfold tailWord_2946600
  simp only [CollatzResearch.WordTrace]
  refine ⟨53735665562489457030094627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71647554083319276040126169 53735665562489457030094627)
  ·
    refine ⟨80603498343734185545141941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53735665562489457030094627 80603498343734185545141941)
    ·
      refine ⟨7556577969725079894857057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80603498343734185545141941 7556577969725079894857057)
      ·
        refine ⟨5667433477293809921142793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7556577969725079894857057 5667433477293809921142793)
        ·
          refine ⟨4250575107970357440857095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667433477293809921142793 4250575107970357440857095)
          ·
            refine ⟨6375862661955536161285643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250575107970357440857095 6375862661955536161285643)
            ·
              refine ⟨9563793992933304241928465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375862661955536161285643 9563793992933304241928465)
              ·
                refine ⟨7172845494699978181446349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563793992933304241928465 7172845494699978181446349)
                ·
                  refine ⟨2689817060512491818042381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7172845494699978181446349 2689817060512491818042381)
                  ·
                    refine ⟨1008681397692184431765893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689817060512491818042381 1008681397692184431765893)
                    ·
                      rfl

theorem cell22_2946600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2946600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946600 prefixEnd_2946600 := by exact prefixLift 2946600
  have htrace : WordTrace (prefixWord ++ tailWord_2946600) baseStart_2946600 baseEnd_2946600 := by
    simpa [prefixWord, tailWord_2946600, baseEnd_2946600] using wordTrace_append hprefix tailTrace_2946600
  have hstable : (prefixWord ++ tailWord_2946600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946600).length < 2 ^ (prefixWord ++ tailWord_2946600).sum := by decide
  have hdescent : baseEnd_2946600 < baseStart_2946600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946624 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_2946624 : Nat := 118140960795 + 2946624 * 2 ^ 59
def prefixEnd_2946624 : Nat := 4983230072969 + 3 ^ 40 * 2946624 * 2
def baseEnd_2946624 : Nat := 336229871127552123055273

theorem tailTrace_2946624 : CollatzResearch.WordTrace tailWord_2946624 prefixEnd_2946624 336229871127552123055273 := by
  unfold tailWord_2946624
  simp only [CollatzResearch.WordTrace]
  refine ⟨53736103238445983079531463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71648137651261310772708617 53736103238445983079531463)
  ·
    refine ⟨80604154857668974619297195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53736103238445983079531463 80604154857668974619297195)
    ·
      refine ⟨120906232286503461928945793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80604154857668974619297195 120906232286503461928945793)
      ·
        refine ⟨90679674214877596446709345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120906232286503461928945793 90679674214877596446709345)
        ·
          refine ⟨68009755661158197335032009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90679674214877596446709345 68009755661158197335032009)
          ·
            refine ⟨51007316745868648001274007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68009755661158197335032009 51007316745868648001274007)
            ·
              refine ⟨76510975118802972001911011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51007316745868648001274007 76510975118802972001911011)
              ·
                refine ⟨114766462678204458002866517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76510975118802972001911011 114766462678204458002866517)
                ·
                  refine ⟨336229871127552123055273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114766462678204458002866517 336229871127552123055273)
                  ·
                    rfl

theorem cell22_2946624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_2946624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946624 prefixEnd_2946624 := by exact prefixLift 2946624
  have htrace : WordTrace (prefixWord ++ tailWord_2946624) baseStart_2946624 baseEnd_2946624 := by
    simpa [prefixWord, tailWord_2946624, baseEnd_2946624] using wordTrace_append hprefix tailTrace_2946624
  have hstable : (prefixWord ++ tailWord_2946624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946624).length < 2 ^ (prefixWord ++ tailWord_2946624).sum := by decide
  have hdescent : baseEnd_2946624 < baseStart_2946624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946630 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2946630 : Nat := 118140960795 + 2946630 * 2 ^ 59
def prefixEnd_2946630 : Nat := 4983230072969 + 3 ^ 40 * 2946630 * 2
def baseEnd_2946630 : Nat := 336230555768424784505267

theorem tailTrace_2946630 : CollatzResearch.WordTrace tailWord_2946630 prefixEnd_2946630 336230555768424784505267 := by
  unfold tailWord_2946630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358513291089694661993167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71648283543246819455854229 3358513291089694661993167)
  ·
    refine ⟨5037769936634541992989751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3358513291089694661993167 5037769936634541992989751)
    ·
      refine ⟨7556654904951812989484627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5037769936634541992989751 7556654904951812989484627)
      ·
        refine ⟨11334982357427719484226941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7556654904951812989484627 11334982357427719484226941)
        ·
          refine ⟨4250618384035394806585103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11334982357427719484226941 4250618384035394806585103)
          ·
            refine ⟨6375927576053092209877655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250618384035394806585103 6375927576053092209877655)
            ·
              refine ⟨9563891364079638314816483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375927576053092209877655 9563891364079638314816483)
              ·
                refine ⟨14345837046119457472224725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563891364079638314816483 14345837046119457472224725)
                ·
                  refine ⟨336230555768424784505267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14345837046119457472224725 336230555768424784505267)
                  ·
                    rfl

theorem cell22_2946630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2946630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946630 prefixEnd_2946630 := by exact prefixLift 2946630
  have htrace : WordTrace (prefixWord ++ tailWord_2946630) baseStart_2946630 baseEnd_2946630 := by
    simpa [prefixWord, tailWord_2946630, baseEnd_2946630] using wordTrace_append hprefix tailTrace_2946630
  have hstable : (prefixWord ++ tailWord_2946630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946630).length < 2 ^ (prefixWord ++ tailWord_2946630).sum := by decide
  have hdescent : baseEnd_2946630 < baseStart_2946630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946641 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 6]
def baseStart_2946641 : Nat := 118140960795 + 2946641 * 2 ^ 59
def prefixEnd_2946641 : Nat := 4983230072969 + 3 ^ 40 * 2946641 * 2
def baseEnd_2946641 : Nat := 336231810943357997163589

theorem tailTrace_2946641 : CollatzResearch.WordTrace tailWord_2946641 prefixEnd_2946641 336231810943357997163589 := by
  unfold tailWord_2946641
  simp only [CollatzResearch.WordTrace]
  refine ⟨107472826517830378062431777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71648551011886918708287851 107472826517830378062431777)
  ·
    refine ⟨80604619888372783546823833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107472826517830378062431777 80604619888372783546823833)
    ·
      refine ⟨60453464916279587660117875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80604619888372783546823833 60453464916279587660117875)
      ·
        refine ⟨90680197374419381490176813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60453464916279587660117875 90680197374419381490176813)
        ·
          refine ⟨34005074015407268058816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90680197374419381490176813 34005074015407268058816305)
          ·
            refine ⟨25503805511555451044112229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34005074015407268058816305 25503805511555451044112229)
            ·
              refine ⟨4781963533416647070771043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25503805511555451044112229 4781963533416647070771043)
              ·
                refine ⟨7172945300124970606156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781963533416647070771043 7172945300124970606156565)
                ·
                  refine ⟨336231810943357997163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7172945300124970606156565 336231810943357997163589)
                  ·
                    rfl

theorem cell22_2946641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_2946641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946641 prefixEnd_2946641 := by exact prefixLift 2946641
  have htrace : WordTrace (prefixWord ++ tailWord_2946641) baseStart_2946641 baseEnd_2946641 := by
    simpa [prefixWord, tailWord_2946641, baseEnd_2946641] using wordTrace_append hprefix tailTrace_2946641
  have hstable : (prefixWord ++ tailWord_2946641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946641).length < 2 ^ (prefixWord ++ tailWord_2946641).sum := by decide
  have hdescent : baseEnd_2946641 < baseStart_2946641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946671 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_2946671 : Nat := 118140960795 + 2946671 * 2 ^ 59
def prefixEnd_2946671 : Nat := 4983230072969 + 3 ^ 40 * 2946671 * 2
def baseEnd_2946671 : Nat := 1008705702443163913240675

theorem tailTrace_2946671 : CollatzResearch.WordTrace tailWord_2946671 prefixEnd_2946671 1008705702443163913240675 := by
  unfold tailWord_2946671
  simp only [CollatzResearch.WordTrace]
  refine ⟨107473920707721693186023867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71649280471814462124015911 107473920707721693186023867)
  ·
    refine ⟨161210881061582539779035801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107473920707721693186023867 161210881061582539779035801)
    ·
      refine ⟨120908160796186904834276851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161210881061582539779035801 120908160796186904834276851)
      ·
        refine ⟨181362241194280357251415277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120908160796186904834276851 181362241194280357251415277)
        ·
          refine ⟨68010840447855133969280729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181362241194280357251415277 68010840447855133969280729)
          ·
            refine ⟨51008130335891350476960547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68010840447855133969280729 51008130335891350476960547)
            ·
              refine ⟨76512195503837025715440821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51008130335891350476960547 76512195503837025715440821)
              ·
                refine ⟨7173018328484721160822577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76512195503837025715440821 7173018328484721160822577)
                ·
                  refine ⟨5379763746363540870616933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173018328484721160822577 5379763746363540870616933)
                  ·
                    refine ⟨1008705702443163913240675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379763746363540870616933 1008705702443163913240675)
                    ·
                      rfl

theorem cell22_2946671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_2946671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946671 prefixEnd_2946671 := by exact prefixLift 2946671
  have htrace : WordTrace (prefixWord ++ tailWord_2946671) baseStart_2946671 baseEnd_2946671 := by
    simpa [prefixWord, tailWord_2946671, baseEnd_2946671] using wordTrace_append hprefix tailTrace_2946671
  have hstable : (prefixWord ++ tailWord_2946671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946671).length < 2 ^ (prefixWord ++ tailWord_2946671).sum := by decide
  have hdescent : baseEnd_2946671 < baseStart_2946671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946692 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2946692 : Nat := 118140960795 + 2946692 * 2 ^ 59
def prefixEnd_2946692 : Nat := 4983230072969 + 3 ^ 40 * 2946692 * 2
def baseEnd_2946692 : Nat := 336237630390775619488537

theorem tailTrace_2946692 : CollatzResearch.WordTrace tailWord_2946692 prefixEnd_2946692 336237630390775619488537 := by
  unfold tailWord_2946692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53737343320322806886269165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71649791093763742515025553 53737343320322806886269165)
  ·
    refine ⟨20151503745121052582350937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53737343320322806886269165 20151503745121052582350937)
    ·
      refine ⟨15113627808840789436763203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20151503745121052582350937 15113627808840789436763203)
      ·
        refine ⟨22670441713261184155144805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15113627808840789436763203 22670441713261184155144805)
        ·
          refine ⟨4250707821236472029089651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22670441713261184155144805 4250707821236472029089651)
          ·
            refine ⟨6376061731854708043634477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250707821236472029089651 6376061731854708043634477)
            ·
              refine ⟨2391023149445515516362929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6376061731854708043634477 2391023149445515516362929)
              ·
                refine ⟨1793267362084136637272197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391023149445515516362929 1793267362084136637272197)
                ·
                  refine ⟨336237630390775619488537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793267362084136637272197 336237630390775619488537)
                  ·
                    rfl

theorem cell22_2946692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2946692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946692 prefixEnd_2946692 := by exact prefixLift 2946692
  have htrace : WordTrace (prefixWord ++ tailWord_2946692) baseStart_2946692 baseEnd_2946692 := by
    simpa [prefixWord, tailWord_2946692, baseEnd_2946692] using wordTrace_append hprefix tailTrace_2946692
  have hstable : (prefixWord ++ tailWord_2946692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946692).length < 2 ^ (prefixWord ++ tailWord_2946692).sum := by decide
  have hdescent : baseEnd_2946692 < baseStart_2946692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946722 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2946722 : Nat := 118140960795 + 2946722 * 2 ^ 59
def prefixEnd_2946722 : Nat := 4983230072969 + 3 ^ 40 * 2946722 * 2
def baseEnd_2946722 : Nat := 1008723160785416780215519

theorem tailTrace_2946722 : CollatzResearch.WordTrace tailWord_2946722 prefixEnd_2946722 1008723160785416780215519 := by
  unfold tailWord_2946722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868945207634232224032605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71650520553691285930753613 26868945207634232224032605)
  ·
    refine ⟨10075854452862837084012227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26868945207634232224032605 10075854452862837084012227)
    ·
      refine ⟨15113781679294255626018341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075854452862837084012227 15113781679294255626018341)
      ·
        refine ⟨2833834064867672929878439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15113781679294255626018341 2833834064867672929878439)
        ·
          refine ⟨4250751097301509394817659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833834064867672929878439 4250751097301509394817659)
          ·
            refine ⟨6376126645952264092226489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250751097301509394817659 6376126645952264092226489)
            ·
              refine ⟨4782094984464198069169867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376126645952264092226489 4782094984464198069169867)
              ·
                refine ⟨7173142476696297103754801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782094984464198069169867 7173142476696297103754801)
                ·
                  refine ⟨5379856857522222827816101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173142476696297103754801 5379856857522222827816101)
                  ·
                    refine ⟨1008723160785416780215519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379856857522222827816101 1008723160785416780215519)
                    ·
                      rfl

theorem cell22_2946722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2946722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946722 prefixEnd_2946722 := by exact prefixLift 2946722
  have htrace : WordTrace (prefixWord ++ tailWord_2946722) baseStart_2946722 baseEnd_2946722 := by
    simpa [prefixWord, tailWord_2946722, baseEnd_2946722] using wordTrace_append hprefix tailTrace_2946722
  have hstable : (prefixWord ++ tailWord_2946722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946722).length < 2 ^ (prefixWord ++ tailWord_2946722).sum := by decide
  have hdescent : baseEnd_2946722 < baseStart_2946722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946735 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 1, 3]
def baseStart_2946735 : Nat := 118140960795 + 2946735 * 2 ^ 59
def prefixEnd_2946735 : Nat := 4983230072969 + 3 ^ 40 * 2946735 * 2
def baseEnd_2946735 : Nat := 1008727610951089079640479

theorem tailTrace_2946735 : CollatzResearch.WordTrace tailWord_2946735 prefixEnd_2946735 1008727610951089079640479 := by
  unfold tailWord_2946735
  simp only [CollatzResearch.WordTrace]
  refine ⟨107476254979489832116353659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71650836652993221410902439 107476254979489832116353659)
  ·
    refine ⟨161214382469234748174530489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107476254979489832116353659 161214382469234748174530489)
    ·
      refine ⟨120910786851926061130897867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161214382469234748174530489 120910786851926061130897867)
      ·
        refine ⟨181366180277889091696346801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120910786851926061130897867 181366180277889091696346801)
        ·
          refine ⟨136024635208416818772260101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181366180277889091696346801 136024635208416818772260101)
          ·
            refine ⟨25504619101578153519798769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136024635208416818772260101 25504619101578153519798769)
            ·
              refine ⟨19128464326183615139849077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25504619101578153519798769 19128464326183615139849077)
              ·
                refine ⟨1793293530579713919360851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19128464326183615139849077 1793293530579713919360851)
                ·
                  refine ⟨2689940295869570879041277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793293530579713919360851 2689940295869570879041277)
                  ·
                    refine ⟨1008727610951089079640479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2689940295869570879041277 1008727610951089079640479)
                    ·
                      rfl

theorem cell22_2946735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_2946735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946735 prefixEnd_2946735 := by exact prefixLift 2946735
  have htrace : WordTrace (prefixWord ++ tailWord_2946735) baseStart_2946735 baseEnd_2946735 := by
    simpa [prefixWord, tailWord_2946735, baseEnd_2946735] using wordTrace_append hprefix tailTrace_2946735
  have hstable : (prefixWord ++ tailWord_2946735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946735).length < 2 ^ (prefixWord ++ tailWord_2946735).sum := by decide
  have hdescent : baseEnd_2946735 < baseStart_2946735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946748 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_2946748 : Nat := 118140960795 + 2946748 * 2 ^ 59
def prefixEnd_2946748 : Nat := 4983230072969 + 3 ^ 40 * 2946748 * 2
def baseEnd_2946748 : Nat := 336244020372253793021813

theorem tailTrace_2946748 : CollatzResearch.WordTrace tailWord_2946748 prefixEnd_2946748 336244020372253793021813 := by
  unfold tailWord_2946748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53738364564221367668288449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71651152752295156891051265 53738364564221367668288449)
  ·
    refine ⟨40303773423166025751216337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53738364564221367668288449 40303773423166025751216337)
    ·
      refine ⟨30227830067374519313412253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40303773423166025751216337 30227830067374519313412253)
      ·
        refine ⟨11335436275265444742529595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30227830067374519313412253 11335436275265444742529595)
        ·
          refine ⟨17003154412898167113794393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11335436275265444742529595 17003154412898167113794393)
          ·
            refine ⟨12752365809673625335345795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17003154412898167113794393 12752365809673625335345795)
            ·
              refine ⟨19128548714510438003018693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12752365809673625335345795 19128548714510438003018693)
              ·
                refine ⟨3586602883970707125566005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19128548714510438003018693 3586602883970707125566005)
                ·
                  refine ⟨336244020372253793021813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3586602883970707125566005 336244020372253793021813)
                  ·
                    rfl

theorem cell22_2946748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_2946748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946748 prefixEnd_2946748 := by exact prefixLift 2946748
  have htrace : WordTrace (prefixWord ++ tailWord_2946748) baseStart_2946748 baseEnd_2946748 := by
    simpa [prefixWord, tailWord_2946748, baseEnd_2946748] using wordTrace_append hprefix tailTrace_2946748
  have hstable : (prefixWord ++ tailWord_2946748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946748).length < 2 ^ (prefixWord ++ tailWord_2946748).sum := by decide
  have hdescent : baseEnd_2946748 < baseStart_2946748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946754 : List Nat := [3, 5, 1, 2, 1, 2, 1, 7]
def baseStart_2946754 : Nat := 118140960795 + 2946754 * 2 ^ 59
def prefixEnd_2946754 : Nat := 4983230072969 + 3 ^ 40 * 2946754 * 2
def baseEnd_2946754 : Nat := 112081568337708818157269

theorem tailTrace_2946754 : CollatzResearch.WordTrace tailWord_2946754 prefixEnd_2946754 112081568337708818157269 := by
  unfold tailWord_2946754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26869236991605249590323829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71651298644280665574196877 26869236991605249590323829)
  ·
    refine ⟨2518990967962992149092859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26869236991605249590323829 2518990967962992149092859)
    ·
      refine ⟨3778486451944488223639289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518990967962992149092859 3778486451944488223639289)
      ·
        refine ⟨2833864838958366167729467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778486451944488223639289 2833864838958366167729467)
        ·
          refine ⟨4250797258437549251594201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833864838958366167729467 4250797258437549251594201)
          ·
            refine ⟨3188097943828161938695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4250797258437549251594201 3188097943828161938695651)
            ·
              refine ⟨4782146915742242908043477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188097943828161938695651 4782146915742242908043477)
              ·
                refine ⟨112081568337708818157269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4782146915742242908043477 112081568337708818157269)
                ·
                  rfl

theorem cell22_2946754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_2946754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946754 prefixEnd_2946754 := by exact prefixLift 2946754
  have htrace : WordTrace (prefixWord ++ tailWord_2946754) baseStart_2946754 baseEnd_2946754 := by
    simpa [prefixWord, tailWord_2946754, baseEnd_2946754] using wordTrace_append hprefix tailTrace_2946754
  have hstable : (prefixWord ++ tailWord_2946754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946754).length < 2 ^ (prefixWord ++ tailWord_2946754).sum := by decide
  have hdescent : baseEnd_2946754 < baseStart_2946754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946778 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2946778 : Nat := 118140960795 + 2946778 * 2 ^ 59
def prefixEnd_2946778 : Nat := 4983230072969 + 3 ^ 40 * 2946778 * 2
def baseEnd_2946778 : Nat := 1008742330729851300815347

theorem tailTrace_2946778 : CollatzResearch.WordTrace tailWord_2946778 prefixEnd_2946778 1008742330729851300815347 := by
  unfold tailWord_2946778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26869455829583512615042247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71651882212222700306779325 26869455829583512615042247)
  ·
    refine ⟨40304183744375268922563371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26869455829583512615042247 40304183744375268922563371)
    ·
      refine ⟨60456275616562903383845057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40304183744375268922563371 60456275616562903383845057)
      ·
        refine ⟨45342206712422177537883793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60456275616562903383845057 45342206712422177537883793)
        ·
          refine ⟨34006655034316633153412845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45342206712422177537883793 34006655034316633153412845)
          ·
            refine ⟨12752495637868737432529817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34006655034316633153412845 12752495637868737432529817)
            ·
              refine ⟨9564371728401553074397363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12752495637868737432529817 9564371728401553074397363)
              ·
                refine ⟨14346557592602329611596045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9564371728401553074397363 14346557592602329611596045)
                ·
                  refine ⟨5379959097225873604348517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14346557592602329611596045 5379959097225873604348517)
                  ·
                    refine ⟨1008742330729851300815347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379959097225873604348517 1008742330729851300815347)
                    ·
                      rfl

theorem cell22_2946778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2946778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946778 prefixEnd_2946778 := by exact prefixLift 2946778
  have htrace : WordTrace (prefixWord ++ tailWord_2946778) baseStart_2946778 baseEnd_2946778 := by
    simpa [prefixWord, tailWord_2946778, baseEnd_2946778] using wordTrace_append hprefix tailTrace_2946778
  have hstable : (prefixWord ++ tailWord_2946778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946778).length < 2 ^ (prefixWord ++ tailWord_2946778).sum := by decide
  have hdescent : baseEnd_2946778 < baseStart_2946778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946795 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 1, 4]
def baseStart_2946795 : Nat := 118140960795 + 2946795 * 2 ^ 59
def prefixEnd_2946795 : Nat := 4983230072969 + 3 ^ 40 * 2946795 * 2
def baseEnd_2946795 : Nat := 1008748150177268923140295

theorem tailTrace_2946795 : CollatzResearch.WordTrace tailWord_2946795 prefixEnd_2946795 1008748150177268923140295 := by
  unfold tailWord_2946795
  simp only [CollatzResearch.WordTrace]
  refine ⟨107478443359272462363537839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71652295572848308242358559 107478443359272462363537839)
  ·
    refine ⟨161217665038908693545306759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107478443359272462363537839 161217665038908693545306759)
    ·
      refine ⟨241826497558363040317960139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161217665038908693545306759 241826497558363040317960139)
      ·
        refine ⟨362739746337544560476940209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241826497558363040317960139 362739746337544560476940209)
        ·
          refine ⟨272054809753158420357705157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362739746337544560476940209 272054809753158420357705157)
          ·
            refine ⟨51010276828717203817069717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272054809753158420357705157 51010276828717203817069717)
            ·
              refine ⟨2391106726346118928925143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51010276828717203817069717 2391106726346118928925143)
              ·
                refine ⟨3586660089519178393387715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391106726346118928925143 3586660089519178393387715)
                ·
                  refine ⟨5379990134278767590081573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586660089519178393387715 5379990134278767590081573)
                  ·
                    refine ⟨1008748150177268923140295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5379990134278767590081573 1008748150177268923140295)
                    ·
                      rfl

theorem cell22_2946795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 4].length) (baseStart_2946795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946795 prefixEnd_2946795 := by exact prefixLift 2946795
  have htrace : WordTrace (prefixWord ++ tailWord_2946795) baseStart_2946795 baseEnd_2946795 := by
    simpa [prefixWord, tailWord_2946795, baseEnd_2946795] using wordTrace_append hprefix tailTrace_2946795
  have hstable : (prefixWord ++ tailWord_2946795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946795).length < 2 ^ (prefixWord ++ tailWord_2946795).sum := by decide
  have hdescent : baseEnd_2946795 < baseStart_2946795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946928 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_2946928 : Nat := 118140960795 + 2946928 * 2 ^ 59
def prefixEnd_2946928 : Nat := 4983230072969 + 3 ^ 40 * 2946928 * 2
def baseEnd_2946928 : Nat := 336264559598433636521629

theorem tailTrace_2946928 : CollatzResearch.WordTrace tailWord_2946928 prefixEnd_2946928 336264559598433636521629 := by
  unfold tailWord_2946928
  simp only [CollatzResearch.WordTrace]
  refine ⟨53741647133895313039064719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71655529511860417385419625 53741647133895313039064719)
  ·
    refine ⟨80612470700842969558597079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53741647133895313039064719 80612470700842969558597079)
    ·
      refine ⟨120918706051264454337895619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80612470700842969558597079 120918706051264454337895619)
      ·
        refine ⟨181378059076896681506843429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120918706051264454337895619 181378059076896681506843429)
        ·
          refine ⟨34008386076918127782533143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181378059076896681506843429 34008386076918127782533143)
          ·
            refine ⟨51012579115377191673799715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34008386076918127782533143 51012579115377191673799715)
            ·
              refine ⟨76518868673065787510699573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51012579115377191673799715 76518868673065787510699573)
              ·
                refine ⟨7173643938099917579128085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76518868673065787510699573 7173643938099917579128085)
                ·
                  refine ⟨336264559598433636521629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7173643938099917579128085 336264559598433636521629)
                  ·
                    rfl

theorem cell22_2946928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_2946928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946928 prefixEnd_2946928 := by exact prefixLift 2946928
  have htrace : WordTrace (prefixWord ++ tailWord_2946928) baseStart_2946928 baseEnd_2946928 := by
    simpa [prefixWord, tailWord_2946928, baseEnd_2946928] using wordTrace_append hprefix tailTrace_2946928
  have hstable : (prefixWord ++ tailWord_2946928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946928).length < 2 ^ (prefixWord ++ tailWord_2946928).sum := by decide
  have hdescent : baseEnd_2946928 < baseStart_2946928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946964 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2946964 : Nat := 118140960795 + 2946964 * 2 ^ 59
def prefixEnd_2946964 : Nat := 4983230072969 + 3 ^ 40 * 2946964 * 2
def baseEnd_2946964 : Nat := 1008806002331008815664777

theorem tailTrace_2946964 : CollatzResearch.WordTrace tailWord_2946964 prefixEnd_2946964 1008806002331008815664777 := by
  unfold tailWord_2946964
  simp only [CollatzResearch.WordTrace]
  refine ⟨53742303647830102113219973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71656404863773469484293297 53742303647830102113219973)
  ·
    refine ⟨10076681933968144146228745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53742303647830102113219973 10076681933968144146228745)
    ·
      refine ⟨7557511450476108109671559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10076681933968144146228745 7557511450476108109671559)
      ·
        refine ⟨11336267175714162164507339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7557511450476108109671559 11336267175714162164507339)
        ·
          refine ⟨17004400763571243246761009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11336267175714162164507339 17004400763571243246761009)
          ·
            refine ⟨12753300572678432435070757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17004400763571243246761009 12753300572678432435070757)
            ·
              refine ⟨2391243857377206081575767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12753300572678432435070757 2391243857377206081575767)
              ·
                refine ⟨3586865786065809122363651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391243857377206081575767 3586865786065809122363651)
                ·
                  refine ⟨5380298679098713683545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586865786065809122363651 5380298679098713683545477)
                  ·
                    refine ⟨1008806002331008815664777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5380298679098713683545477 1008806002331008815664777)
                    ·
                      rfl

theorem cell22_2946964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2946964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946964 prefixEnd_2946964 := by exact prefixLift 2946964
  have htrace : WordTrace (prefixWord ++ tailWord_2946964) baseStart_2946964 baseEnd_2946964 := by
    simpa [prefixWord, tailWord_2946964, baseEnd_2946964] using wordTrace_append hprefix tailTrace_2946964
  have hstable : (prefixWord ++ tailWord_2946964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946964).length < 2 ^ (prefixWord ++ tailWord_2946964).sum := by decide
  have hdescent : baseEnd_2946964 < baseStart_2946964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2946988 : Nat := 118140960795 + 2946988 * 2 ^ 59
def prefixEnd_2946988 : Nat := 4983230072969 + 3 ^ 40 * 2946988 * 2
def baseEnd_2946988 : Nat := 1008814218021480753064703

theorem tailTrace_2946988 : CollatzResearch.WordTrace tailWord_2946988 prefixEnd_2946988 1008814218021480753064703 := by
  unfold tailWord_2946988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53742741323786628162656809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71656988431715504216875745 53742741323786628162656809)
  ·
    refine ⟨40307055992839971121992607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53742741323786628162656809 40307055992839971121992607)
    ·
      refine ⟨60460583989259956682988911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40307055992839971121992607 60460583989259956682988911)
      ·
        refine ⟨90690875983889935024483367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60460583989259956682988911 90690875983889935024483367)
        ·
          refine ⟨136036313975834902536725051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90690875983889935024483367 136036313975834902536725051)
          ·
            refine ⟨204054470963752353805087577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136036313975834902536725051 204054470963752353805087577)
            ·
              refine ⟨153040853222814265353815683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204054470963752353805087577 153040853222814265353815683)
              ·
                refine ⟨229561279834221398030723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153040853222814265353815683 229561279834221398030723525)
                ·
                  refine ⟨43042739968916512130760661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229561279834221398030723525 43042739968916512130760661)
                  ·
                    refine ⟨1008814218021480753064703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43042739968916512130760661 1008814218021480753064703)
                    ·
                      rfl

theorem cell22_2946988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2946988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2946988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2946988 prefixEnd_2946988 := by exact prefixLift 2946988
  have htrace : WordTrace (prefixWord ++ tailWord_2946988) baseStart_2946988 baseEnd_2946988 := by
    simpa [prefixWord, tailWord_2946988, baseEnd_2946988] using wordTrace_append hprefix tailTrace_2946988
  have hstable : (prefixWord ++ tailWord_2946988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946988).length < 2 ^ (prefixWord ++ tailWord_2946988).sum := by decide
  have hdescent : baseEnd_2946988 < baseStart_2946988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_2947003 : Nat := 118140960795 + 2947003 * 2 ^ 59
def prefixEnd_2947003 : Nat := 4983230072969 + 3 ^ 40 * 2947003 * 2
def baseEnd_2947003 : Nat := 1008819352828025713939657

theorem tailTrace_2947003 : CollatzResearch.WordTrace tailWord_2947003 prefixEnd_2947003 1008819352828025713939657 := by
  unfold tailWord_2947003
  simp only [CollatzResearch.WordTrace]
  refine ⟨107486029742518913887109663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71657353161679275924739775 107486029742518913887109663)
  ·
    refine ⟨161229044613778370830664495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107486029742518913887109663 161229044613778370830664495)
    ·
      refine ⟨241843566920667556245996743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161229044613778370830664495 241843566920667556245996743)
      ·
        refine ⟨362765350381001334368995115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241843566920667556245996743 362765350381001334368995115)
        ·
          refine ⟨544148025571502001553492673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362765350381001334368995115 544148025571502001553492673)
          ·
            refine ⟨408111019178626501165119505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544148025571502001553492673 408111019178626501165119505)
            ·
              refine ⟨306083264383969875873839629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408111019178626501165119505 306083264383969875873839629)
              ·
                refine ⟨114781224143988703452689861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306083264383969875873839629 114781224143988703452689861)
                ·
                  refine ⟨21521479526997881897379349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114781224143988703452689861 21521479526997881897379349)
                  ·
                    refine ⟨1008819352828025713939657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21521479526997881897379349 1008819352828025713939657)
                    ·
                      rfl

theorem cell22_2947003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_2947003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947003 prefixEnd_2947003 := by exact prefixLift 2947003
  have htrace : WordTrace (prefixWord ++ tailWord_2947003) baseStart_2947003 baseEnd_2947003 := by
    simpa [prefixWord, tailWord_2947003, baseEnd_2947003] using wordTrace_append hprefix tailTrace_2947003
  have hstable : (prefixWord ++ tailWord_2947003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947003).length < 2 ^ (prefixWord ++ tailWord_2947003).sum := by decide
  have hdescent : baseEnd_2947003 < baseStart_2947003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947039 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 3, 3]
def baseStart_2947039 : Nat := 118140960795 + 2947039 * 2 ^ 59
def prefixEnd_2947039 : Nat := 4983230072969 + 3 ^ 40 * 2947039 * 2
def baseEnd_2947039 : Nat := 1008831676363733620039547

theorem tailTrace_2947039 : CollatzResearch.WordTrace tailWord_2947039 prefixEnd_2947039 1008831676363733620039547 := by
  unfold tailWord_2947039
  simp only [CollatzResearch.WordTrace]
  refine ⟨107487342770388492035420171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71658228513592328023613447 107487342770388492035420171)
  ·
    refine ⟨161231014155582738053130257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107487342770388492035420171 161231014155582738053130257)
    ·
      refine ⟨120923260616687053539847693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161231014155582738053130257 120923260616687053539847693)
      ·
        refine ⟨45346222731257645077442885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120923260616687053539847693 45346222731257645077442885)
        ·
          refine ⟨8502416762110808452020541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45346222731257645077442885 8502416762110808452020541)
          ·
            refine ⟨3188406285791553169507703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8502416762110808452020541 3188406285791553169507703)
            ·
              refine ⟨4782609428687329754261555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188406285791553169507703 4782609428687329754261555)
              ·
                refine ⟨7173914143030994631392333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782609428687329754261555 7173914143030994631392333)
                ·
                  refine ⟨2690217803636622986772125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7173914143030994631392333 2690217803636622986772125)
                  ·
                    refine ⟨1008831676363733620039547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690217803636622986772125 1008831676363733620039547)
                    ·
                      rfl

theorem cell22_2947039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_2947039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947039 prefixEnd_2947039 := by exact prefixLift 2947039
  have htrace : WordTrace (prefixWord ++ tailWord_2947039) baseStart_2947039 baseEnd_2947039 := by
    simpa [prefixWord, tailWord_2947039, baseEnd_2947039] using wordTrace_append hprefix tailTrace_2947039
  have hstable : (prefixWord ++ tailWord_2947039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947039).length < 2 ^ (prefixWord ++ tailWord_2947039).sum := by decide
  have hdescent : baseEnd_2947039 < baseStart_2947039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947050 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2947050 : Nat := 118140960795 + 2947050 * 2 ^ 59
def prefixEnd_2947050 : Nat := 4983230072969 + 3 ^ 40 * 2947050 * 2
def baseEnd_2947050 : Nat := 1008835441888533258014513

theorem tailTrace_2947050 : CollatzResearch.WordTrace tailWord_2947050 prefixEnd_2947050 1008835441888533258014513 := by
  unfold tailWord_2947050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871935993337160228517651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71658495982232427276047069 26871935993337160228517651)
  ·
    refine ⟨40307903990005740342776477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26871935993337160228517651 40307903990005740342776477)
    ·
      refine ⟨15115463996252152628541179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40307903990005740342776477 15115463996252152628541179)
      ·
        refine ⟨22673195994378228942811769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115463996252152628541179 22673195994378228942811769)
        ·
          refine ⟨17004896995783671707108827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22673195994378228942811769 17004896995783671707108827)
          ·
            refine ⟨25507345493675507560663241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17004896995783671707108827 25507345493675507560663241)
            ·
              refine ⟨19130509120256630670497431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25507345493675507560663241 19130509120256630670497431)
              ·
                refine ⟨28695763680384946005746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19130509120256630670497431 28695763680384946005746147)
                ·
                  refine ⟨43043645520577419008619221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28695763680384946005746147 43043645520577419008619221)
                  ·
                    refine ⟨1008835441888533258014513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43043645520577419008619221 1008835441888533258014513)
                    ·
                      rfl

theorem cell22_2947050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2947050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947050 prefixEnd_2947050 := by exact prefixLift 2947050
  have htrace : WordTrace (prefixWord ++ tailWord_2947050) baseStart_2947050 baseEnd_2947050 := by
    simpa [prefixWord, tailWord_2947050, baseEnd_2947050] using wordTrace_append hprefix tailTrace_2947050
  have hstable : (prefixWord ++ tailWord_2947050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947050).length < 2 ^ (prefixWord ++ tailWord_2947050).sum := by decide
  have hdescent : baseEnd_2947050 < baseStart_2947050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947125 : List Nat := [1, 3, 3, 1, 1, 1, 2, 10]
def baseStart_2947125 : Nat := 118140960795 + 2947125 * 2 ^ 59
def prefixEnd_2947125 : Nat := 4983230072969 + 3 ^ 40 * 2947125 * 2
def baseEnd_2947125 : Nat := 112095679546806451376587

theorem tailTrace_2947125 : CollatzResearch.WordTrace tailWord_2947125 prefixEnd_2947125 112095679546806451376587 := by
  unfold tailWord_2947125
  simp only [CollatzResearch.WordTrace]
  refine ⟨107490479448076928723050829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71660319632051285815367219 107490479448076928723050829)
  ·
    refine ⟨40308929793028848271144061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107490479448076928723050829 40308929793028848271144061)
    ·
      refine ⟨15115848672385818101679023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40308929793028848271144061 15115848672385818101679023)
      ·
        refine ⟨22673773008578727152518535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115848672385818101679023 22673773008578727152518535)
        ·
          refine ⟨34010659512868090728777803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22673773008578727152518535 34010659512868090728777803)
          ·
            refine ⟨51015989269302136093166705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34010659512868090728777803 51015989269302136093166705)
            ·
              refine ⟨38261991951976602069875029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51015989269302136093166705 38261991951976602069875029)
              ·
                refine ⟨112095679546806451376587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38261991951976602069875029 112095679546806451376587)
                ·
                  rfl

theorem cell22_2947125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 10].length) (baseStart_2947125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947125 prefixEnd_2947125 := by exact prefixLift 2947125
  have htrace : WordTrace (prefixWord ++ tailWord_2947125) baseStart_2947125 baseEnd_2947125 := by
    simpa [prefixWord, tailWord_2947125, baseEnd_2947125] using wordTrace_append hprefix tailTrace_2947125
  have hstable : (prefixWord ++ tailWord_2947125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947125).length < 2 ^ (prefixWord ++ tailWord_2947125).sum := by decide
  have hdescent : baseEnd_2947125 < baseStart_2947125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947127 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_2947127 : Nat := 118140960795 + 2947127 * 2 ^ 59
def prefixEnd_2947127 : Nat := 4983230072969 + 3 ^ 40 * 2947127 * 2
def baseEnd_2947127 : Nat := 1008861800562130723839277

theorem tailTrace_2947127 : CollatzResearch.WordTrace tailWord_2947127 prefixEnd_2947127 1008861800562130723839277 := by
  unfold tailWord_2947127
  simp only [CollatzResearch.WordTrace]
  refine ⟨107490552394069683064623635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71660368262713122043082423 107490552394069683064623635)
  ·
    refine ⟨161235828591104524596935453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107490552394069683064623635 161235828591104524596935453)
    ·
      refine ⟨60463435721664196723850795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161235828591104524596935453 60463435721664196723850795)
      ·
        refine ⟨90695153582496295085776193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60463435721664196723850795 90695153582496295085776193)
        ·
          refine ⟨68021365186872221314332145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90695153582496295085776193 68021365186872221314332145)
          ·
            refine ⟨51016023890154165985749109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68021365186872221314332145 51016023890154165985749109)
            ·
              refine ⟨4782752239701953061163979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51016023890154165985749109 4782752239701953061163979)
              ·
                refine ⟨7174128359552929591745969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782752239701953061163979 7174128359552929591745969)
                ·
                  refine ⟨5380596269664697193809477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174128359552929591745969 5380596269664697193809477)
                  ·
                    refine ⟨1008861800562130723839277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5380596269664697193809477 1008861800562130723839277)
                    ·
                      rfl

theorem cell22_2947127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_2947127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947127 prefixEnd_2947127 := by exact prefixLift 2947127
  have htrace : WordTrace (prefixWord ++ tailWord_2947127) baseStart_2947127 baseEnd_2947127 := by
    simpa [prefixWord, tailWord_2947127, baseEnd_2947127] using wordTrace_append hprefix tailTrace_2947127
  have hstable : (prefixWord ++ tailWord_2947127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947127).length < 2 ^ (prefixWord ++ tailWord_2947127).sum := by decide
  have hdescent : baseEnd_2947127 < baseStart_2947127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947191 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 1, 3]
def baseStart_2947191 : Nat := 118140960795 + 2947191 * 2 ^ 59
def prefixEnd_2947191 : Nat := 4983230072969 + 3 ^ 40 * 2947191 * 2
def baseEnd_2947191 : Nat := 1008883709070055890239081

theorem tailTrace_2947191 : CollatzResearch.WordTrace tailWord_2947191 prefixEnd_2947191 1008883709070055890239081 := by
  unfold tailWord_2947191
  simp only [CollatzResearch.WordTrace]
  refine ⟨107492886665837821994953427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71661924443891881329968951 107492886665837821994953427)
  ·
    refine ⟨161239329998756732992430141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107492886665837821994953427 161239329998756732992430141)
    ·
      refine ⟨60464748749533774872161303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161239329998756732992430141 60464748749533774872161303)
      ·
        refine ⟨90697123124300662308241955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60464748749533774872161303 90697123124300662308241955)
        ·
          refine ⟨136045684686450993462362933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90697123124300662308241955 136045684686450993462362933)
          ·
            refine ⟨12754282939354780637096525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136045684686450993462362933 12754282939354780637096525)
            ·
              refine ⟨4782856102258042738911197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12754282939354780637096525 4782856102258042738911197)
              ·
                refine ⟨1793571038346766027091699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4782856102258042738911197 1793571038346766027091699)
                ·
                  refine ⟨2690356557520149040637549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793571038346766027091699 2690356557520149040637549)
                  ·
                    refine ⟨1008883709070055890239081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690356557520149040637549 1008883709070055890239081)
                    ·
                      rfl

theorem cell22_2947191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_2947191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947191 prefixEnd_2947191 := by exact prefixLift 2947191
  have htrace : WordTrace (prefixWord ++ tailWord_2947191) baseStart_2947191 baseEnd_2947191 := by
    simpa [prefixWord, tailWord_2947191, baseEnd_2947191] using wordTrace_append hprefix tailTrace_2947191
  have hstable : (prefixWord ++ tailWord_2947191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947191).length < 2 ^ (prefixWord ++ tailWord_2947191).sum := by decide
  have hdescent : baseEnd_2947191 < baseStart_2947191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947360 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_2947360 : Nat := 118140960795 + 2947360 * 2 ^ 59
def prefixEnd_2947360 : Nat := 4983230072969 + 3 ^ 40 * 2947360 * 2
def baseEnd_2947360 : Nat := 1008941561223795782763563

theorem tailTrace_2947360 : CollatzResearch.WordTrace tailWord_2947360 prefixEnd_2947360 1008941561223795782763563 := by
  unfold tailWord_2947360
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749525301112781928927767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71666033734817042571903689 53749525301112781928927767)
  ·
    refine ⟨80624287951669172893391651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53749525301112781928927767 80624287951669172893391651)
    ·
      refine ⟨120936431927503759340087477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80624287951669172893391651 120936431927503759340087477)
      ·
        refine ⟨11337790493203477438133201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120936431927503759340087477 11337790493203477438133201)
        ·
          refine ⟨8503342869902608078599901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337790493203477438133201 8503342869902608078599901)
          ·
            refine ⟨3188753576213478029474963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8503342869902608078599901 3188753576213478029474963)
            ·
              refine ⟨4783130364320217044212445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188753576213478029474963 4783130364320217044212445)
              ·
                refine ⟨1793673886620081391579667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4783130364320217044212445 1793673886620081391579667)
                ·
                  refine ⟨2690510829930122087369501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793673886620081391579667 2690510829930122087369501)
                  ·
                    refine ⟨1008941561223795782763563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690510829930122087369501 1008941561223795782763563)
                    ·
                      rfl

theorem cell22_2947360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_2947360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947360 prefixEnd_2947360 := by exact prefixLift 2947360
  have htrace : WordTrace (prefixWord ++ tailWord_2947360) baseStart_2947360 baseEnd_2947360 := by
    simpa [prefixWord, tailWord_2947360, baseEnd_2947360] using wordTrace_append hprefix tailTrace_2947360
  have hstable : (prefixWord ++ tailWord_2947360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947360).length < 2 ^ (prefixWord ++ tailWord_2947360).sum := by decide
  have hdescent : baseEnd_2947360 < baseStart_2947360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947384 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_2947384 : Nat := 118140960795 + 2947384 * 2 ^ 59
def prefixEnd_2947384 : Nat := 4983230072969 + 3 ^ 40 * 2947384 * 2
def baseEnd_2947384 : Nat := 336316592304755906721163

theorem tailTrace_2947384 : CollatzResearch.WordTrace tailWord_2947384 prefixEnd_2947384 336316592304755906721163 := by
  unfold tailWord_2947384
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749962977069307978364603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71666617302759077304486137 53749962977069307978364603)
  ·
    refine ⟨80624944465603961967546905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53749962977069307978364603 80624944465603961967546905)
    ·
      refine ⟨60468708349202971475660179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80624944465603961967546905 60468708349202971475660179)
      ·
        refine ⟨90703062523804457213490269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60468708349202971475660179 90703062523804457213490269)
        ·
          refine ⟨34013648446426671455058851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90703062523804457213490269 34013648446426671455058851)
          ·
            refine ⟨51020472669640007182588277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34013648446426671455058851 51020472669640007182588277)
            ·
              refine ⟨4783169312778750673367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51020472669640007182588277 4783169312778750673367651)
              ·
                refine ⟨7174753969168126010051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783169312778750673367651 7174753969168126010051477)
                ·
                  refine ⟨336316592304755906721163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7174753969168126010051477 336316592304755906721163)
                  ·
                    rfl

theorem cell22_2947384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_2947384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947384 prefixEnd_2947384 := by exact prefixLift 2947384
  have htrace : WordTrace (prefixWord ++ tailWord_2947384) baseStart_2947384 baseEnd_2947384 := by
    simpa [prefixWord, tailWord_2947384, baseEnd_2947384] using wordTrace_append hprefix tailTrace_2947384
  have hstable : (prefixWord ++ tailWord_2947384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947384).length < 2 ^ (prefixWord ++ tailWord_2947384).sum := by decide
  have hdescent : baseEnd_2947384 < baseStart_2947384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947399 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2947399 : Nat := 118140960795 + 2947399 * 2 ^ 59
def prefixEnd_2947399 : Nat := 4983230072969 + 3 ^ 40 * 2947399 * 2
def baseEnd_2947399 : Nat := 1008954911720812681038443

theorem tailTrace_2947399 : CollatzResearch.WordTrace tailWord_2947399 prefixEnd_2947399 1008954911720812681038443 := by
  unfold tailWord_2947399
  simp only [CollatzResearch.WordTrace]
  refine ⟨107500473049084273518525251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71666982032722849012350167 107500473049084273518525251)
  ·
    refine ⟨161250709573626410277787877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107500473049084273518525251 161250709573626410277787877)
    ·
      refine ⟨30234508045054951927085227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161250709573626410277787877 30234508045054951927085227)
      ·
        refine ⟨45351762067582427890627841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30234508045054951927085227 45351762067582427890627841)
        ·
          refine ⟨34013821550686820917970881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45351762067582427890627841 34013821550686820917970881)
          ·
            refine ⟨25510366163015115688478161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34013821550686820917970881 25510366163015115688478161)
            ·
              refine ⟨19132774622261336766358621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25510366163015115688478161 19132774622261336766358621)
              ·
                refine ⟨7174790483348001287384483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19132774622261336766358621 7174790483348001287384483)
                ·
                  refine ⟨10762185725022001931076725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174790483348001287384483 10762185725022001931076725)
                  ·
                    refine ⟨1008954911720812681038443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10762185725022001931076725 1008954911720812681038443)
                    ·
                      rfl

theorem cell22_2947399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2947399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947399 prefixEnd_2947399 := by exact prefixLift 2947399
  have htrace : WordTrace (prefixWord ++ tailWord_2947399) baseStart_2947399 baseEnd_2947399 := by
    simpa [prefixWord, tailWord_2947399, baseEnd_2947399] using wordTrace_append hprefix tailTrace_2947399
  have hstable : (prefixWord ++ tailWord_2947399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947399).length < 2 ^ (prefixWord ++ tailWord_2947399).sum := by decide
  have hdescent : baseEnd_2947399 < baseStart_2947399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947431 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2947431 : Nat := 118140960795 + 2947431 * 2 ^ 59
def prefixEnd_2947431 : Nat := 4983230072969 + 3 ^ 40 * 2947431 * 2
def baseEnd_2947431 : Nat := 1008965865974775264238345

theorem tailTrace_2947431 : CollatzResearch.WordTrace tailWord_2947431 prefixEnd_2947431 1008965865974775264238345 := by
  unfold tailWord_2947431
  simp only [CollatzResearch.WordTrace]
  refine ⟨107501640184968342983690147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71667760123312228655793431 107501640184968342983690147)
  ·
    refine ⟨161252460277452514475535221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107501640184968342983690147 161252460277452514475535221)
    ·
      refine ⟨15117418151011173232081427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161252460277452514475535221 15117418151011173232081427)
      ·
        refine ⟨22676127226516759848122141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15117418151011173232081427 22676127226516759848122141)
        ·
          refine ⟨8503547709943784943045803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22676127226516759848122141 8503547709943784943045803)
          ·
            refine ⟨12755321564915677414568705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503547709943784943045803 12755321564915677414568705)
            ·
              refine ⟨9566491173686758060926529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12755321564915677414568705 9566491173686758060926529)
              ·
                refine ⟨7174868380265068545694897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9566491173686758060926529 7174868380265068545694897)
                ·
                  refine ⟨5381151285198801409271173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174868380265068545694897 5381151285198801409271173)
                  ·
                    refine ⟨1008965865974775264238345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381151285198801409271173 1008965865974775264238345)
                    ·
                      rfl

theorem cell22_2947431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2947431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947431 prefixEnd_2947431 := by exact prefixLift 2947431
  have htrace : WordTrace (prefixWord ++ tailWord_2947431) baseStart_2947431 baseEnd_2947431 := by
    simpa [prefixWord, tailWord_2947431, baseEnd_2947431] using wordTrace_append hprefix tailTrace_2947431
  have hstable : (prefixWord ++ tailWord_2947431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947431).length < 2 ^ (prefixWord ++ tailWord_2947431).sum := by decide
  have hdescent : baseEnd_2947431 < baseStart_2947431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947491 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 5]
def baseStart_2947491 : Nat := 118140960795 + 2947491 * 2 ^ 59
def prefixEnd_2947491 : Nat := 4983230072969 + 3 ^ 40 * 2947491 * 2
def baseEnd_2947491 : Nat := 336328801733651702579387

theorem tailTrace_2947491 : CollatzResearch.WordTrace tailWord_2947491 prefixEnd_2947491 336328801733651702579387 := by
  unfold tailWord_2947491
  simp only [CollatzResearch.WordTrace]
  refine ⟨107503828564750973230874327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71669219043167315487249551 107503828564750973230874327)
  ·
    refine ⟨161255742847126459846311491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107503828564750973230874327 161255742847126459846311491)
    ·
      refine ⟨241883614270689689769467237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161255742847126459846311491 241883614270689689769467237)
      ·
        refine ⟨45353177675754316831775107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241883614270689689769467237 45353177675754316831775107)
        ·
          refine ⟨68029766513631475247662661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45353177675754316831775107 68029766513631475247662661)
          ·
            refine ⟨12755581221305901608936749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68029766513631475247662661 12755581221305901608936749)
            ·
              refine ⟨4783342957989713103351281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12755581221305901608936749 4783342957989713103351281)
              ·
                refine ⟨3587507218492284827513461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783342957989713103351281 3587507218492284827513461)
                ·
                  refine ⟨336328801733651702579387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587507218492284827513461 336328801733651702579387)
                  ·
                    rfl

theorem cell22_2947491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].length) (baseStart_2947491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947491 prefixEnd_2947491 := by exact prefixLift 2947491
  have htrace : WordTrace (prefixWord ++ tailWord_2947491) baseStart_2947491 baseEnd_2947491 := by
    simpa [prefixWord, tailWord_2947491, baseEnd_2947491] using wordTrace_append hprefix tailTrace_2947491
  have hstable : (prefixWord ++ tailWord_2947491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947491).length < 2 ^ (prefixWord ++ tailWord_2947491).sum := by decide
  have hdescent : baseEnd_2947491 < baseStart_2947491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947495 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2947495 : Nat := 118140960795 + 2947495 * 2 ^ 59
def prefixEnd_2947495 : Nat := 4983230072969 + 3 ^ 40 * 2947495 * 2
def baseEnd_2947495 : Nat := 1008987774482700430638149

theorem tailTrace_2947495 : CollatzResearch.WordTrace tailWord_2947495 prefixEnd_2947495 1008987774482700430638149 := by
  unfold tailWord_2947495
  simp only [CollatzResearch.WordTrace]
  refine ⟨107503974456736481914019939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71669316304490987942679959 107503974456736481914019939)
  ·
    refine ⟨161255961685104722871029909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107503974456736481914019939 161255961685104722871029909)
    ·
      refine ⟨7558873203989283884579527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161255961685104722871029909 7558873203989283884579527)
      ·
        refine ⟨11338309805983925826869291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558873203989283884579527 11338309805983925826869291)
        ·
          refine ⟨17007464708975888740303937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11338309805983925826869291 17007464708975888740303937)
          ·
            refine ⟨12755598531731916555227953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17007464708975888740303937 12755598531731916555227953)
            ·
              refine ⟨9566698898798937416420965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12755598531731916555227953 9566698898798937416420965)
              ·
                refine ⟨1793756043524800765578931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9566698898798937416420965 1793756043524800765578931)
                ·
                  refine ⟨2690634065287201148368397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793756043524800765578931 2690634065287201148368397)
                  ·
                    refine ⟨1008987774482700430638149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690634065287201148368397 1008987774482700430638149)
                    ·
                      rfl

theorem cell22_2947495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2947495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947495 prefixEnd_2947495 := by exact prefixLift 2947495
  have htrace : WordTrace (prefixWord ++ tailWord_2947495) baseStart_2947495 baseEnd_2947495 := by
    simpa [prefixWord, tailWord_2947495, baseEnd_2947495] using wordTrace_append hprefix tailTrace_2947495
  have hstable : (prefixWord ++ tailWord_2947495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947495).length < 2 ^ (prefixWord ++ tailWord_2947495).sum := by decide
  have hdescent : baseEnd_2947495 < baseStart_2947495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947568 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_2947568 : Nat := 118140960795 + 2947568 * 2 ^ 59
def prefixEnd_2947568 : Nat := 4983230072969 + 3 ^ 40 * 2947568 * 2
def baseEnd_2947568 : Nat := 1009012763874552573562925

theorem tailTrace_2947568 : CollatzResearch.WordTrace tailWord_2947568 prefixEnd_2947568 1009012763874552573562925 := by
  unfold tailWord_2947568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53753318492736007690713679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71671091323648010254284905 53753318492736007690713679)
  ·
    refine ⟨80629977739104011536070519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53753318492736007690713679 80629977739104011536070519)
    ·
      refine ⟨120944966608656017304105779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80629977739104011536070519 120944966608656017304105779)
      ·
        refine ⟨181417449912984025956158669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120944966608656017304105779 181417449912984025956158669)
        ·
          refine ⟨68031543717369009733559501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181417449912984025956158669 68031543717369009733559501)
          ·
            refine ⟨25511828894013378650084813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68031543717369009733559501 25511828894013378650084813)
            ·
              refine ⟨9566935835255016993781805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25511828894013378650084813 9566935835255016993781805)
              ·
                refine ⟨3587600938220631372668177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9566935835255016993781805 3587600938220631372668177)
                ·
                  refine ⟨2690700703665473529501133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3587600938220631372668177 2690700703665473529501133)
                  ·
                    refine ⟨1009012763874552573562925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690700703665473529501133 1009012763874552573562925)
                    ·
                      rfl

theorem cell22_2947568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_2947568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947568 prefixEnd_2947568 := by exact prefixLift 2947568
  have htrace : WordTrace (prefixWord ++ tailWord_2947568) baseStart_2947568 baseEnd_2947568 := by
    simpa [prefixWord, tailWord_2947568, baseEnd_2947568] using wordTrace_append hprefix tailTrace_2947568
  have hstable : (prefixWord ++ tailWord_2947568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947568).length < 2 ^ (prefixWord ++ tailWord_2947568).sum := by decide
  have hdescent : baseEnd_2947568 < baseStart_2947568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947604 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2947604 : Nat := 118140960795 + 2947604 * 2 ^ 59
def prefixEnd_2947604 : Nat := 4983230072969 + 3 ^ 40 * 2947604 * 2
def baseEnd_2947604 : Nat := 336341695803420159887605

theorem tailTrace_2947604 : CollatzResearch.WordTrace tailWord_2947604 prefixEnd_2947604 336341695803420159887605 := by
  unfold tailWord_2947604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53753975006670796764868933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71671966675561062353158577 53753975006670796764868933)
  ·
    refine ⟨10078870313750774393412925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53753975006670796764868933 10078870313750774393412925)
    ·
      refine ⟨3779576367656540397529847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10078870313750774393412925 3779576367656540397529847)
      ·
        refine ⟨5669364551484810596294771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779576367656540397529847 5669364551484810596294771)
        ·
          refine ⟨8504046827227215894442157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669364551484810596294771 8504046827227215894442157)
          ·
            refine ⟨3189017560210205960415809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8504046827227215894442157 3189017560210205960415809)
            ·
              refine ⟨2391763170157654470311857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189017560210205960415809 2391763170157654470311857)
              ·
                refine ⟨1793822377618240852733893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391763170157654470311857 1793822377618240852733893)
                ·
                  refine ⟨336341695803420159887605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793822377618240852733893 336341695803420159887605)
                  ·
                    rfl

theorem cell22_2947604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2947604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947604 prefixEnd_2947604 := by exact prefixLift 2947604
  have htrace : WordTrace (prefixWord ++ tailWord_2947604) baseStart_2947604 baseEnd_2947604 := by
    simpa [prefixWord, tailWord_2947604, baseEnd_2947604] using wordTrace_append hprefix tailTrace_2947604
  have hstable : (prefixWord ++ tailWord_2947604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947604).length < 2 ^ (prefixWord ++ tailWord_2947604).sum := by decide
  have hdescent : baseEnd_2947604 < baseStart_2947604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947641 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_2947641 : Nat := 118140960795 + 2947641 * 2 ^ 59
def prefixEnd_2947641 : Nat := 4983230072969 + 3 ^ 40 * 2947641 * 2
def baseEnd_2947641 : Nat := 1009037753266404716487701

theorem tailTrace_2947641 : CollatzResearch.WordTrace tailWord_2947641 prefixEnd_2947641 1009037753266404716487701 := by
  unfold tailWord_2947641
  simp only [CollatzResearch.WordTrace]
  refine ⟨107509299514207548848834777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71672866342805032565889851 107509299514207548848834777)
  ·
    refine ⟨80631974635655661636626083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107509299514207548848834777 80631974635655661636626083)
    ·
      refine ⟨120947961953483492454939125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80631974635655661636626083 120947961953483492454939125)
      ·
        refine ⟨11338871433139077417650543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120947961953483492454939125 11338871433139077417650543)
        ·
          refine ⟨17008307149708616126475815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11338871433139077417650543 17008307149708616126475815)
          ·
            refine ⟨25512460724562924189713723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17008307149708616126475815 25512460724562924189713723)
            ·
              refine ⟨38268691086844386284570585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25512460724562924189713723 38268691086844386284570585)
              ·
                refine ⟨28701518315133289713427939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38268691086844386284570585 28701518315133289713427939)
                ·
                  refine ⟨43052277472699934570141909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28701518315133289713427939 43052277472699934570141909)
                  ·
                    refine ⟨1009037753266404716487701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43052277472699934570141909 1009037753266404716487701)
                    ·
                      rfl

theorem cell22_2947641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_2947641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947641 prefixEnd_2947641 := by exact prefixLift 2947641
  have htrace : WordTrace (prefixWord ++ tailWord_2947641) baseStart_2947641 baseEnd_2947641 := by
    simpa [prefixWord, tailWord_2947641, baseEnd_2947641] using wordTrace_append hprefix tailTrace_2947641
  have hstable : (prefixWord ++ tailWord_2947641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947641).length < 2 ^ (prefixWord ++ tailWord_2947641).sum := by decide
  have hdescent : baseEnd_2947641 < baseStart_2947641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947690 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2947690 : Nat := 118140960795 + 2947690 * 2 ^ 59
def prefixEnd_2947690 : Nat := 4983230072969 + 3 ^ 40 * 2947690 * 2
def baseEnd_2947690 : Nat := 1009054526967784922012551

theorem tailTrace_2947690 : CollatzResearch.WordTrace tailWord_2947690 prefixEnd_2947690 1009054526967784922012551 := by
  unfold tailWord_2947690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877771672757507554342131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71674057794020020144912349 26877771672757507554342131)
  ·
    refine ⟨40316657509136261331513197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26877771672757507554342131 40316657509136261331513197)
    ·
      refine ⟨15118746565926097999317449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40316657509136261331513197 15118746565926097999317449)
      ·
        refine ⟨11339059924444573499488087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15118746565926097999317449 11339059924444573499488087)
        ·
          refine ⟨17008589886666860249232131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11339059924444573499488087 17008589886666860249232131)
          ·
            refine ⟨25512884830000290373848197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17008589886666860249232131 25512884830000290373848197)
            ·
              refine ⟨4783665905625054445096537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25512884830000290373848197 4783665905625054445096537)
              ·
                refine ⟨3587749429218790833822403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783665905625054445096537 3587749429218790833822403)
                ·
                  refine ⟨5381624143828186250733605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587749429218790833822403 5381624143828186250733605)
                  ·
                    refine ⟨1009054526967784922012551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381624143828186250733605 1009054526967784922012551)
                    ·
                      rfl

theorem cell22_2947690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2947690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947690 prefixEnd_2947690 := by exact prefixLift 2947690
  have htrace : WordTrace (prefixWord ++ tailWord_2947690) baseStart_2947690 baseEnd_2947690 := by
    simpa [prefixWord, tailWord_2947690, baseEnd_2947690] using wordTrace_append hprefix tailTrace_2947690
  have hstable : (prefixWord ++ tailWord_2947690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947690).length < 2 ^ (prefixWord ++ tailWord_2947690).sum := by decide
  have hdescent : baseEnd_2947690 < baseStart_2947690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947703 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 4, 3]
def baseStart_2947703 : Nat := 118140960795 + 2947703 * 2 ^ 59
def prefixEnd_2947703 : Nat := 4983230072969 + 3 ^ 40 * 2947703 * 2
def baseEnd_2947703 : Nat := 1009058977133457221437511

theorem tailTrace_2947703 : CollatzResearch.WordTrace tailWord_2947703 prefixEnd_2947703 1009058977133457221437511 := by
  unfold tailWord_2947703
  simp only [CollatzResearch.WordTrace]
  refine ⟨107511560839982933437591763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71674373893321955625061175 107511560839982933437591763)
  ·
    refine ⟨161267341259974400156387645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107511560839982933437591763 161267341259974400156387645)
    ·
      refine ⟨60475252972490400058645367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161267341259974400156387645 60475252972490400058645367)
      ·
        refine ⟨90712879458735600087968051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60475252972490400058645367 90712879458735600087968051)
        ·
          refine ⟨136069319188103400131952077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90712879458735600087968051 136069319188103400131952077)
          ·
            refine ⟨51025994695538775049482029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136069319188103400131952077 51025994695538775049482029)
            ·
              refine ⟨19134748010827040643555761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51025994695538775049482029 19134748010827040643555761)
              ·
                refine ⟨14351061008120280482666821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19134748010827040643555761 14351061008120280482666821)
                ·
                  refine ⟨2690823939022552590500029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14351061008120280482666821 2690823939022552590500029)
                  ·
                    refine ⟨1009058977133457221437511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690823939022552590500029 1009058977133457221437511)
                    ·
                      rfl

theorem cell22_2947703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_2947703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947703 prefixEnd_2947703 := by exact prefixLift 2947703
  have htrace : WordTrace (prefixWord ++ tailWord_2947703) baseStart_2947703 baseEnd_2947703 := by
    simpa [prefixWord, tailWord_2947703, baseEnd_2947703] using wordTrace_append hprefix tailTrace_2947703
  have hstable : (prefixWord ++ tailWord_2947703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947703).length < 2 ^ (prefixWord ++ tailWord_2947703).sum := by decide
  have hdescent : baseEnd_2947703 < baseStart_2947703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947705 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 4]
def baseStart_2947705 : Nat := 118140960795 + 2947705 * 2 ^ 59
def prefixEnd_2947705 : Nat := 4983230072969 + 3 ^ 40 * 2947705 * 2
def baseEnd_2947705 : Nat := 336353220591443294295835

theorem tailTrace_2947705 : CollatzResearch.WordTrace tailWord_2947705 prefixEnd_2947705 336353220591443294295835 := by
  unfold tailWord_2947705
  simp only [CollatzResearch.WordTrace]
  refine ⟨107511633785975687779164569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71674422523983791852776379 107511633785975687779164569)
  ·
    refine ⟨80633725339481765834373427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107511633785975687779164569 80633725339481765834373427)
    ·
      refine ⟨120950588009222648751560141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80633725339481765834373427 120950588009222648751560141)
      ·
        refine ⟨45356470503458493281835053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120950588009222648751560141 45356470503458493281835053)
        ·
          refine ⟨17008676438796934980688145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45356470503458493281835053 17008676438796934980688145)
          ·
            refine ⟨12756507329097701235516109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17008676438796934980688145 12756507329097701235516109)
            ·
              refine ⟨4783690248411637963318541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12756507329097701235516109 4783690248411637963318541)
              ·
                refine ⟨1793883843154364236244453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4783690248411637963318541 1793883843154364236244453)
                ·
                  refine ⟨336353220591443294295835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793883843154364236244453 336353220591443294295835)
                  ·
                    rfl

theorem cell22_2947705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_2947705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947705 prefixEnd_2947705 := by exact prefixLift 2947705
  have htrace : WordTrace (prefixWord ++ tailWord_2947705) baseStart_2947705 baseEnd_2947705 := by
    simpa [prefixWord, tailWord_2947705, baseEnd_2947705] using wordTrace_append hprefix tailTrace_2947705
  have hstable : (prefixWord ++ tailWord_2947705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947705).length < 2 ^ (prefixWord ++ tailWord_2947705).sum := by decide
  have hdescent : baseEnd_2947705 < baseStart_2947705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947722 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_2947722 : Nat := 118140960795 + 2947722 * 2 ^ 59
def prefixEnd_2947722 : Nat := 4983230072969 + 3 ^ 40 * 2947722 * 2
def baseEnd_2947722 : Nat := 336355160407249168404151

theorem tailTrace_2947722 : CollatzResearch.WordTrace tailWord_2947722 prefixEnd_2947722 336355160407249168404151 := by
  unfold tailWord_2947722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26878063456728524920633355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71674835884609399788355613 26878063456728524920633355)
  ·
    refine ⟨40317095185092787380950033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26878063456728524920633355 40317095185092787380950033)
    ·
      refine ⟨30237821388819590535712525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40317095185092787380950033 30237821388819590535712525)
      ·
        refine ⟨11339183020807346450892197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30237821388819590535712525 11339183020807346450892197)
        ·
          refine ⟨2126096816401377459542287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11339183020807346450892197 2126096816401377459542287)
          ·
            refine ⟨3189145224602066189313431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126096816401377459542287 3189145224602066189313431)
            ·
              refine ⟨4783717836903099283970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189145224602066189313431 4783717836903099283970147)
              ·
                refine ⟨7175576755354648925955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783717836903099283970147 7175576755354648925955221)
                ·
                  refine ⟨336355160407249168404151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7175576755354648925955221 336355160407249168404151)
                  ·
                    rfl

theorem cell22_2947722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_2947722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947722 prefixEnd_2947722 := by exact prefixLift 2947722
  have htrace : WordTrace (prefixWord ++ tailWord_2947722) baseStart_2947722 baseEnd_2947722 := by
    simpa [prefixWord, tailWord_2947722, baseEnd_2947722] using wordTrace_append hprefix tailTrace_2947722
  have hstable : (prefixWord ++ tailWord_2947722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947722).length < 2 ^ (prefixWord ++ tailWord_2947722).sum := by decide
  have hdescent : baseEnd_2947722 < baseStart_2947722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947793 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_2947793 : Nat := 118140960795 + 2947793 * 2 ^ 59
def prefixEnd_2947793 : Nat := 4983230072969 + 3 ^ 40 * 2947793 * 2
def baseEnd_2947793 : Nat := 1009089785972726986687235

theorem tailTrace_2947793 : CollatzResearch.WordTrace tailWord_2947793 prefixEnd_2947793 1009089785972726986687235 := by
  unfold tailWord_2947793
  simp only [CollatzResearch.WordTrace]
  refine ⟨107514843409656878808368033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71676562273104585872245355 107514843409656878808368033)
  ·
    refine ⟨80636132557242659106276025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107514843409656878808368033 80636132557242659106276025)
    ·
      refine ⟨60477099417931994329707019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80636132557242659106276025 60477099417931994329707019)
      ·
        refine ⟨90715649126897991494560529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60477099417931994329707019 90715649126897991494560529)
        ·
          refine ⟨68036736845173493620920397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90715649126897991494560529 68036736845173493620920397)
          ·
            refine ⟨25513776316940060107845149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68036736845173493620920397 25513776316940060107845149)
            ·
              refine ⟨9567666118852522540441931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25513776316940060107845149 9567666118852522540441931)
              ·
                refine ⟨14351499178278783810662897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567666118852522540441931 14351499178278783810662897)
                ·
                  refine ⟨10763624383709087857997173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14351499178278783810662897 10763624383709087857997173)
                  ·
                    refine ⟨1009089785972726986687235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10763624383709087857997173 1009089785972726986687235)
                    ·
                      rfl

theorem cell22_2947793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_2947793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947793 prefixEnd_2947793 := by exact prefixLift 2947793
  have htrace : WordTrace (prefixWord ++ tailWord_2947793) baseStart_2947793 baseEnd_2947793 := by
    simpa [prefixWord, tailWord_2947793, baseEnd_2947793] using wordTrace_append hprefix tailTrace_2947793
  have hstable : (prefixWord ++ tailWord_2947793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947793).length < 2 ^ (prefixWord ++ tailWord_2947793).sum := by decide
  have hdescent : baseEnd_2947793 < baseStart_2947793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947825 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_2947825 : Nat := 118140960795 + 2947825 * 2 ^ 59
def prefixEnd_2947825 : Nat := 4983230072969 + 3 ^ 40 * 2947825 * 2
def baseEnd_2947825 : Nat := 1009100740226689569887137

theorem tailTrace_2947825 : CollatzResearch.WordTrace tailWord_2947825 prefixEnd_2947825 1009100740226689569887137 := by
  unfold tailWord_2947825
  simp only [CollatzResearch.WordTrace]
  refine ⟨107516010545540948273532929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71677340363693965515688619 107516010545540948273532929)
  ·
    refine ⟨80637007909155711205149697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107516010545540948273532929 80637007909155711205149697)
    ·
      refine ⟨60477755931866783403862273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80637007909155711205149697 60477755931866783403862273)
      ·
        refine ⟨45358316948900087552896705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60477755931866783403862273 45358316948900087552896705)
        ·
          refine ⟨34018737711675065664672529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45358316948900087552896705 34018737711675065664672529)
          ·
            refine ⟨25514053283756299248504397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34018737711675065664672529 25514053283756299248504397)
            ·
              refine ⟨9567769981408612218189149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25514053283756299248504397 9567769981408612218189149)
              ·
                refine ⟨3587913743028229581820931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9567769981408612218189149 3587913743028229581820931)
                ·
                  refine ⟨5381870614542344372731397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587913743028229581820931 5381870614542344372731397)
                  ·
                    refine ⟨1009100740226689569887137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5381870614542344372731397 1009100740226689569887137)
                    ·
                      rfl

theorem cell22_2947825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_2947825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947825 prefixEnd_2947825 := by exact prefixLift 2947825
  have htrace : WordTrace (prefixWord ++ tailWord_2947825) baseStart_2947825 baseEnd_2947825 := by
    simpa [prefixWord, tailWord_2947825, baseEnd_2947825] using wordTrace_append hprefix tailTrace_2947825
  have hstable : (prefixWord ++ tailWord_2947825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947825).length < 2 ^ (prefixWord ++ tailWord_2947825).sum := by decide
  have hdescent : baseEnd_2947825 < baseStart_2947825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947829 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 7]
def baseStart_2947829 : Nat := 118140960795 + 2947829 * 2 ^ 59
def prefixEnd_2947829 : Nat := 4983230072969 + 3 ^ 40 * 2947829 * 2
def baseEnd_2947829 : Nat := 336367369836144964262375

theorem tailTrace_2947829 : CollatzResearch.WordTrace tailWord_2947829 prefixEnd_2947829 336367369836144964262375 := by
  unfold tailWord_2947829
  simp only [CollatzResearch.WordTrace]
  refine ⟨107516156437526456956678541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71677437625017637971119027 107516156437526456956678541)
  ·
    refine ⟨40318558664072421358754453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107516156437526456956678541 40318558664072421358754453)
    ·
      refine ⟨1889932437378394751191615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40318558664072421358754453 1889932437378394751191615)
      ·
        refine ⟨2834898656067592126787423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889932437378394751191615 2834898656067592126787423)
        ·
          refine ⟨4252347984101388190181135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834898656067592126787423 4252347984101388190181135)
          ·
            refine ⟨6378521976152082285271703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252347984101388190181135 6378521976152082285271703)
            ·
              refine ⟨9567782964228123427907555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378521976152082285271703 9567782964228123427907555)
              ·
                refine ⟨14351674446342185141861333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567782964228123427907555 14351674446342185141861333)
                ·
                  refine ⟨336367369836144964262375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14351674446342185141861333 336367369836144964262375)
                  ·
                    rfl

theorem cell22_2947829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_2947829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947829 prefixEnd_2947829 := by exact prefixLift 2947829
  have htrace : WordTrace (prefixWord ++ tailWord_2947829) baseStart_2947829 baseEnd_2947829 := by
    simpa [prefixWord, tailWord_2947829, baseEnd_2947829] using wordTrace_append hprefix tailTrace_2947829
  have hstable : (prefixWord ++ tailWord_2947829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947829).length < 2 ^ (prefixWord ++ tailWord_2947829).sum := by decide
  have hdescent : baseEnd_2947829 < baseStart_2947829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947874 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2947874 : Nat := 118140960795 + 2947874 * 2 ^ 59
def prefixEnd_2947874 : Nat := 4983230072969 + 3 ^ 40 * 2947874 * 2
def baseEnd_2947874 : Nat := 336372504642689925137329

theorem tailTrace_2947874 : CollatzResearch.WordTrace tailWord_2947874 prefixEnd_2947874 336372504642689925137329 := by
  unfold tailWord_2947874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26879449430590857410516669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71678531814908953094711117 26879449430590857410516669)
  ·
    refine ⟨10079793536471571528943751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26879449430590857410516669 10079793536471571528943751)
    ·
      refine ⟨15119690304707357293415627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10079793536471571528943751 15119690304707357293415627)
      ·
        refine ⟨22679535457061035940123441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15119690304707357293415627 22679535457061035940123441)
        ·
          refine ⟨17009651592795776955092581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22679535457061035940123441 17009651592795776955092581)
          ·
            refine ⟨3189309673649208179079859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17009651592795776955092581 3189309673649208179079859)
            ·
              refine ⟨4783964510473812268619789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189309673649208179079859 4783964510473812268619789)
              ·
                refine ⟨1793986691427679600732421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4783964510473812268619789 1793986691427679600732421)
                ·
                  refine ⟨336372504642689925137329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793986691427679600732421 336372504642689925137329)
                  ·
                    rfl

theorem cell22_2947874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2947874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947874 prefixEnd_2947874 := by exact prefixLift 2947874
  have htrace : WordTrace (prefixWord ++ tailWord_2947874) baseStart_2947874 baseEnd_2947874 := by
    simpa [prefixWord, tailWord_2947874, baseEnd_2947874] using wordTrace_append hprefix tailTrace_2947874
  have hstable : (prefixWord ++ tailWord_2947874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947874).length < 2 ^ (prefixWord ++ tailWord_2947874).sum := by decide
  have hdescent : baseEnd_2947874 < baseStart_2947874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947902 : List Nat := [4, 2, 1, 2, 3, 1, 2, 7]
def baseStart_2947902 : Nat := 118140960795 + 2947902 * 2 ^ 59
def prefixEnd_2947902 : Nat := 4983230072969 + 3 ^ 40 * 2947902 * 2
def baseEnd_2947902 : Nat := 112125233211143003967989

theorem tailTrace_2947902 : CollatzResearch.WordTrace tailWord_2947902 prefixEnd_2947902 112125233211143003967989 := by
  unfold tailWord_2947902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439852370782748803010745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71679212644174660282723973 13439852370782748803010745)
  ·
    refine ⟨10079889278087061602258059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13439852370782748803010745 10079889278087061602258059)
    ·
      refine ⟨15119833917130592403387089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10079889278087061602258059 15119833917130592403387089)
      ·
        refine ⟨11339875437847944302540317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15119833917130592403387089 11339875437847944302540317)
        ·
          refine ⟨4252453289192979113452619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11339875437847944302540317 4252453289192979113452619)
          ·
            refine ⟨6378679933789468670178929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252453289192979113452619 6378679933789468670178929)
            ·
              refine ⟨4784009950342101502634197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6378679933789468670178929 4784009950342101502634197)
              ·
                refine ⟨112125233211143003967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4784009950342101502634197 112125233211143003967989)
                ·
                  rfl

theorem cell22_2947902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_2947902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947902 prefixEnd_2947902 := by exact prefixLift 2947902
  have htrace : WordTrace (prefixWord ++ tailWord_2947902) baseStart_2947902 baseEnd_2947902 := by
    simpa [prefixWord, tailWord_2947902, baseEnd_2947902] using wordTrace_append hprefix tailTrace_2947902
  have hstable : (prefixWord ++ tailWord_2947902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947902).length < 2 ^ (prefixWord ++ tailWord_2947902).sum := by decide
  have hdescent : baseEnd_2947902 < baseStart_2947902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947975 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 8]
def baseStart_2947975 : Nat := 118140960795 + 2947975 * 2 ^ 59
def prefixEnd_2947975 : Nat := 4983230072969 + 3 ^ 40 * 2947975 * 2
def baseEnd_2947975 : Nat := 336384029430713059545559

theorem tailTrace_2947975 : CollatzResearch.WordTrace tailWord_2947975 prefixEnd_2947975 336384029430713059545559 := by
  unfold tailWord_2947975
  simp only [CollatzResearch.WordTrace]
  refine ⟨107521481494997523891493379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71680987663331682594328919 107521481494997523891493379)
  ·
    refine ⟨161282222242496285837240069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107521481494997523891493379 161282222242496285837240069)
    ·
      refine ⟨30240416670468053594482513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161282222242496285837240069 30240416670468053594482513)
      ·
        refine ⟨22680312502851040195861885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30240416670468053594482513 22680312502851040195861885)
        ·
          refine ⟨8505117188569140073448207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22680312502851040195861885 8505117188569140073448207)
          ·
            refine ⟨12757675782853710110172311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505117188569140073448207 12757675782853710110172311)
            ·
              refine ⟨19136513674280565165258467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12757675782853710110172311 19136513674280565165258467)
              ·
                refine ⟨28704770511420847747887701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19136513674280565165258467 28704770511420847747887701)
                ·
                  refine ⟨336384029430713059545559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28704770511420847747887701 336384029430713059545559)
                  ·
                    rfl

theorem cell22_2947975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_2947975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947975 prefixEnd_2947975 := by exact prefixLift 2947975
  have htrace : WordTrace (prefixWord ++ tailWord_2947975) baseStart_2947975 baseEnd_2947975 := by
    simpa [prefixWord, tailWord_2947975, baseEnd_2947975] using wordTrace_append hprefix tailTrace_2947975
  have hstable : (prefixWord ++ tailWord_2947975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947975).length < 2 ^ (prefixWord ++ tailWord_2947975).sum := by decide
  have hdescent : baseEnd_2947975 < baseStart_2947975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947994 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_2947994 : Nat := 118140960795 + 2947994 * 2 ^ 59
def prefixEnd_2947994 : Nat := 4983230072969 + 3 ^ 40 * 2947994 * 2
def baseEnd_2947994 : Nat := 1009158592380429462411619

theorem tailTrace_2947994 : CollatzResearch.WordTrace tailWord_2947994 prefixEnd_2947994 1009158592380429462411619 := by
  unfold tailWord_2947994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26880543620482172534108759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71681449654619126757623357 26880543620482172534108759)
  ·
    refine ⟨40320815430723258801163139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26880543620482172534108759 40320815430723258801163139)
    ·
      refine ⟨60481223146084888201744709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40320815430723258801163139 60481223146084888201744709)
      ·
        refine ⟨11340229339890916537827133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60481223146084888201744709 11340229339890916537827133)
        ·
          refine ⟨4252586002459093701685175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11340229339890916537827133 4252586002459093701685175)
          ·
            refine ⟨6378879003688640552527763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252586002459093701685175 6378879003688640552527763)
            ·
              refine ⟨9568318505532960828791645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378879003688640552527763 9568318505532960828791645)
              ·
                refine ⟨3588119439574860310796867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9568318505532960828791645 3588119439574860310796867)
                ·
                  refine ⟨5382179159362290466195301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588119439574860310796867 5382179159362290466195301)
                  ·
                    refine ⟨1009158592380429462411619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382179159362290466195301 1009158592380429462411619)
                    ·
                      rfl

theorem cell22_2947994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_2947994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2947994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2947994 prefixEnd_2947994 := by exact prefixLift 2947994
  have htrace : WordTrace (prefixWord ++ tailWord_2947994) baseStart_2947994 baseEnd_2947994 := by
    simpa [prefixWord, tailWord_2947994, baseEnd_2947994] using wordTrace_append hprefix tailTrace_2947994
  have hstable : (prefixWord ++ tailWord_2947994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947994).length < 2 ^ (prefixWord ++ tailWord_2947994).sum := by decide
  have hdescent : baseEnd_2947994 < baseStart_2947994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948054 : List Nat := [5, 2, 1, 1, 2, 3, 8]
def baseStart_2948054 : Nat := 118140960795 + 2948054 * 2 ^ 59
def prefixEnd_2948054 : Nat := 4983230072969 + 3 ^ 40 * 2948054 * 2
def baseEnd_2948054 : Nat := 37377004874318863181905

theorem tailTrace_2948054 : CollatzResearch.WordTrace tailWord_2948054 prefixEnd_2948054 37377004874318863181905 := by
  unfold tailWord_2948054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720272678856957523976201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71682908574474213589079477 6720272678856957523976201)
  ·
    refine ⟨5040204509142718142982151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6720272678856957523976201 5040204509142718142982151)
    ·
      refine ⟨7560306763714077214473227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040204509142718142982151 7560306763714077214473227)
      ·
        refine ⟨11340460145571115821709841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560306763714077214473227 11340460145571115821709841)
        ·
          refine ⟨8505345109178336866282381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11340460145571115821709841 8505345109178336866282381)
          ·
            refine ⟨3189504415941876324855893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505345109178336866282381 3189504415941876324855893)
            ·
              refine ⟨37377004874318863181905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3189504415941876324855893 37377004874318863181905)
              ·
                rfl

theorem cell22_2948054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 8].length) (baseStart_2948054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948054 prefixEnd_2948054 := by exact prefixLift 2948054
  have htrace : WordTrace (prefixWord ++ tailWord_2948054) baseStart_2948054 baseEnd_2948054 := by
    simpa [prefixWord, tailWord_2948054, baseEnd_2948054] using wordTrace_append hprefix tailTrace_2948054
  have hstable : (prefixWord ++ tailWord_2948054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948054).length < 2 ^ (prefixWord ++ tailWord_2948054).sum := by decide
  have hdescent : baseEnd_2948054 < baseStart_2948054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948080 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_2948080 : Nat := 118140960795 + 2948080 * 2 ^ 59
def prefixEnd_2948080 : Nat := 4983230072969 + 3 ^ 40 * 2948080 * 2
def baseEnd_2948080 : Nat := 1009188031937953904761355

theorem tailTrace_2948080 : CollatzResearch.WordTrace tailWord_2948080 prefixEnd_2948080 1009188031937953904761355 := by
  unfold tailWord_2948080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53762655579808563412032847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71683540773078084549377129 53762655579808563412032847)
  ·
    refine ⟨80643983369712845118049271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53762655579808563412032847 80643983369712845118049271)
    ·
      refine ⟨120965975054569267677073907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80643983369712845118049271 120965975054569267677073907)
      ·
        refine ⟨181448962581853901515610861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120965975054569267677073907 181448962581853901515610861)
        ·
          refine ⟨68043360968195213068354073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181448962581853901515610861 68043360968195213068354073)
          ·
            refine ⟨51032520726146409801265555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68043360968195213068354073 51032520726146409801265555)
            ·
              refine ⟨76548781089219614701898333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51032520726146409801265555 76548781089219614701898333)
              ·
                refine ⟨28705792908457355513211875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76548781089219614701898333 28705792908457355513211875)
                ·
                  refine ⟨43058689362686033269817813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28705792908457355513211875 43058689362686033269817813)
                  ·
                    refine ⟨1009188031937953904761355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43058689362686033269817813 1009188031937953904761355)
                    ·
                      rfl

theorem cell22_2948080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_2948080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948080 prefixEnd_2948080 := by exact prefixLift 2948080
  have htrace : WordTrace (prefixWord ++ tailWord_2948080) baseStart_2948080 baseEnd_2948080 := by
    simpa [prefixWord, tailWord_2948080, baseEnd_2948080] using wordTrace_append hprefix tailTrace_2948080
  have hstable : (prefixWord ++ tailWord_2948080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948080).length < 2 ^ (prefixWord ++ tailWord_2948080).sum := by decide
  have hdescent : baseEnd_2948080 < baseStart_2948080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948204 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_2948204 : Nat := 118140960795 + 2948204 * 2 ^ 59
def prefixEnd_2948204 : Nat := 4983230072969 + 3 ^ 40 * 2948204 * 2
def baseEnd_2948204 : Nat := 1009230479672058914660975

theorem tailTrace_2948204 : CollatzResearch.WordTrace tailWord_2948204 prefixEnd_2948204 1009230479672058914660975 := by
  unfold tailWord_2948204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53764916905583948000789833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71686555874111930667719777 53764916905583948000789833)
  ·
    refine ⟨40323687679187961000592375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53764916905583948000789833 40323687679187961000592375)
    ·
      refine ⟨60485531518781941500888563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40323687679187961000592375 60485531518781941500888563)
      ·
        refine ⟨90728297278172912251332845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60485531518781941500888563 90728297278172912251332845)
        ·
          refine ⟨34023111479314842094249817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90728297278172912251332845 34023111479314842094249817)
          ·
            refine ⟨25517333609486131570687363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34023111479314842094249817 25517333609486131570687363)
            ·
              refine ⟨38276000414229197356031045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25517333609486131570687363 38276000414229197356031045)
              ·
                refine ⟨7176750077667974504255821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38276000414229197356031045 7176750077667974504255821)
                ·
                  refine ⟨2691281279125490439095933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7176750077667974504255821 2691281279125490439095933)
                  ·
                    refine ⟨1009230479672058914660975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691281279125490439095933 1009230479672058914660975)
                    ·
                      rfl

theorem cell22_2948204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_2948204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948204 prefixEnd_2948204 := by exact prefixLift 2948204
  have htrace : WordTrace (prefixWord ++ tailWord_2948204) baseStart_2948204 baseEnd_2948204 := by
    simpa [prefixWord, tailWord_2948204, baseEnd_2948204] using wordTrace_append hprefix tailTrace_2948204
  have hstable : (prefixWord ++ tailWord_2948204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948204).length < 2 ^ (prefixWord ++ tailWord_2948204).sum := by decide
  have hdescent : baseEnd_2948204 < baseStart_2948204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948206 : List Nat := [4, 1, 2, 2, 1, 4, 2, 6]
def baseStart_2948206 : Nat := 118140960795 + 2948206 * 2 ^ 59
def prefixEnd_2948206 : Nat := 4983230072969 + 3 ^ 40 * 2948206 * 2
def baseEnd_2948206 : Nat := 112136796034770175123441

theorem tailTrace_2948206 : CollatzResearch.WordTrace tailWord_2948206 prefixEnd_2948206 112136796034770175123441 := by
  unfold tailWord_2948206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441238344645081292894059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71686604504773766895434981 13441238344645081292894059)
  ·
    refine ⟨20161857516967621939341089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13441238344645081292894059 20161857516967621939341089)
    ·
      refine ⟨15121393137725716454505817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20161857516967621939341089 15121393137725716454505817)
      ·
        refine ⟨11341044853294287340879363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15121393137725716454505817 11341044853294287340879363)
        ·
          refine ⟨17011567279941431011319045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341044853294287340879363 17011567279941431011319045)
          ·
            refine ⟨3189668864989018314622321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17011567279941431011319045 3189668864989018314622321)
            ·
              refine ⟨2392251648741763735966741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189668864989018314622321 2392251648741763735966741)
              ·
                refine ⟨112136796034770175123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2392251648741763735966741 112136796034770175123441)
                ·
                  rfl

theorem cell22_2948206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_2948206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948206 prefixEnd_2948206 := by exact prefixLift 2948206
  have htrace : WordTrace (prefixWord ++ tailWord_2948206) baseStart_2948206 baseEnd_2948206 := by
    simpa [prefixWord, tailWord_2948206, baseEnd_2948206] using wordTrace_append hprefix tailTrace_2948206
  have hstable : (prefixWord ++ tailWord_2948206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948206).length < 2 ^ (prefixWord ++ tailWord_2948206).sum := by decide
  have hdescent : baseEnd_2948206 < baseStart_2948206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948234 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_2948234 : Nat := 118140960795 + 2948234 * 2 ^ 59
def prefixEnd_2948234 : Nat := 4983230072969 + 3 ^ 40 * 2948234 * 2
def baseEnd_2948234 : Nat := 336413583095049612136961

theorem tailTrace_2948234 : CollatzResearch.WordTrace tailWord_2948234 prefixEnd_2948234 336413583095049612136961 := by
  unfold tailWord_2948234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882732000264802781292939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71687285334039474083447837 26882732000264802781292939)
  ·
    refine ⟨40324098000397204171939409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26882732000264802781292939 40324098000397204171939409)
    ·
      refine ⟨30243073500297903128954557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40324098000397204171939409 30243073500297903128954557)
      ·
        refine ⟨11341152562611713673357959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30243073500297903128954557 11341152562611713673357959)
        ·
          refine ⟨17011728843917570510036939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341152562611713673357959 17011728843917570510036939)
          ·
            refine ⟨25517593265876355765055409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17011728843917570510036939 25517593265876355765055409)
            ·
              refine ⟨19138194949407266823791557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25517593265876355765055409 19138194949407266823791557)
              ·
                refine ⟨3588411553013862529460917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19138194949407266823791557 3588411553013862529460917)
                ·
                  refine ⟨336413583095049612136961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588411553013862529460917 336413583095049612136961)
                  ·
                    rfl

theorem cell22_2948234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_2948234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948234 prefixEnd_2948234 := by exact prefixLift 2948234
  have htrace : WordTrace (prefixWord ++ tailWord_2948234) baseStart_2948234 baseEnd_2948234 := by
    simpa [prefixWord, tailWord_2948234, baseEnd_2948234] using wordTrace_append hprefix tailTrace_2948234
  have hstable : (prefixWord ++ tailWord_2948234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948234).length < 2 ^ (prefixWord ++ tailWord_2948234).sum := by decide
  have hdescent : baseEnd_2948234 < baseStart_2948234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948238 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_2948238 : Nat := 118140960795 + 2948238 * 2 ^ 59
def prefixEnd_2948238 : Nat := 4983230072969 + 3 ^ 40 * 2948238 * 2
def baseEnd_2948238 : Nat := 1009242118566894159310871

theorem tailTrace_2948238 : CollatzResearch.WordTrace tailWord_2948238 prefixEnd_2948238 1009242118566894159310871 := by
  unfold tailWord_2948238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441384236630589976039671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71687382595363146538878245 13441384236630589976039671)
  ·
    refine ⟨20162076354945884964059507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13441384236630589976039671 20162076354945884964059507)
    ·
      refine ⟨30243114532418827446089261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20162076354945884964059507 30243114532418827446089261)
      ·
        refine ⟨11341167949657060292283473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30243114532418827446089261 11341167949657060292283473)
        ·
          refine ⟨8505875962242795219212605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11341167949657060292283473 8505875962242795219212605)
          ·
            refine ⟨3189703485841048207204727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505875962242795219212605 3189703485841048207204727)
            ·
              refine ⟨4784555228761572310807091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189703485841048207204727 4784555228761572310807091)
              ·
                refine ⟨7176832843142358466210637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784555228761572310807091 7176832843142358466210637)
                ·
                  refine ⟨2691312316178384424828989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7176832843142358466210637 2691312316178384424828989)
                  ·
                    refine ⟨1009242118566894159310871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691312316178384424828989 1009242118566894159310871)
                    ·
                      rfl

theorem cell22_2948238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_2948238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948238 prefixEnd_2948238 := by exact prefixLift 2948238
  have htrace : WordTrace (prefixWord ++ tailWord_2948238) baseStart_2948238 baseEnd_2948238 := by
    simpa [prefixWord, tailWord_2948238, baseEnd_2948238] using wordTrace_append hprefix tailTrace_2948238
  have hstable : (prefixWord ++ tailWord_2948238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948238).length < 2 ^ (prefixWord ++ tailWord_2948238).sum := by decide
  have hdescent : baseEnd_2948238 < baseStart_2948238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948311 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 2, 3]
def baseStart_2948311 : Nat := 118140960795 + 2948311 * 2 ^ 59
def prefixEnd_2948311 : Nat := 4983230072969 + 3 ^ 40 * 2948311 * 2
def baseEnd_2948311 : Nat := 1009267107958746302235647

theorem tailTrace_2948311 : CollatzResearch.WordTrace tailWord_2948311 prefixEnd_2948311 1009267107958746302235647 := by
  unfold tailWord_2948311
  simp only [CollatzResearch.WordTrace]
  refine ⟨107533736421780253275724787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71689157614520168850483191 107533736421780253275724787)
  ·
    refine ⟨161300604632670379913587181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107533736421780253275724787 161300604632670379913587181)
    ·
      refine ⟨60487726737251392467595193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161300604632670379913587181 60487726737251392467595193)
      ·
        refine ⟨45365795052938544350696395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60487726737251392467595193 45365795052938544350696395)
        ·
          refine ⟨68048692579407816526044593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45365795052938544350696395 68048692579407816526044593)
          ·
            refine ⟨51036519434555862394533445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68048692579407816526044593 51036519434555862394533445)
            ·
              refine ⟨9569347393979224198975021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51036519434555862394533445 9569347393979224198975021)
              ·
                refine ⟨3588505272742209074615633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9569347393979224198975021 3588505272742209074615633)
                ·
                  refine ⟨2691378954556656805961725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588505272742209074615633 2691378954556656805961725)
                  ·
                    refine ⟨1009267107958746302235647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691378954556656805961725 1009267107958746302235647)
                    ·
                      rfl

theorem cell22_2948311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_2948311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948311 prefixEnd_2948311 := by exact prefixLift 2948311
  have htrace : WordTrace (prefixWord ++ tailWord_2948311) baseStart_2948311 baseEnd_2948311 := by
    simpa [prefixWord, tailWord_2948311, baseEnd_2948311] using wordTrace_append hprefix tailTrace_2948311
  have hstable : (prefixWord ++ tailWord_2948311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948311).length < 2 ^ (prefixWord ++ tailWord_2948311).sum := by decide
  have hdescent : baseEnd_2948311 < baseStart_2948311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948399 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_2948399 : Nat := 118140960795 + 2948399 * 2 ^ 59
def prefixEnd_2948399 : Nat := 4983230072969 + 3 ^ 40 * 2948399 * 2
def baseEnd_2948399 : Nat := 1009297232157143406035377

theorem tailTrace_2948399 : CollatzResearch.WordTrace tailWord_2948399 prefixEnd_2948399 1009297232157143406035377 := by
  unfold tailWord_2948399
  simp only [CollatzResearch.WordTrace]
  refine ⟨107536946045461444304928251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71691297363640962869952167 107536946045461444304928251)
  ·
    refine ⟨161305419068192166457392377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107536946045461444304928251 161305419068192166457392377)
    ·
      refine ⟨120979064301144124843044283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161305419068192166457392377 120979064301144124843044283)
      ·
        refine ⟨181468596451716187264566425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120979064301144124843044283 181468596451716187264566425)
        ·
          refine ⟨136101447338787140448424819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181468596451716187264566425 136101447338787140448424819)
          ·
            refine ⟨204152171008180710672637229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136101447338787140448424819 204152171008180710672637229)
            ·
              refine ⟨76557064128067766502238961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204152171008180710672637229 76557064128067766502238961)
              ·
                refine ⟨57417798096050824876679221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76557064128067766502238961 57417798096050824876679221)
                ·
                  refine ⟨5382918571504764832188677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57417798096050824876679221 5382918571504764832188677)
                  ·
                    refine ⟨1009297232157143406035377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382918571504764832188677 1009297232157143406035377)
                    ·
                      rfl

theorem cell22_2948399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_2948399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948399 prefixEnd_2948399 := by exact prefixLift 2948399
  have htrace : WordTrace (prefixWord ++ tailWord_2948399) baseStart_2948399 baseEnd_2948399 := by
    simpa [prefixWord, tailWord_2948399, baseEnd_2948399] using wordTrace_append hprefix tailTrace_2948399
  have hstable : (prefixWord ++ tailWord_2948399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948399).length < 2 ^ (prefixWord ++ tailWord_2948399).sum := by decide
  have hdescent : baseEnd_2948399 < baseStart_2948399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948420 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2948420 : Nat := 118140960795 + 2948420 * 2 ^ 59
def prefixEnd_2948420 : Nat := 4983230072969 + 3 ^ 40 * 2948420 * 2
def baseEnd_2948420 : Nat := 336434806962102117086771

theorem tailTrace_2948420 : CollatzResearch.WordTrace tailWord_2948420 prefixEnd_2948420 336434806962102117086771 := by
  unfold tailWord_2948420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53768855989192682445721357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71691807985590243260961809 53768855989192682445721357)
  ·
    refine ⟨20163320995947255917145509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53768855989192682445721357 20163320995947255917145509)
    ·
      refine ⟨3780622686740110484464783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20163320995947255917145509 3780622686740110484464783)
      ·
        refine ⟨5670934030110165726697175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780622686740110484464783 5670934030110165726697175)
        ·
          refine ⟨8506401045165248590045763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670934030110165726697175 8506401045165248590045763)
          ·
            refine ⟨12759601567747872885068645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506401045165248590045763 12759601567747872885068645)
            ·
              refine ⟨2392425293952726165950371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12759601567747872885068645 2392425293952726165950371)
              ·
                refine ⟨3588637940929089248925557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392425293952726165950371 3588637940929089248925557)
                ·
                  refine ⟨336434806962102117086771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588637940929089248925557 336434806962102117086771)
                  ·
                    rfl

theorem cell22_2948420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2948420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948420 prefixEnd_2948420 := by exact prefixLift 2948420
  have htrace : WordTrace (prefixWord ++ tailWord_2948420) baseStart_2948420 baseEnd_2948420 := by
    simpa [prefixWord, tailWord_2948420, baseEnd_2948420] using wordTrace_append hprefix tailTrace_2948420
  have hstable : (prefixWord ++ tailWord_2948420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948420).length < 2 ^ (prefixWord ++ tailWord_2948420).sum := by decide
  have hdescent : baseEnd_2948420 < baseStart_2948420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948450 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2948450 : Nat := 118140960795 + 2948450 * 2 ^ 59
def prefixEnd_2948450 : Nat := 4983230072969 + 3 ^ 40 * 2948450 * 2
def baseEnd_2948450 : Nat := 1009314690499396273010221

theorem tailTrace_2948450 : CollatzResearch.WordTrace tailWord_2948450 prefixEnd_2948450 1009314690499396273010221 := by
  unfold tailWord_2948450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26884701542069170003758701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71692537445517786676689869 26884701542069170003758701)
  ·
    refine ⟨10081763078275938751409513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26884701542069170003758701 10081763078275938751409513)
    ·
      refine ⟨7561322308706954063557135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10081763078275938751409513 7561322308706954063557135)
      ·
        refine ⟨11341983463060431095335703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561322308706954063557135 11341983463060431095335703)
        ·
          refine ⟨17012975194590646643003555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341983463060431095335703 17012975194590646643003555)
          ·
            refine ⟨25519462791885969964505333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012975194590646643003555 25519462791885969964505333)
            ·
              refine ⟨2392449636739309684172375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25519462791885969964505333 2392449636739309684172375)
              ·
                refine ⟨3588674455108964526258563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392449636739309684172375 3588674455108964526258563)
                ·
                  refine ⟨5383011682663446789387845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588674455108964526258563 5383011682663446789387845)
                  ·
                    refine ⟨1009314690499396273010221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383011682663446789387845 1009314690499396273010221)
                    ·
                      rfl

theorem cell22_2948450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2948450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948450 prefixEnd_2948450 := by exact prefixLift 2948450
  have htrace : WordTrace (prefixWord ++ tailWord_2948450) baseStart_2948450 baseEnd_2948450 := by
    simpa [prefixWord, tailWord_2948450, baseEnd_2948450] using wordTrace_append hprefix tailTrace_2948450
  have hstable : (prefixWord ++ tailWord_2948450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948450).length < 2 ^ (prefixWord ++ tailWord_2948450).sum := by decide
  have hdescent : baseEnd_2948450 < baseStart_2948450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948463 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 2, 3]
def baseStart_2948463 : Nat := 118140960795 + 2948463 * 2 ^ 59
def prefixEnd_2948463 : Nat := 4983230072969 + 3 ^ 40 * 2948463 * 2
def baseEnd_2948463 : Nat := 1009319140665068572435181

theorem tailTrace_2948463 : CollatzResearch.WordTrace tailWord_2948463 prefixEnd_2948463 1009319140665068572435181 := by
  unfold tailWord_2948463
  simp only [CollatzResearch.WordTrace]
  refine ⟨107539280317229583235258043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71692853544819722156838695 107539280317229583235258043)
  ·
    refine ⟨161308920475844374852887065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107539280317229583235258043 161308920475844374852887065)
    ·
      refine ⟨120981690356883281139665299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161308920475844374852887065 120981690356883281139665299)
      ·
        refine ⟨181472535535324921709497949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120981690356883281139665299 181472535535324921709497949)
        ·
          refine ⟨68052200825746845641061731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181472535535324921709497949 68052200825746845641061731)
          ·
            refine ⟨102078301238620268461592597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68052200825746845641061731 102078301238620268461592597)
            ·
              refine ⟨4784920370560325084137153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102078301238620268461592597 4784920370560325084137153)
              ·
                refine ⟨3588690277920243813102865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4784920370560325084137153 3588690277920243813102865)
                ·
                  refine ⟨2691517708440182859827149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588690277920243813102865 2691517708440182859827149)
                  ·
                    refine ⟨1009319140665068572435181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691517708440182859827149 1009319140665068572435181)
                    ·
                      rfl

theorem cell22_2948463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_2948463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948463 prefixEnd_2948463 := by exact prefixLift 2948463
  have htrace : WordTrace (prefixWord ++ tailWord_2948463) baseStart_2948463 baseEnd_2948463 := by
    simpa [prefixWord, tailWord_2948463, baseEnd_2948463] using wordTrace_append hprefix tailTrace_2948463
  have hstable : (prefixWord ++ tailWord_2948463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948463).length < 2 ^ (prefixWord ++ tailWord_2948463).sum := by decide
  have hdescent : baseEnd_2948463 < baseStart_2948463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948525 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2948525 : Nat := 118140960795 + 2948525 * 2 ^ 59
def prefixEnd_2948525 : Nat := 4983230072969 + 3 ^ 40 * 2948525 * 2
def baseEnd_2948525 : Nat := 1009340364532121077384991

theorem tailTrace_2948525 : CollatzResearch.WordTrace tailWord_2948525 prefixEnd_2948525 1009340364532121077384991 := by
  unfold tailWord_2948525
  simp only [CollatzResearch.WordTrace]
  refine ⟨107541541643004967824015029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71694361095336645216010019 107541541643004967824015029)
  ·
    refine ⟨10082019529031715733501409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107541541643004967824015029 10082019529031715733501409)
    ·
      refine ⟨7561514646773786800126057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10082019529031715733501409 7561514646773786800126057)
      ·
        refine ⟨5671135985080340100094543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561514646773786800126057 5671135985080340100094543)
        ·
          refine ⟨8506703977620510150141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671135985080340100094543 8506703977620510150141815)
          ·
            refine ⟨12760055966430765225212723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506703977620510150141815 12760055966430765225212723)
            ·
              refine ⟨19140083949646147837819085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760055966430765225212723 19140083949646147837819085)
              ·
                refine ⟨7177531481117305439182157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19140083949646147837819085 7177531481117305439182157)
                ·
                  refine ⟨2691574305418989539693309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7177531481117305439182157 2691574305418989539693309)
                  ·
                    refine ⟨1009340364532121077384991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691574305418989539693309 1009340364532121077384991)
                    ·
                      rfl

theorem cell22_2948525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2948525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948525 prefixEnd_2948525 := by exact prefixLift 2948525
  have htrace : WordTrace (prefixWord ++ tailWord_2948525) baseStart_2948525 baseEnd_2948525 := by
    simpa [prefixWord, tailWord_2948525, baseEnd_2948525] using wordTrace_append hprefix tailTrace_2948525
  have hstable : (prefixWord ++ tailWord_2948525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948525).length < 2 ^ (prefixWord ++ tailWord_2948525).sum := by decide
  have hdescent : baseEnd_2948525 < baseStart_2948525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948536 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_2948536 : Nat := 118140960795 + 2948536 * 2 ^ 59
def prefixEnd_2948536 : Nat := 4983230072969 + 3 ^ 40 * 2948536 * 2
def baseEnd_2948536 : Nat := 1009344130056920715359957

theorem tailTrace_2948536 : CollatzResearch.WordTrace tailWord_2948536 prefixEnd_2948536 1009344130056920715359957 := by
  unfold tailWord_2948536
  simp only [CollatzResearch.WordTrace]
  refine ⟨53770971422982558351332731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71694628563976744468443641 53770971422982558351332731)
  ·
    refine ⟨80656457134473837526999097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53770971422982558351332731 80656457134473837526999097)
    ·
      refine ⟨60492342850855378145249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80656457134473837526999097 60492342850855378145249323)
      ·
        refine ⟨90738514276283067217873985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60492342850855378145249323 90738514276283067217873985)
        ·
          refine ⟨68053885707212300413405489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90738514276283067217873985 68053885707212300413405489)
          ·
            refine ⟨51040414280409225310054117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68053885707212300413405489 51040414280409225310054117)
            ·
              refine ⟨9570077677576729745635147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51040414280409225310054117 9570077677576729745635147)
              ·
                refine ⟨14355116516365094618452721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570077677576729745635147 14355116516365094618452721)
                ·
                  refine ⟨10766337387273820963839541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14355116516365094618452721 10766337387273820963839541)
                  ·
                    refine ⟨1009344130056920715359957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10766337387273820963839541 1009344130056920715359957)
                    ·
                      rfl

theorem cell22_2948536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_2948536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948536 prefixEnd_2948536 := by exact prefixLift 2948536
  have htrace : WordTrace (prefixWord ++ tailWord_2948536) baseStart_2948536 baseEnd_2948536 := by
    simpa [prefixWord, tailWord_2948536, baseEnd_2948536] using wordTrace_append hprefix tailTrace_2948536
  have hstable : (prefixWord ++ tailWord_2948536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948536).length < 2 ^ (prefixWord ++ tailWord_2948536).sum := by decide
  have hdescent : baseEnd_2948536 < baseStart_2948536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948568 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_2948568 : Nat := 118140960795 + 2948568 * 2 ^ 59
def prefixEnd_2948568 : Nat := 4983230072969 + 3 ^ 40 * 2948568 * 2
def baseEnd_2948568 : Nat := 1009355084310883298559859

theorem tailTrace_2948568 : CollatzResearch.WordTrace tailWord_2948568 prefixEnd_2948568 1009355084310883298559859 := by
  unfold tailWord_2948568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53771554990924593083915179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71695406654566124111886905 53771554990924593083915179)
  ·
    refine ⟨80657332486386889625872769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53771554990924593083915179 80657332486386889625872769)
    ·
      refine ⟨60492999364790167219404577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80657332486386889625872769 60492999364790167219404577)
      ·
        refine ⟨45369749523592625414553433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60492999364790167219404577 45369749523592625414553433)
        ·
          refine ⟨34027312142694469060915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45369749523592625414553433 34027312142694469060915075)
          ·
            refine ⟨51040968214041703591372613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34027312142694469060915075 51040968214041703591372613)
            ·
              refine ⟨9570181540132819423382365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51040968214041703591372613 9570181540132819423382365)
              ·
                refine ⟨3588818077549807283768387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9570181540132819423382365 3588818077549807283768387)
                ·
                  refine ⟨5383227116324710925652581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588818077549807283768387 5383227116324710925652581)
                  ·
                    refine ⟨1009355084310883298559859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383227116324710925652581 1009355084310883298559859)
                    ·
                      rfl

theorem cell22_2948568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_2948568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948568 prefixEnd_2948568 := by exact prefixLift 2948568
  have htrace : WordTrace (prefixWord ++ tailWord_2948568) baseStart_2948568 baseEnd_2948568 := by
    simpa [prefixWord, tailWord_2948568, baseEnd_2948568] using wordTrace_append hprefix tailTrace_2948568
  have hstable : (prefixWord ++ tailWord_2948568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948568).length < 2 ^ (prefixWord ++ tailWord_2948568).sum := by decide
  have hdescent : baseEnd_2948568 < baseStart_2948568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948583 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 6]
def baseStart_2948583 : Nat := 118140960795 + 2948583 * 2 ^ 59
def prefixEnd_2948583 : Nat := 4983230072969 + 3 ^ 40 * 2948583 * 2
def baseEnd_2948583 : Nat := 336453406372476086478271

theorem tailTrace_2948583 : CollatzResearch.WordTrace tailWord_2948583 prefixEnd_2948583 336453406372476086478271 := by
  unfold tailWord_2948583
  simp only [CollatzResearch.WordTrace]
  refine ⟨107543657076794843729626403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71695771384529895819750935 107543657076794843729626403)
  ·
    refine ⟨161315485615192265594439605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107543657076794843729626403 161315485615192265594439605)
    ·
      refine ⟨15123326776424274899478713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161315485615192265594439605 15123326776424274899478713)
      ·
        refine ⟨11342495082318206174609035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15123326776424274899478713 11342495082318206174609035)
        ·
          refine ⟨17013742623477309261913553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11342495082318206174609035 17013742623477309261913553)
          ·
            refine ⟨12760306967607981946435165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17013742623477309261913553 12760306967607981946435165)
            ·
              refine ⟨4785115112852993229913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12760306967607981946435165 4785115112852993229913187)
              ·
                refine ⟨7177672669279489844869781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785115112852993229913187 7177672669279489844869781)
                ·
                  refine ⟨336453406372476086478271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7177672669279489844869781 336453406372476086478271)
                  ·
                    rfl

theorem cell22_2948583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_2948583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948583 prefixEnd_2948583 := by exact prefixLift 2948583
  have htrace : WordTrace (prefixWord ++ tailWord_2948583) baseStart_2948583 baseEnd_2948583 := by
    simpa [prefixWord, tailWord_2948583, baseEnd_2948583] using wordTrace_append hprefix tailTrace_2948583
  have hstable : (prefixWord ++ tailWord_2948583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948583).length < 2 ^ (prefixWord ++ tailWord_2948583).sum := by decide
  have hdescent : baseEnd_2948583 < baseStart_2948583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948589 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2948589 : Nat := 118140960795 + 2948589 * 2 ^ 59
def prefixEnd_2948589 : Nat := 4983230072969 + 3 ^ 40 * 2948589 * 2
def baseEnd_2948589 : Nat := 336454091013348747928265

theorem tailTrace_2948589 : CollatzResearch.WordTrace tailWord_2948589 prefixEnd_2948589 336454091013348747928265 := by
  unfold tailWord_2948589
  simp only [CollatzResearch.WordTrace]
  refine ⟨107543875914773106754344821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71695917276515404502896547 107543875914773106754344821)
  ·
    refine ⟨10082238367009978758219827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107543875914773106754344821 10082238367009978758219827)
    ·
      refine ⟨15123357550514968137329741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10082238367009978758219827 15123357550514968137329741)
      ·
        refine ⟨5671259081443113051498653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15123357550514968137329741 5671259081443113051498653)
        ·
          refine ⟨2126722155541167394311995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5671259081443113051498653 2126722155541167394311995)
          ·
            refine ⟨3190083233311751091467993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126722155541167394311995 3190083233311751091467993)
            ·
              refine ⟨2392562424983813318600995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190083233311751091467993 2392562424983813318600995)
              ·
                refine ⟨3588843637475719977901493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392562424983813318600995 3588843637475719977901493)
                ·
                  refine ⟨336454091013348747928265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588843637475719977901493 336454091013348747928265)
                  ·
                    rfl

theorem cell22_2948589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2948589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948589 prefixEnd_2948589 := by exact prefixLift 2948589
  have htrace : WordTrace (prefixWord ++ tailWord_2948589) baseStart_2948589 baseEnd_2948589 := by
    simpa [prefixWord, tailWord_2948589, baseEnd_2948589] using wordTrace_append hprefix tailTrace_2948589
  have hstable : (prefixWord ++ tailWord_2948589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948589).length < 2 ^ (prefixWord ++ tailWord_2948589).sum := by decide
  have hdescent : baseEnd_2948589 < baseStart_2948589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948628 : List Nat := [2, 4, 3, 1, 12]
def baseStart_2948628 : Nat := 118140960795 + 2948628 * 2 ^ 59
def prefixEnd_2948628 : Nat := 4983230072969 + 3 ^ 40 * 2948628 * 2
def baseEnd_2948628 : Nat := 4153809150358284535225

theorem tailTrace_2948628 : CollatzResearch.WordTrace tailWord_2948628 prefixEnd_2948628 4153809150358284535225 := by
  unfold tailWord_2948628
  simp only [CollatzResearch.WordTrace]
  refine ⟨53772649180815908207507269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71696865574421210943343025 53772649180815908207507269)
  ·
    refine ⟨10082371721402982788907613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53772649180815908207507269 10082371721402982788907613)
    ·
      refine ⟨3780889395526118545840355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10082371721402982788907613 3780889395526118545840355)
      ·
        refine ⟨5671334093289177818760533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780889395526118545840355 5671334093289177818760533)
        ·
          refine ⟨4153809150358284535225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5671334093289177818760533 4153809150358284535225)
          ·
            rfl

theorem cell22_2948628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 12].length) (baseStart_2948628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948628 prefixEnd_2948628 := by exact prefixLift 2948628
  have htrace : WordTrace (prefixWord ++ tailWord_2948628) baseStart_2948628 baseEnd_2948628 := by
    simpa [prefixWord, tailWord_2948628, baseEnd_2948628] using wordTrace_append hprefix tailTrace_2948628
  have hstable : (prefixWord ++ tailWord_2948628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948628).length < 2 ^ (prefixWord ++ tailWord_2948628).sum := by decide
  have hdescent : baseEnd_2948628 < baseStart_2948628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948632 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_2948632 : Nat := 118140960795 + 2948632 * 2 ^ 59
def prefixEnd_2948632 : Nat := 4983230072969 + 3 ^ 40 * 2948632 * 2
def baseEnd_2948632 : Nat := 1009376992818808464959663

theorem tailTrace_2948632 : CollatzResearch.WordTrace tailWord_2948632 prefixEnd_2948632 1009376992818808464959663 := by
  unfold tailWord_2948632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53772722126808662549080075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71696962835744883398773433 53772722126808662549080075)
  ·
    refine ⟨80659083190212993823620113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53772722126808662549080075 80659083190212993823620113)
    ·
      refine ⟨60494312392659745367715085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80659083190212993823620113 60494312392659745367715085)
      ·
        refine ⟨22685367147247404512893157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60494312392659745367715085 22685367147247404512893157)
        ·
          refine ⟨4253506340108888346167467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22685367147247404512893157 4253506340108888346167467)
          ·
            refine ⟨6380259510163332519251201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253506340108888346167467 6380259510163332519251201)
            ·
              refine ⟨4785194632622499389438401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6380259510163332519251201 4785194632622499389438401)
              ·
                refine ⟨3588895974466874542078801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4785194632622499389438401 3588895974466874542078801)
                ·
                  refine ⟨2691671980850155906559101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588895974466874542078801 2691671980850155906559101)
                  ·
                    refine ⟨1009376992818808464959663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691671980850155906559101 1009376992818808464959663)
                    ·
                      rfl

theorem cell22_2948632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_2948632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948632 prefixEnd_2948632 := by exact prefixLift 2948632
  have htrace : WordTrace (prefixWord ++ tailWord_2948632) baseStart_2948632 baseEnd_2948632 := by
    simpa [prefixWord, tailWord_2948632, baseEnd_2948632] using wordTrace_append hprefix tailTrace_2948632
  have hstable : (prefixWord ++ tailWord_2948632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948632).length < 2 ^ (prefixWord ++ tailWord_2948632).sum := by decide
  have hdescent : baseEnd_2948632 < baseStart_2948632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948656 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_2948656 : Nat := 118140960795 + 2948656 * 2 ^ 59
def prefixEnd_2948656 : Nat := 4983230072969 + 3 ^ 40 * 2948656 * 2
def baseEnd_2948656 : Nat := 336461736169760134119863

theorem tailTrace_2948656 : CollatzResearch.WordTrace tailWord_2948656 prefixEnd_2948656 336461736169760134119863 := by
  unfold tailWord_2948656
  simp only [CollatzResearch.WordTrace]
  refine ⟨53773159802765188598516911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71697546403686918131355881 53773159802765188598516911)
  ·
    refine ⟨80659739704147782897775367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53773159802765188598516911 80659739704147782897775367)
    ·
      refine ⟨120989609556221674346663051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80659739704147782897775367 120989609556221674346663051)
      ·
        refine ⟨181484414334332511519994577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120989609556221674346663051 181484414334332511519994577)
        ·
          refine ⟨136113310750749383639995933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181484414334332511519994577 136113310750749383639995933)
          ·
            refine ⟨51042491531531018864998475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136113310750749383639995933 51042491531531018864998475)
            ·
              refine ⟨76563737297296528297497713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51042491531531018864998475 76563737297296528297497713)
              ·
                refine ⟨57422802972972396223123285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76563737297296528297497713 57422802972972396223123285)
                ·
                  refine ⟨336461736169760134119863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57422802972972396223123285 336461736169760134119863)
                  ·
                    rfl

theorem cell22_2948656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_2948656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948656 prefixEnd_2948656 := by exact prefixLift 2948656
  have htrace : WordTrace (prefixWord ++ tailWord_2948656) baseStart_2948656 baseEnd_2948656 := by
    simpa [prefixWord, tailWord_2948656, baseEnd_2948656] using wordTrace_append hprefix tailTrace_2948656
  have hstable : (prefixWord ++ tailWord_2948656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948656).length < 2 ^ (prefixWord ++ tailWord_2948656).sum := by decide
  have hdescent : baseEnd_2948656 < baseStart_2948656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948662 : List Nat := [5, 1, 2, 1, 3, 1, 3, 6]
def baseStart_2948662 : Nat := 118140960795 + 2948662 * 2 ^ 59
def prefixEnd_2948662 : Nat := 4983230072969 + 3 ^ 40 * 2948662 * 2
def baseEnd_2948662 : Nat := 112154140270210931856619

theorem tailTrace_2948662 : CollatzResearch.WordTrace tailWord_2948662 prefixEnd_2948662 112154140270210931856619 := by
  unfold tailWord_2948662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721658652719290013859515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71697692295672426814501493 6721658652719290013859515)
  ·
    refine ⟨10082487979078935020789273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721658652719290013859515 10082487979078935020789273)
    ·
      refine ⟨7561865984309201265591955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10082487979078935020789273 7561865984309201265591955)
      ·
        refine ⟨11342798976463801898387933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561865984309201265591955 11342798976463801898387933)
        ·
          refine ⟨4253549616173925711895475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11342798976463801898387933 4253549616173925711895475)
          ·
            refine ⟨6380324424260888567843213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253549616173925711895475 6380324424260888567843213)
            ·
              refine ⟨2392621659097833212941205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6380324424260888567843213 2392621659097833212941205)
              ·
                refine ⟨112154140270210931856619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2392621659097833212941205 112154140270210931856619)
                ·
                  rfl

theorem cell22_2948662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_2948662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948662 prefixEnd_2948662 := by exact prefixLift 2948662
  have htrace : WordTrace (prefixWord ++ tailWord_2948662) baseStart_2948662 baseEnd_2948662 := by
    simpa [prefixWord, tailWord_2948662, baseEnd_2948662] using wordTrace_append hprefix tailTrace_2948662
  have hstable : (prefixWord ++ tailWord_2948662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948662).length < 2 ^ (prefixWord ++ tailWord_2948662).sum := by decide
  have hdescent : baseEnd_2948662 < baseStart_2948662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948673 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 7]
def baseStart_2948673 : Nat := 118140960795 + 2948673 * 2 ^ 59
def prefixEnd_2948673 : Nat := 4983230072969 + 3 ^ 40 * 2948673 * 2
def baseEnd_2948673 : Nat := 336463675985566008228179

theorem tailTrace_2948673 : CollatzResearch.WordTrace tailWord_2948673 prefixEnd_2948673 336463675985566008228179 := by
  unfold tailWord_2948673
  simp only [CollatzResearch.WordTrace]
  refine ⟨107546939646468789100402673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71697959764312526066935115 107546939646468789100402673)
  ·
    refine ⟨80660204734851591825302005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107546939646468789100402673 80660204734851591825302005)
    ·
      refine ⟨7561894193892336733622063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80660204734851591825302005 7561894193892336733622063)
      ·
        refine ⟨11342841290838505100433095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561894193892336733622063 11342841290838505100433095)
        ·
          refine ⟨17014261936257757650649643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11342841290838505100433095 17014261936257757650649643)
          ·
            refine ⟨25521392904386636475974465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17014261936257757650649643 25521392904386636475974465)
            ·
              refine ⟨19141044678289977356980849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25521392904386636475974465 19141044678289977356980849)
              ·
                refine ⟨14355783508717483017735637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19141044678289977356980849 14355783508717483017735637)
                ·
                  refine ⟨336463675985566008228179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14355783508717483017735637 336463675985566008228179)
                  ·
                    rfl

theorem cell22_2948673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_2948673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948673 prefixEnd_2948673 := by exact prefixLift 2948673
  have htrace : WordTrace (prefixWord ++ tailWord_2948673) baseStart_2948673 baseEnd_2948673 := by
    simpa [prefixWord, tailWord_2948673, baseEnd_2948673] using wordTrace_append hprefix tailTrace_2948673
  have hstable : (prefixWord ++ tailWord_2948673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948673).length < 2 ^ (prefixWord ++ tailWord_2948673).sum := by decide
  have hdescent : baseEnd_2948673 < baseStart_2948673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948677 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2948677 : Nat := 118140960795 + 2948677 * 2 ^ 59
def prefixEnd_2948677 : Nat := 4983230072969 + 3 ^ 40 * 2948677 * 2
def baseEnd_2948677 : Nat := 1009392397238443347584525

theorem tailTrace_2948677 : CollatzResearch.WordTrace tailWord_2948677 prefixEnd_2948677 1009392397238443347584525 := by
  unfold tailWord_2948677
  simp only [CollatzResearch.WordTrace]
  refine ⟨107547085538454297783548285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71698057025636198522365523 107547085538454297783548285)
  ·
    refine ⟨40330157076920361668830607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107547085538454297783548285 40330157076920361668830607)
    ·
      refine ⟨60495235615380542503245911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40330157076920361668830607 60495235615380542503245911)
      ·
        refine ⟨90742853423070813754868867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60495235615380542503245911 90742853423070813754868867)
        ·
          refine ⟨136114280134606220632303301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90742853423070813754868867 136114280134606220632303301)
          ·
            refine ⟨25521427525238666368556869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136114280134606220632303301 25521427525238666368556869)
            ·
              refine ⟨4785267660982249944104413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25521427525238666368556869 4785267660982249944104413)
              ·
                refine ⟨1794475372868343729039155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785267660982249944104413 1794475372868343729039155)
                ·
                  refine ⟨2691713059302515593558733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794475372868343729039155 2691713059302515593558733)
                  ·
                    refine ⟨1009392397238443347584525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691713059302515593558733 1009392397238443347584525)
                    ·
                      rfl

theorem cell22_2948677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2948677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948677 prefixEnd_2948677 := by exact prefixLift 2948677
  have htrace : WordTrace (prefixWord ++ tailWord_2948677) baseStart_2948677 baseEnd_2948677 := by
    simpa [prefixWord, tailWord_2948677, baseEnd_2948677] using wordTrace_append hprefix tailTrace_2948677
  have hstable : (prefixWord ++ tailWord_2948677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948677).length < 2 ^ (prefixWord ++ tailWord_2948677).sum := by decide
  have hdescent : baseEnd_2948677 < baseStart_2948677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948690 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_2948690 : Nat := 118140960795 + 2948690 * 2 ^ 59
def prefixEnd_2948690 : Nat := 4983230072969 + 3 ^ 40 * 2948690 * 2
def baseEnd_2948690 : Nat := 336465615801371882336495

theorem tailTrace_2948690 : CollatzResearch.WordTrace tailWord_2948690 prefixEnd_2948690 336465615801371882336495 := by
  unfold tailWord_2948690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26886889921851800250942881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71698373124938134002514349 26886889921851800250942881)
  ·
    refine ⟨20165167441388850188207161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26886889921851800250942881 20165167441388850188207161)
    ·
      refine ⟨15123875581041637641155371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20165167441388850188207161 15123875581041637641155371)
      ·
        refine ⟨22685813371562456461733057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15123875581041637641155371 22685813371562456461733057)
        ·
          refine ⟨17014360028671842346299793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22685813371562456461733057 17014360028671842346299793)
          ·
            refine ⟨12760770021503881759724845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17014360028671842346299793 12760770021503881759724845)
            ·
              refine ⟨4785288758063955659896817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12760770021503881759724845 4785288758063955659896817)
              ·
                refine ⟨3588966568547966744922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4785288758063955659896817 3588966568547966744922613)
                ·
                  refine ⟨336465615801371882336495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588966568547966744922613 336465615801371882336495)
                  ·
                    rfl

theorem cell22_2948690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_2948690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948690 prefixEnd_2948690 := by exact prefixLift 2948690
  have htrace : WordTrace (prefixWord ++ tailWord_2948690) baseStart_2948690 baseEnd_2948690 := by
    simpa [prefixWord, tailWord_2948690, baseEnd_2948690] using wordTrace_append hprefix tailTrace_2948690
  have hstable : (prefixWord ++ tailWord_2948690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948690).length < 2 ^ (prefixWord ++ tailWord_2948690).sum := by decide
  have hdescent : baseEnd_2948690 < baseStart_2948690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948720 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_2948720 : Nat := 118140960795 + 2948720 * 2 ^ 59
def prefixEnd_2948720 : Nat := 4983230072969 + 3 ^ 40 * 2948720 * 2
def baseEnd_2948720 : Nat := 1009407117017205568759393

theorem tailTrace_2948720 : CollatzResearch.WordTrace tailWord_2948720 prefixEnd_2948720 1009407117017205568759393 := by
  unfold tailWord_2948720
  simp only [CollatzResearch.WordTrace]
  refine ⟨53774326938649258063681807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71699102584865677418242409 53774326938649258063681807)
  ·
    refine ⟨80661490407973887095522711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53774326938649258063681807 80661490407973887095522711)
    ·
      refine ⟨120992235611960830643284067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80661490407973887095522711 120992235611960830643284067)
      ·
        refine ⟨181488353417941245964926101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120992235611960830643284067 181488353417941245964926101)
        ·
          refine ⟨8507266566465995904605911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181488353417941245964926101 8507266566465995904605911)
          ·
            refine ⟨12760899849698993856908867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507266566465995904605911 12760899849698993856908867)
            ·
              refine ⟨19141349774548490785363301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12760899849698993856908867 19141349774548490785363301)
              ·
                refine ⟨3589003082727842022255619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19141349774548490785363301 3589003082727842022255619)
                ·
                  refine ⟨5383504624091763033383429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589003082727842022255619 5383504624091763033383429)
                  ·
                    refine ⟨1009407117017205568759393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383504624091763033383429 1009407117017205568759393)
                    ·
                      rfl

theorem cell22_2948720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_2948720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948720 prefixEnd_2948720 := by exact prefixLift 2948720
  have htrace : WordTrace (prefixWord ++ tailWord_2948720) baseStart_2948720 baseEnd_2948720 := by
    simpa [prefixWord, tailWord_2948720, baseEnd_2948720] using wordTrace_append hprefix tailTrace_2948720
  have hstable : (prefixWord ++ tailWord_2948720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948720).length < 2 ^ (prefixWord ++ tailWord_2948720).sum := by decide
  have hdescent : baseEnd_2948720 < baseStart_2948720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948825 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 5]
def baseStart_2948825 : Nat := 118140960795 + 2948825 * 2 ^ 59
def prefixEnd_2948825 : Nat := 4983230072969 + 3 ^ 40 * 2948825 * 2
def baseEnd_2948825 : Nat := 336481020221006764961357

theorem tailTrace_2948825 : CollatzResearch.WordTrace tailWord_2948825 prefixEnd_2948825 336481020221006764961357 := by
  unfold tailWord_2948825
  simp only [CollatzResearch.WordTrace]
  refine ⟨107552483541918119059935929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71701655694612079373290619 107552483541918119059935929)
  ·
    refine ⟨80664362656438589294951947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107552483541918119059935929 80664362656438589294951947)
    ·
      refine ⟨120996543984657883942427921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80664362656438589294951947 120996543984657883942427921)
      ·
        refine ⟨90747407988493412956820941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120996543984657883942427921 90747407988493412956820941)
        ·
          refine ⟨34030277995685029858807853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90747407988493412956820941 34030277995685029858807853)
          ·
            refine ⟨12761354248381886197052945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34030277995685029858807853 12761354248381886197052945)
            ·
              refine ⟨9571015686286414647789709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761354248381886197052945 9571015686286414647789709)
              ·
                refine ⟨3589130882357405492921141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9571015686286414647789709 3589130882357405492921141)
                ·
                  refine ⟨336481020221006764961357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3589130882357405492921141 336481020221006764961357)
                  ·
                    rfl

theorem cell22_2948825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_2948825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948825 prefixEnd_2948825 := by exact prefixLift 2948825
  have htrace : WordTrace (prefixWord ++ tailWord_2948825) baseStart_2948825 baseEnd_2948825 := by
    simpa [prefixWord, tailWord_2948825, baseEnd_2948825] using wordTrace_append hprefix tailTrace_2948825
  have hstable : (prefixWord ++ tailWord_2948825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948825).length < 2 ^ (prefixWord ++ tailWord_2948825).sum := by decide
  have hdescent : baseEnd_2948825 < baseStart_2948825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948904 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_2948904 : Nat := 118140960795 + 2948904 * 2 ^ 59
def prefixEnd_2948904 : Nat := 4983230072969 + 3 ^ 40 * 2948904 * 2
def baseEnd_2948904 : Nat := 336490034659163474052943

theorem tailTrace_2948904 : CollatzResearch.WordTrace tailWord_2948904 prefixEnd_2948904 336490034659163474052943 := by
  unfold tailWord_2948904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53777682454315957776030883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71703576605754610368041177 53777682454315957776030883)
  ·
    refine ⟨80666523681473936664046325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53777682454315957776030883 80666523681473936664046325)
    ·
      refine ⟨7562486595138181562254343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80666523681473936664046325 7562486595138181562254343)
      ·
        refine ⟨11343729892707272343381515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562486595138181562254343 11343729892707272343381515)
        ·
          refine ⟨17015594839060908515072273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11343729892707272343381515 17015594839060908515072273)
          ·
            refine ⟨12761696129295681386304205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17015594839060908515072273 12761696129295681386304205)
            ·
              refine ⟨4785636048485880519864077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12761696129295681386304205 4785636048485880519864077)
              ·
                refine ⟨1794613518182205194949029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785636048485880519864077 1794613518182205194949029)
                ·
                  refine ⟨336490034659163474052943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794613518182205194949029 336490034659163474052943)
                  ·
                    rfl

theorem cell22_2948904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_2948904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948904 prefixEnd_2948904 := by exact prefixLift 2948904
  have htrace : WordTrace (prefixWord ++ tailWord_2948904) baseStart_2948904 baseEnd_2948904 := by
    simpa [prefixWord, tailWord_2948904, baseEnd_2948904] using wordTrace_append hprefix tailTrace_2948904
  have hstable : (prefixWord ++ tailWord_2948904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948904).length < 2 ^ (prefixWord ++ tailWord_2948904).sum := by decide
  have hdescent : baseEnd_2948904 < baseStart_2948904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948921 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 6]
def baseStart_2948921 : Nat := 118140960795 + 2948921 * 2 ^ 59
def prefixEnd_2948921 : Nat := 4983230072969 + 3 ^ 40 * 2948921 * 2
def baseEnd_2948921 : Nat := 336491974474969348161259

theorem tailTrace_2948921 : CollatzResearch.WordTrace tailWord_2948921 prefixEnd_2948921 336491974474969348161259 := by
  unfold tailWord_2948921
  simp only [CollatzResearch.WordTrace]
  refine ⟨107555984949570327455430617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71703989966380218303620411 107555984949570327455430617)
  ·
    refine ⟨80666988712177745591572963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107555984949570327455430617 80666988712177745591572963)
    ·
      refine ⟨121000483068266618387359445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80666988712177745591572963 121000483068266618387359445)
      ·
        refine ⟨2835948821912498868453737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121000483068266618387359445 2835948821912498868453737)
        ·
          refine ⟨2126961616434374151340303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2835948821912498868453737 2126961616434374151340303)
          ·
            refine ⟨3190442424651561227010455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126961616434374151340303 3190442424651561227010455)
            ·
              refine ⟨4785663636977341840515683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190442424651561227010455 4785663636977341840515683)
              ·
                refine ⟨7178495455466012760773525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785663636977341840515683 7178495455466012760773525)
                ·
                  refine ⟨336491974474969348161259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7178495455466012760773525 336491974474969348161259)
                  ·
                    rfl

theorem cell22_2948921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_2948921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948921 prefixEnd_2948921 := by exact prefixLift 2948921
  have htrace : WordTrace (prefixWord ++ tailWord_2948921) baseStart_2948921 baseEnd_2948921 := by
    simpa [prefixWord, tailWord_2948921, baseEnd_2948921] using wordTrace_append hprefix tailTrace_2948921
  have hstable : (prefixWord ++ tailWord_2948921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948921).length < 2 ^ (prefixWord ++ tailWord_2948921).sum := by decide
  have hdescent : baseEnd_2948921 < baseStart_2948921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948936 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_2948936 : Nat := 118140960795 + 2948936 * 2 ^ 59
def prefixEnd_2948936 : Nat := 4983230072969 + 3 ^ 40 * 2948936 * 2
def baseEnd_2948936 : Nat := 1009481058231453005358731

theorem tailTrace_2948936 : CollatzResearch.WordTrace tailWord_2948936 prefixEnd_2948936 1009481058231453005358731 := by
  unfold tailWord_2948936
  simp only [CollatzResearch.WordTrace]
  refine ⟨53778266022257992508613331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71704354696343990011484441 53778266022257992508613331)
  ·
    refine ⟨80667399033386988762919997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53778266022257992508613331 80667399033386988762919997)
    ·
      refine ⟨30250274637520120786094999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80667399033386988762919997 30250274637520120786094999)
      ·
        refine ⟨45375411956280181179142499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30250274637520120786094999 45375411956280181179142499)
        ·
          refine ⟨68063117934420271768713749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45375411956280181179142499 68063117934420271768713749)
          ·
            refine ⟨3190458653175950239158457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68063117934420271768713749 3190458653175950239158457)
            ·
              refine ⟨2392843989881962679368843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190458653175950239158457 2392843989881962679368843)
              ·
                refine ⟨3589265984822944019053265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392843989881962679368843 3589265984822944019053265)
                ·
                  refine ⟨2691949488617208014289949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3589265984822944019053265 2691949488617208014289949)
                  ·
                    refine ⟨1009481058231453005358731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691949488617208014289949 1009481058231453005358731)
                    ·
                      rfl

theorem cell22_2948936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_2948936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948936 prefixEnd_2948936 := by exact prefixLift 2948936
  have htrace : WordTrace (prefixWord ++ tailWord_2948936) baseStart_2948936 baseEnd_2948936 := by
    simpa [prefixWord, tailWord_2948936, baseEnd_2948936] using wordTrace_append hprefix tailTrace_2948936
  have hstable : (prefixWord ++ tailWord_2948936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948936).length < 2 ^ (prefixWord ++ tailWord_2948936).sum := by decide
  have hdescent : baseEnd_2948936 < baseStart_2948936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948977 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 5]
def baseStart_2948977 : Nat := 118140960795 + 2948977 * 2 ^ 59
def prefixEnd_2948977 : Nat := 4983230072969 + 3 ^ 40 * 2948977 * 2
def baseEnd_2948977 : Nat := 336498364456447521694535

theorem tailTrace_2948977 : CollatzResearch.WordTrace tailWord_2948977 prefixEnd_2948977 336498364456447521694535 := by
  unfold tailWord_2948977
  simp only [CollatzResearch.WordTrace]
  refine ⟨107558027437367449019469185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71705351624911632679646123 107558027437367449019469185)
  ·
    refine ⟨80668520578025586764601889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107558027437367449019469185 80668520578025586764601889)
    ·
      refine ⟨60501390433519190073451417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80668520578025586764601889 60501390433519190073451417)
      ·
        refine ⟨45376042825139392555088563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60501390433519190073451417 45376042825139392555088563)
        ·
          refine ⟨68064064237709088832632845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45376042825139392555088563 68064064237709088832632845)
          ·
            refine ⟨25524024089140908312237317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68064064237709088832632845 25524024089140908312237317)
            ·
              refine ⟨4785754516713920308544497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25524024089140908312237317 4785754516713920308544497)
              ·
                refine ⟨3589315887535440231408373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4785754516713920308544497 3589315887535440231408373)
                ·
                  refine ⟨336498364456447521694535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3589315887535440231408373 336498364456447521694535)
                  ·
                    rfl

theorem cell22_2948977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_2948977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948977 prefixEnd_2948977 := by exact prefixLift 2948977
  have htrace : WordTrace (prefixWord ++ tailWord_2948977) baseStart_2948977 baseEnd_2948977 := by
    simpa [prefixWord, tailWord_2948977, baseEnd_2948977] using wordTrace_append hprefix tailTrace_2948977
  have hstable : (prefixWord ++ tailWord_2948977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948977).length < 2 ^ (prefixWord ++ tailWord_2948977).sum := by decide
  have hdescent : baseEnd_2948977 < baseStart_2948977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948981 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2948981 : Nat := 118140960795 + 2948981 * 2 ^ 59
def prefixEnd_2948981 : Nat := 4983230072969 + 3 ^ 40 * 2948981 * 2
def baseEnd_2948981 : Nat := 1009496462651087887983593

theorem tailTrace_2948981 : CollatzResearch.WordTrace tailWord_2948981 prefixEnd_2948981 1009496462651087887983593 := by
  unfold tailWord_2948981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107558173329352957702614797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71705448886235305135076531 107558173329352957702614797)
  ·
    refine ⟨40334314998507359138480549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107558173329352957702614797 40334314998507359138480549)
    ·
      refine ⟨7562684062220129838465103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40334314998507359138480549 7562684062220129838465103)
      ·
        refine ⟨11344026093330194757697655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562684062220129838465103 11344026093330194757697655)
        ·
          refine ⟨17016039139995292136546483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11344026093330194757697655 17016039139995292136546483)
          ·
            refine ⟨25524058709992938204819725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17016039139995292136546483 25524058709992938204819725)
            ·
              refine ⟨9571522016247351826807397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25524058709992938204819725 9571522016247351826807397)
              ·
                refine ⟨1794660378046378467526387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9571522016247351826807397 1794660378046378467526387)
                ·
                  refine ⟨2691990567069567701289581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794660378046378467526387 2691990567069567701289581)
                  ·
                    refine ⟨1009496462651087887983593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691990567069567701289581 1009496462651087887983593)
                    ·
                      rfl

theorem cell22_2948981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2948981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2948981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2948981 prefixEnd_2948981 := by exact prefixLift 2948981
  have htrace : WordTrace (prefixWord ++ tailWord_2948981) baseStart_2948981 baseEnd_2948981 := by
    simpa [prefixWord, tailWord_2948981, baseEnd_2948981] using wordTrace_append hprefix tailTrace_2948981
  have hstable : (prefixWord ++ tailWord_2948981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948981).length < 2 ^ (prefixWord ++ tailWord_2948981).sum := by decide
  have hdescent : baseEnd_2948981 < baseStart_2948981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_2949035 : Nat := 118140960795 + 2949035 * 2 ^ 59
def prefixEnd_2949035 : Nat := 4983230072969 + 3 ^ 40 * 2949035 * 2
def baseEnd_2949035 : Nat := 1009514947954649747133427

theorem tailTrace_2949035 : CollatzResearch.WordTrace tailWord_2949035 prefixEnd_2949035 1009514947954649747133427 := by
  unfold tailWord_2949035
  simp only [CollatzResearch.WordTrace]
  refine ⟨107560142871157324925080559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71706761914104883283387039 107560142871157324925080559)
  ·
    refine ⟨161340214306735987387620839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107560142871157324925080559 161340214306735987387620839)
    ·
      refine ⟨242010321460103981081431259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161340214306735987387620839 242010321460103981081431259)
      ·
        refine ⟨363015482190155971622146889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242010321460103981081431259 363015482190155971622146889)
        ·
          refine ⟨272261611642616978716610167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363015482190155971622146889 272261611642616978716610167)
          ·
            refine ⟨408392417463925468074915251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272261611642616978716610167 408392417463925468074915251)
            ·
              refine ⟨612588626195888202112372877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408392417463925468074915251 612588626195888202112372877)
              ·
                refine ⟨229720734823458075792139829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612588626195888202112372877 229720734823458075792139829)
                ·
                  refine ⟨21536318889699194605513109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229720734823458075792139829 21536318889699194605513109)
                  ·
                    refine ⟨1009514947954649747133427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21536318889699194605513109 1009514947954649747133427)
                    ·
                      rfl

theorem cell22_2949035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_2949035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949035 prefixEnd_2949035 := by exact prefixLift 2949035
  have htrace : WordTrace (prefixWord ++ tailWord_2949035) baseStart_2949035 baseEnd_2949035 := by
    simpa [prefixWord, tailWord_2949035, baseEnd_2949035] using wordTrace_append hprefix tailTrace_2949035
  have hstable : (prefixWord ++ tailWord_2949035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949035).length < 2 ^ (prefixWord ++ tailWord_2949035).sum := by decide
  have hdescent : baseEnd_2949035 < baseStart_2949035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949054 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2949054 : Nat := 118140960795 + 2949054 * 2 ^ 59
def prefixEnd_2949054 : Nat := 4983230072969 + 3 ^ 40 * 2949054 * 2
def baseEnd_2949054 : Nat := 1009521452042940030908369

theorem tailTrace_2949054 : CollatzResearch.WordTrace tailWord_2949054 prefixEnd_2949054 1009521452042940030908369 := by
  unfold tailWord_2949054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445104482261061396252777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71707223905392327446681477 13445104482261061396252777)
  ·
    refine ⟨10083828361695796047189583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13445104482261061396252777 10083828361695796047189583)
    ·
      refine ⟨15125742542543694070784375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083828361695796047189583 15125742542543694070784375)
      ·
        refine ⟨22688613813815541106176563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15125742542543694070784375 22688613813815541106176563)
        ·
          refine ⟨34032920720723311659264845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22688613813815541106176563 34032920720723311659264845)
          ·
            refine ⟨12762345270271241872224317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34032920720723311659264845 12762345270271241872224317)
            ·
              refine ⟨4785879476351715702084119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12762345270271241872224317 4785879476351715702084119)
              ·
                refine ⟨7178819214527573553126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785879476351715702084119 7178819214527573553126179)
                ·
                  refine ⟨10768228821791360329689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7178819214527573553126179 10768228821791360329689269)
                  ·
                    refine ⟨1009521452042940030908369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10768228821791360329689269 1009521452042940030908369)
                    ·
                      rfl

theorem cell22_2949054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2949054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949054 prefixEnd_2949054 := by exact prefixLift 2949054
  have htrace : WordTrace (prefixWord ++ tailWord_2949054) baseStart_2949054 baseEnd_2949054 := by
    simpa [prefixWord, tailWord_2949054, baseEnd_2949054] using wordTrace_append hprefix tailTrace_2949054
  have hstable : (prefixWord ++ tailWord_2949054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949054).length < 2 ^ (prefixWord ++ tailWord_2949054).sum := by decide
  have hdescent : baseEnd_2949054 < baseStart_2949054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949090 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2949090 : Nat := 118140960795 + 2949090 * 2 ^ 59
def prefixEnd_2949090 : Nat := 4983230072969 + 3 ^ 40 * 2949090 * 2
def baseEnd_2949090 : Nat := 336511258526215979002753

theorem tailTrace_2949090 : CollatzResearch.WordTrace tailWord_2949090 prefixEnd_2949090 336511258526215979002753 := by
  unfold tailWord_2949090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890537221489517329583181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71708099257305379545555149 26890537221489517329583181)
  ·
    refine ⟨10083951458058568998593693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26890537221489517329583181 10083951458058568998593693)
    ·
      refine ⟨3781481796771963374472635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10083951458058568998593693 3781481796771963374472635)
      ·
        refine ⟨5672222695157945061708953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781481796771963374472635 5672222695157945061708953)
        ·
          refine ⟨4254167021368458796281715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5672222695157945061708953 4254167021368458796281715)
          ·
            refine ⟨6381250532052688194422573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254167021368458796281715 6381250532052688194422573)
            ·
              refine ⟨2392968949519758072908465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6381250532052688194422573 2392968949519758072908465)
              ·
                refine ⟨1794726712139818554681349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392968949519758072908465 1794726712139818554681349)
                ·
                  refine ⟨336511258526215979002753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794726712139818554681349 336511258526215979002753)
                  ·
                    rfl

theorem cell22_2949090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2949090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949090 prefixEnd_2949090 := by exact prefixLift 2949090
  have htrace : WordTrace (prefixWord ++ tailWord_2949090) baseStart_2949090 baseEnd_2949090 := by
    simpa [prefixWord, tailWord_2949090, baseEnd_2949090] using wordTrace_append hprefix tailTrace_2949090
  have hstable : (prefixWord ++ tailWord_2949090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949090).length < 2 ^ (prefixWord ++ tailWord_2949090).sum := by decide
  have hdescent : baseEnd_2949090 < baseStart_2949090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949101 : List Nat := [1, 5, 1, 4, 1, 1, 2, 7]
def baseStart_2949101 : Nat := 118140960795 + 2949101 * 2 ^ 59
def prefixEnd_2949101 : Nat := 4983230072969 + 3 ^ 40 * 2949101 * 2
def baseEnd_2949101 : Nat := 112170837900383063887025

theorem tailTrace_2949101 : CollatzResearch.WordTrace tailWord_2949101 prefixEnd_2949101 112170837900383063887025 := by
  unfold tailWord_2949101
  simp only [CollatzResearch.WordTrace]
  refine ⟨107562550088918218196983157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71708366725945478797988771 107562550088918218196983157)
  ·
    refine ⟨10083989070836082955967171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107562550088918218196983157 10083989070836082955967171)
    ·
      refine ⟨15125983606254124433950757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083989070836082955967171 15125983606254124433950757)
      ·
        refine ⟨2836121926172648331365767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15125983606254124433950757 2836121926172648331365767)
        ·
          refine ⟨4254182889258972497048651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836121926172648331365767 4254182889258972497048651)
          ·
            refine ⟨6381274333888458745572977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254182889258972497048651 6381274333888458745572977)
            ·
              refine ⟨4785955750416344059179733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6381274333888458745572977 4785955750416344059179733)
              ·
                refine ⟨112170837900383063887025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4785955750416344059179733 112170837900383063887025)
                ·
                  rfl

theorem cell22_2949101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 7].length) (baseStart_2949101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949101 prefixEnd_2949101 := by exact prefixLift 2949101
  have htrace : WordTrace (prefixWord ++ tailWord_2949101) baseStart_2949101 baseEnd_2949101 := by
    simpa [prefixWord, tailWord_2949101, baseEnd_2949101] using wordTrace_append hprefix tailTrace_2949101
  have hstable : (prefixWord ++ tailWord_2949101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949101).length < 2 ^ (prefixWord ++ tailWord_2949101).sum := by decide
  have hdescent : baseEnd_2949101 < baseStart_2949101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949105 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_2949105 : Nat := 118140960795 + 2949105 * 2 ^ 59
def prefixEnd_2949105 : Nat := 4983230072969 + 3 ^ 40 * 2949105 * 2
def baseEnd_2949105 : Nat := 1009538910385192897883213

theorem tailTrace_2949105 : CollatzResearch.WordTrace tailWord_2949105 prefixEnd_2949105 1009538910385192897883213 := by
  unfold tailWord_2949105
  simp only [CollatzResearch.WordTrace]
  refine ⟨107562695980903726880128769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71708463987269151253419179 107562695980903726880128769)
  ·
    refine ⟨80672021985677795160096577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107562695980903726880128769 80672021985677795160096577)
    ·
      refine ⟨60504016489258346370072433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80672021985677795160096577 60504016489258346370072433)
      ·
        refine ⟨45378012366943759777554325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60504016489258346370072433 45378012366943759777554325)
        ·
          refine ⟨2127094329700488739572859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45378012366943759777554325 2127094329700488739572859)
          ·
            refine ⟨3190641494550733109359289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127094329700488739572859 3190641494550733109359289)
            ·
              refine ⟨2392981120913049832019467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190641494550733109359289 2392981120913049832019467)
              ·
                refine ⟨3589471681369574748029201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392981120913049832019467 3589471681369574748029201)
                ·
                  refine ⟨2692103761027181061021901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3589471681369574748029201 2692103761027181061021901)
                  ·
                    refine ⟨1009538910385192897883213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692103761027181061021901 1009538910385192897883213)
                    ·
                      rfl

theorem cell22_2949105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_2949105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949105 prefixEnd_2949105 := by exact prefixLift 2949105
  have htrace : WordTrace (prefixWord ++ tailWord_2949105) baseStart_2949105 baseEnd_2949105 := by
    simpa [prefixWord, tailWord_2949105, baseEnd_2949105] using wordTrace_append hprefix tailTrace_2949105
  have hstable : (prefixWord ++ tailWord_2949105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949105).length < 2 ^ (prefixWord ++ tailWord_2949105).sum := by decide
  have hdescent : baseEnd_2949105 < baseStart_2949105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949189 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_2949189 : Nat := 118140960795 + 2949189 * 2 ^ 59
def prefixEnd_2949189 : Nat := 4983230072969 + 3 ^ 40 * 2949189 * 2
def baseEnd_2949189 : Nat := 1009567665301844678782955

theorem tailTrace_2949189 : CollatzResearch.WordTrace tailWord_2949189 prefixEnd_2949189 1009567665301844678782955 := by
  unfold tailWord_2949189
  simp only [CollatzResearch.WordTrace]
  refine ⟨107565759712599409226186621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71710506475066272817457747 107565759712599409226186621)
  ·
    refine ⟨40337159892224778459819983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107565759712599409226186621 40337159892224778459819983)
    ·
      refine ⟨60505739838337167689729975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40337159892224778459819983 60505739838337167689729975)
      ·
        refine ⟨90758609757505751534594963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60505739838337167689729975 90758609757505751534594963)
        ·
          refine ⟨136137914636258627301892445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90758609757505751534594963 136137914636258627301892445)
          ·
            refine ⟨51051717988596985238209667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136137914636258627301892445 51051717988596985238209667)
            ·
              refine ⟨76577576982895477857314501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51051717988596985238209667 76577576982895477857314501)
              ·
                refine ⟨14358295684292902098246469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76577576982895477857314501 14358295684292902098246469)
                ·
                  refine ⟨2692180440804919143421213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14358295684292902098246469 2692180440804919143421213)
                  ·
                    refine ⟨1009567665301844678782955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692180440804919143421213 1009567665301844678782955)
                    ·
                      rfl

theorem cell22_2949189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_2949189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949189 prefixEnd_2949189 := by exact prefixLift 2949189
  have htrace : WordTrace (prefixWord ++ tailWord_2949189) baseStart_2949189 baseEnd_2949189 := by
    simpa [prefixWord, tailWord_2949189, baseEnd_2949189] using wordTrace_append hprefix tailTrace_2949189
  have hstable : (prefixWord ++ tailWord_2949189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949189).length < 2 ^ (prefixWord ++ tailWord_2949189).sum := by decide
  have hdescent : baseEnd_2949189 < baseStart_2949189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949191 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 4]
def baseStart_2949191 : Nat := 118140960795 + 2949191 * 2 ^ 59
def prefixEnd_2949191 : Nat := 4983230072969 + 3 ^ 40 * 2949191 * 2
def baseEnd_2949191 : Nat := 336522783314239113410983

theorem tailTrace_2949191 : CollatzResearch.WordTrace tailWord_2949191 prefixEnd_2949191 336522783314239113410983 := by
  unfold tailWord_2949191
  simp only [CollatzResearch.WordTrace]
  refine ⟨107565832658592163567759427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71710555105728109045172951 107565832658592163567759427)
  ·
    refine ⟨161348748987888245351639141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107565832658592163567759427 161348748987888245351639141)
    ·
      refine ⟨30252890435229046003432339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161348748987888245351639141 30252890435229046003432339)
      ·
        refine ⟨45379335652843569005148509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30252890435229046003432339 45379335652843569005148509)
        ·
          refine ⟨17017250869816338376930691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45379335652843569005148509 17017250869816338376930691)
          ·
            refine ⟨25525876304724507565396037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17017250869816338376930691 25525876304724507565396037)
            ·
              refine ⟨4786101807135845168511757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25525876304724507565396037 4786101807135845168511757)
              ·
                refine ⟨1794788177675941938191909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4786101807135845168511757 1794788177675941938191909)
                ·
                  refine ⟨336522783314239113410983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794788177675941938191909 336522783314239113410983)
                  ·
                    rfl

theorem cell22_2949191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 4].length) (baseStart_2949191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949191 prefixEnd_2949191 := by exact prefixLift 2949191
  have htrace : WordTrace (prefixWord ++ tailWord_2949191) baseStart_2949191 baseEnd_2949191 := by
    simpa [prefixWord, tailWord_2949191, baseEnd_2949191] using wordTrace_append hprefix tailTrace_2949191
  have hstable : (prefixWord ++ tailWord_2949191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949191).length < 2 ^ (prefixWord ++ tailWord_2949191).sum := by decide
  have hdescent : baseEnd_2949191 < baseStart_2949191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949204 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2949204 : Nat := 118140960795 + 2949204 * 2 ^ 59
def prefixEnd_2949204 : Nat := 4983230072969 + 3 ^ 40 * 2949204 * 2
def baseEnd_2949204 : Nat := 1009572800108389639657909

theorem tailTrace_2949204 : CollatzResearch.WordTrace tailWord_2949204 prefixEnd_2949204 1009572800108389639657909 := by
  unfold tailWord_2949204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53783153403772533393991333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71710871205030044525321777 53783153403772533393991333)
  ·
    refine ⟨10084341263207350011373375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53783153403772533393991333 10084341263207350011373375)
    ·
      refine ⟨15126511894811025017060063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10084341263207350011373375 15126511894811025017060063)
      ·
        refine ⟨22689767842216537525590095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126511894811025017060063 22689767842216537525590095)
        ·
          refine ⟨34034651763324806288385143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22689767842216537525590095 34034651763324806288385143)
          ·
            refine ⟨51051977644987209432577715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34034651763324806288385143 51051977644987209432577715)
            ·
              refine ⟨76577966467480814148866573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51051977644987209432577715 76577966467480814148866573)
              ·
                refine ⟨28716737425305305305824965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76577966467480814148866573 28716737425305305305824965)
                ·
                  refine ⟨5384388267244744744842181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28716737425305305305824965 5384388267244744744842181)
                  ·
                    refine ⟨1009572800108389639657909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384388267244744744842181 1009572800108389639657909)
                    ·
                      rfl

theorem cell22_2949204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2949204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949204 prefixEnd_2949204 := by exact prefixLift 2949204
  have htrace : WordTrace (prefixWord ++ tailWord_2949204) baseStart_2949204 baseEnd_2949204 := by
    simpa [prefixWord, tailWord_2949204, baseEnd_2949204] using wordTrace_append hprefix tailTrace_2949204
  have hstable : (prefixWord ++ tailWord_2949204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949204).length < 2 ^ (prefixWord ++ tailWord_2949204).sum := by decide
  have hdescent : baseEnd_2949204 < baseStart_2949204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949223 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2949223 : Nat := 118140960795 + 2949223 * 2 ^ 59
def prefixEnd_2949223 : Nat := 4983230072969 + 3 ^ 40 * 2949223 * 2
def baseEnd_2949223 : Nat := 1009579304196679923432851

theorem tailTrace_2949223 : CollatzResearch.WordTrace tailWord_2949223 prefixEnd_2949223 1009579304196679923432851 := by
  unfold tailWord_2949223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107566999794476233032924323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71711333196317488688616215 107566999794476233032924323)
  ·
    refine ⟨161350499691714349549386485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107566999794476233032924323 161350499691714349549386485)
    ·
      refine ⟨15126609346098220270254983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161350499691714349549386485 15126609346098220270254983)
      ·
        refine ⟨22689914019147330405382475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126609346098220270254983 22689914019147330405382475)
        ·
          refine ⟨34034871028720995608073713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22689914019147330405382475 34034871028720995608073713)
          ·
            refine ⟨25526153271540746706055285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34034871028720995608073713 25526153271540746706055285)
            ·
              refine ⟨2393076869206945003692683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25526153271540746706055285 2393076869206945003692683)
              ·
                refine ⟨3589615303810417505539025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393076869206945003692683 3589615303810417505539025)
                ·
                  refine ⟨2692211477857813129154269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3589615303810417505539025 2692211477857813129154269)
                  ·
                    refine ⟨1009579304196679923432851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692211477857813129154269 1009579304196679923432851)
                    ·
                      rfl

theorem cell22_2949223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2949223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949223 prefixEnd_2949223 := by exact prefixLift 2949223
  have htrace : WordTrace (prefixWord ++ tailWord_2949223) baseStart_2949223 baseEnd_2949223 := by
    simpa [prefixWord, tailWord_2949223, baseEnd_2949223] using wordTrace_append hprefix tailTrace_2949223
  have hstable : (prefixWord ++ tailWord_2949223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949223).length < 2 ^ (prefixWord ++ tailWord_2949223).sum := by decide
  have hdescent : baseEnd_2949223 < baseStart_2949223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949264 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_2949264 : Nat := 118140960795 + 2949264 * 2 ^ 59
def prefixEnd_2949264 : Nat := 4983230072969 + 3 ^ 40 * 2949264 * 2
def baseEnd_2949264 : Nat := 336531113111523161052575

theorem tailTrace_2949264 : CollatzResearch.WordTrace tailWord_2949264 prefixEnd_2949264 336531113111523161052575 := by
  unfold tailWord_2949264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53784247593663848517583423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71712330124885131356777897 53784247593663848517583423)
  ·
    refine ⟨80676371390495772776375135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53784247593663848517583423 80676371390495772776375135)
    ·
      refine ⟨121014557085743659164562703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80676371390495772776375135 121014557085743659164562703)
      ·
        refine ⟨181521835628615488746844055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121014557085743659164562703 181521835628615488746844055)
        ·
          refine ⟨272282753442923233120266083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181521835628615488746844055 272282753442923233120266083)
          ·
            refine ⟨408424130164384849680399125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272282753442923233120266083 408424130164384849680399125)
            ·
              refine ⟨19144881101455539828768709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 408424130164384849680399125 19144881101455539828768709)
              ·
                refine ⟨3589665206522913717894133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19144881101455539828768709 3589665206522913717894133)
                ·
                  refine ⟨336531113111523161052575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3589665206522913717894133 336531113111523161052575)
                  ·
                    rfl

theorem cell22_2949264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_2949264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949264 prefixEnd_2949264 := by exact prefixLift 2949264
  have htrace : WordTrace (prefixWord ++ tailWord_2949264) baseStart_2949264 baseEnd_2949264 := by
    simpa [prefixWord, tailWord_2949264, baseEnd_2949264] using wordTrace_append hprefix tailTrace_2949264
  have hstable : (prefixWord ++ tailWord_2949264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949264).length < 2 ^ (prefixWord ++ tailWord_2949264).sum := by decide
  have hdescent : baseEnd_2949264 < baseStart_2949264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949281 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 5]
def baseStart_2949281 : Nat := 118140960795 + 2949281 * 2 ^ 59
def prefixEnd_2949281 : Nat := 4983230072969 + 3 ^ 40 * 2949281 * 2
def baseEnd_2949281 : Nat := 336533052927329035160891

theorem tailTrace_2949281 : CollatzResearch.WordTrace tailWord_2949281 prefixEnd_2949281 336533052927329035160891 := by
  unfold tailWord_2949281
  simp only [CollatzResearch.WordTrace]
  refine ⟨107569115228266108938535697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71712743485510739292357131 107569115228266108938535697)
  ·
    refine ⟨80676836421199581703901773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107569115228266108938535697 80676836421199581703901773)
    ·
      refine ⟨30253813657949843138963165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80676836421199581703901773 30253813657949843138963165)
      ·
        refine ⟨11345180121731191177111187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30253813657949843138963165 11345180121731191177111187)
        ·
          refine ⟨17017770182596786765666781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11345180121731191177111187 17017770182596786765666781)
          ·
            refine ⟨6381663818473795037125043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17017770182596786765666781 6381663818473795037125043)
            ·
              refine ⟨9572495727710692555687565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6381663818473795037125043 9572495727710692555687565)
              ·
                refine ⟨3589685897891509708382837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9572495727710692555687565 3589685897891509708382837)
                ·
                  refine ⟨336533052927329035160891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3589685897891509708382837 336533052927329035160891)
                  ·
                    rfl

theorem cell22_2949281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_2949281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949281 prefixEnd_2949281 := by exact prefixLift 2949281
  have htrace : WordTrace (prefixWord ++ tailWord_2949281) baseStart_2949281 baseEnd_2949281 := by
    simpa [prefixWord, tailWord_2949281, baseEnd_2949281] using wordTrace_append hprefix tailTrace_2949281
  have hstable : (prefixWord ++ tailWord_2949281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949281).length < 2 ^ (prefixWord ++ tailWord_2949281).sum := by decide
  have hdescent : baseEnd_2949281 < baseStart_2949281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_2949339 : Nat := 118140960795 + 2949339 * 2 ^ 59
def prefixEnd_2949339 : Nat := 4983230072969 + 3 ^ 40 * 2949339 * 2
def baseEnd_2949339 : Nat := 1009619013367294287532495

theorem tailTrace_2949339 : CollatzResearch.WordTrace tailWord_2949339 prefixEnd_2949339 1009619013367294287532495 := by
  unfold tailWord_2949339
  simp only [CollatzResearch.WordTrace]
  refine ⟨107571230662055984844147071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71714153774703989896098047 107571230662055984844147071)
  ·
    refine ⟨161356845993083977266220607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107571230662055984844147071 161356845993083977266220607)
    ·
      refine ⟨242035268989625965899330911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161356845993083977266220607 242035268989625965899330911)
      ·
        refine ⟨363052903484438948848996367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242035268989625965899330911 363052903484438948848996367)
        ·
          refine ⟨544579355226658423273494551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363052903484438948848996367 544579355226658423273494551)
          ·
            refine ⟨816869032839987634910241827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544579355226658423273494551 816869032839987634910241827)
            ·
              refine ⟨1225303549259981452365362741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816869032839987634910241827 1225303549259981452365362741)
              ·
                refine ⟨114872207743123261159252757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225303549259981452365362741 114872207743123261159252757)
                ·
                  refine ⟨5384634737958902866839973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114872207743123261159252757 5384634737958902866839973)
                  ·
                    refine ⟨1009619013367294287532495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384634737958902866839973 1009619013367294287532495)
                    ·
                      rfl

theorem cell22_2949339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_2949339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949339 prefixEnd_2949339 := by exact prefixLift 2949339
  have htrace : WordTrace (prefixWord ++ tailWord_2949339) baseStart_2949339 baseEnd_2949339 := by
    simpa [prefixWord, tailWord_2949339, baseEnd_2949339] using wordTrace_append hprefix tailTrace_2949339
  have hstable : (prefixWord ++ tailWord_2949339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949339).length < 2 ^ (prefixWord ++ tailWord_2949339).sum := by decide
  have hdescent : baseEnd_2949339 < baseStart_2949339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949405 : List Nat := [1, 4, 2, 3, 2, 2, 2, 6]
def baseStart_2949405 : Nat := 118140960795 + 2949405 * 2 ^ 59
def prefixEnd_2949405 : Nat := 4983230072969 + 3 ^ 40 * 2949405 * 2
def baseEnd_2949405 : Nat := 112182400724010235042477

theorem tailTrace_2949405 : CollatzResearch.WordTrace tailWord_2949405 prefixEnd_2949405 112182400724010235042477 := by
  unfold tailWord_2949405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107573637879816878116049669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71715758586544585410699779 107573637879816878116049669)
  ·
    refine ⟨20170057102465664646759313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107573637879816878116049669 20170057102465664646759313)
    ·
      refine ⟨15127542826849248485069485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20170057102465664646759313 15127542826849248485069485)
      ·
        refine ⟨5672828560068468181901057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15127542826849248485069485 5672828560068468181901057)
        ·
          refine ⟨4254621420051351136425793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5672828560068468181901057 4254621420051351136425793)
          ·
            refine ⟨3190966065038513352319345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254621420051351136425793 3190966065038513352319345)
            ·
              refine ⟨2393224548778885014239509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190966065038513352319345 2393224548778885014239509)
              ·
                refine ⟨112182400724010235042477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2393224548778885014239509 112182400724010235042477)
                ·
                  rfl

theorem cell22_2949405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 6].length) (baseStart_2949405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949405 prefixEnd_2949405 := by exact prefixLift 2949405
  have htrace : WordTrace (prefixWord ++ tailWord_2949405) baseStart_2949405 baseEnd_2949405 := by
    simpa [prefixWord, tailWord_2949405, baseEnd_2949405] using wordTrace_append hprefix tailTrace_2949405
  have hstable : (prefixWord ++ tailWord_2949405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949405).length < 2 ^ (prefixWord ++ tailWord_2949405).sum := by decide
  have hdescent : baseEnd_2949405 < baseStart_2949405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949420 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_2949420 : Nat := 118140960795 + 2949420 * 2 ^ 59
def prefixEnd_2949420 : Nat := 4983230072969 + 3 ^ 40 * 2949420 * 2
def baseEnd_2949420 : Nat := 1009646741322637076257247

theorem tailTrace_2949420 : CollatzResearch.WordTrace tailWord_2949420 prefixEnd_2949420 1009646741322637076257247 := by
  unfold tailWord_2949420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53787092487381267838922857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71716123316508357118563809 53787092487381267838922857)
  ·
    refine ⟨40340319365535950879192143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53787092487381267838922857 40340319365535950879192143)
    ·
      refine ⟨60510479048303926318788215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40340319365535950879192143 60510479048303926318788215)
      ·
        refine ⟨90765718572455889478182323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60510479048303926318788215 90765718572455889478182323)
        ·
          refine ⟨136148577858683834217273485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90765718572455889478182323 136148577858683834217273485)
          ·
            refine ⟨51055716697006437831477557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136148577858683834217273485 51055716697006437831477557)
            ·
              refine ⟨4786473440344353546701021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51055716697006437831477557 4786473440344353546701021)
              ·
                refine ⟨1794927540129132580012883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4786473440344353546701021 1794927540129132580012883)
                ·
                  refine ⟨2692391310193698870019325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794927540129132580012883 2692391310193698870019325)
                  ·
                    refine ⟨1009646741322637076257247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692391310193698870019325 1009646741322637076257247)
                    ·
                      rfl

theorem cell22_2949420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_2949420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949420 prefixEnd_2949420 := by exact prefixLift 2949420
  have htrace : WordTrace (prefixWord ++ tailWord_2949420) baseStart_2949420 baseEnd_2949420 := by
    simpa [prefixWord, tailWord_2949420, baseEnd_2949420] using wordTrace_append hprefix tailTrace_2949420
  have hstable : (prefixWord ++ tailWord_2949420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949420).length < 2 ^ (prefixWord ++ tailWord_2949420).sum := by decide
  have hdescent : baseEnd_2949420 < baseStart_2949420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949544 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2949544 : Nat := 118140960795 + 2949544 * 2 ^ 59
def prefixEnd_2949544 : Nat := 4983230072969 + 3 ^ 40 * 2949544 * 2
def baseEnd_2949544 : Nat := 1009689189056742086156867

theorem tailTrace_2949544 : CollatzResearch.WordTrace tailWord_2949544 prefixEnd_2949544 1009689189056742086156867 := by
  unfold tailWord_2949544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53789353813156652427679843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71719138417542203236906457 53789353813156652427679843)
  ·
    refine ⟨80684030719734978641519765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53789353813156652427679843 80684030719734978641519765)
    ·
      refine ⟨3782063939987577123821239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80684030719734978641519765 3782063939987577123821239)
      ·
        refine ⟨5673095909981365685731859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782063939987577123821239 5673095909981365685731859)
        ·
          refine ⟨8509643864972048528597789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673095909981365685731859 8509643864972048528597789)
          ·
            refine ⟨3191116449364518198224171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8509643864972048528597789 3191116449364518198224171)
            ·
              refine ⟨4786674674046777297336257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191116449364518198224171 4786674674046777297336257)
              ·
                refine ⟨3590006005535082973002193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786674674046777297336257 3590006005535082973002193)
                ·
                  refine ⟨2692504504151312229751645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590006005535082973002193 2692504504151312229751645)
                  ·
                    refine ⟨1009689189056742086156867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692504504151312229751645 1009689189056742086156867)
                    ·
                      rfl

theorem cell22_2949544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2949544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949544 prefixEnd_2949544 := by exact prefixLift 2949544
  have htrace : WordTrace (prefixWord ++ tailWord_2949544) baseStart_2949544 baseEnd_2949544 := by
    simpa [prefixWord, tailWord_2949544, baseEnd_2949544] using wordTrace_append hprefix tailTrace_2949544
  have hstable : (prefixWord ++ tailWord_2949544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949544).length < 2 ^ (prefixWord ++ tailWord_2949544).sum := by decide
  have hdescent : baseEnd_2949544 < baseStart_2949544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949589 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2949589 : Nat := 118140960795 + 2949589 * 2 ^ 59
def prefixEnd_2949589 : Nat := 4983230072969 + 3 ^ 40 * 2949589 * 2
def baseEnd_2949589 : Nat := 1009704593476376968781729

theorem tailTrace_2949589 : CollatzResearch.WordTrace tailWord_2949589 prefixEnd_2949589 1009704593476376968781729 := by
  unfold tailWord_2949589
  simp only [CollatzResearch.WordTrace]
  refine ⟨107580348911150277540747821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71720232607433518360498547 107580348911150277540747821)
  ·
    refine ⟨40342630841681354077780433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107580348911150277540747821 40342630841681354077780433)
    ·
      refine ⟨30256973131261015558335325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40342630841681354077780433 30256973131261015558335325)
      ·
        refine ⟨11346364924222880834375747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30256973131261015558335325 11346364924222880834375747)
        ·
          refine ⟨17019547386334321251563621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346364924222880834375747 17019547386334321251563621)
          ·
            refine ⟨3191165134937685234668179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17019547386334321251563621 3191165134937685234668179)
            ·
              refine ⟨4786747702406527852002269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191165134937685234668179 4786747702406527852002269)
              ·
                refine ⟨1795030388402447944500851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4786747702406527852002269 1795030388402447944500851)
                ·
                  refine ⟨2692545582603671916751277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795030388402447944500851 2692545582603671916751277)
                  ·
                    refine ⟨1009704593476376968781729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692545582603671916751277 1009704593476376968781729)
                    ·
                      rfl

theorem cell22_2949589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2949589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949589 prefixEnd_2949589 := by exact prefixLift 2949589
  have htrace : WordTrace (prefixWord ++ tailWord_2949589) baseStart_2949589 baseEnd_2949589 := by
    simpa [prefixWord, tailWord_2949589, baseEnd_2949589] using wordTrace_append hprefix tailTrace_2949589
  have hstable : (prefixWord ++ tailWord_2949589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949589).length < 2 ^ (prefixWord ++ tailWord_2949589).sum := by decide
  have hdescent : baseEnd_2949589 < baseStart_2949589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949628 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2949628 : Nat := 118140960795 + 2949628 * 2 ^ 59
def prefixEnd_2949628 : Nat := 4983230072969 + 3 ^ 40 * 2949628 * 2
def baseEnd_2949628 : Nat := 1009717943973393867056609

theorem tailTrace_2949628 : CollatzResearch.WordTrace tailWord_2949628 prefixEnd_2949628 1009717943973393867056609 := by
  unfold tailWord_2949628
  simp only [CollatzResearch.WordTrace]
  refine ⟨53790885679004493600708769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71721180905339324800945025 53790885679004493600708769)
  ·
    refine ⟨40343164259253370200531577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53790885679004493600708769 40343164259253370200531577)
    ·
      refine ⟨30257373194440027650398683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40343164259253370200531577 30257373194440027650398683)
      ·
        refine ⟨45386059791660041475598025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30257373194440027650398683 45386059791660041475598025)
        ·
          refine ⟨34039544843745031106698519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45386059791660041475598025 34039544843745031106698519)
          ·
            refine ⟨51059317265617546660047779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34039544843745031106698519 51059317265617546660047779)
            ·
              refine ⟨76588975898426319990071669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51059317265617546660047779 76588975898426319990071669)
              ·
                refine ⟨7180216490477467499069219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76588975898426319990071669 7180216490477467499069219)
                ·
                  refine ⟨10770324735716201248603829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180216490477467499069219 10770324735716201248603829)
                  ·
                    refine ⟨1009717943973393867056609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10770324735716201248603829 1009717943973393867056609)
                    ·
                      rfl

theorem cell22_2949628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2949628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949628 prefixEnd_2949628 := by exact prefixLift 2949628
  have htrace : WordTrace (prefixWord ++ tailWord_2949628) baseStart_2949628 baseEnd_2949628 := by
    simpa [prefixWord, tailWord_2949628, baseEnd_2949628] using wordTrace_append hprefix tailTrace_2949628
  have hstable : (prefixWord ++ tailWord_2949628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949628).length < 2 ^ (prefixWord ++ tailWord_2949628).sum := by decide
  have hdescent : baseEnd_2949628 < baseStart_2949628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949660 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2949660 : Nat := 118140960795 + 2949660 * 2 ^ 59
def prefixEnd_2949660 : Nat := 4983230072969 + 3 ^ 40 * 2949660 * 2
def baseEnd_2949660 : Nat := 1009728898227356450256511

theorem tailTrace_2949660 : CollatzResearch.WordTrace tailWord_2949660 prefixEnd_2949660 1009728898227356450256511 := by
  unfold tailWord_2949660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53791469246946528333291217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71721958995928704444388289 53791469246946528333291217)
  ·
    refine ⟨40343601935209896249968413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53791469246946528333291217 40343601935209896249968413)
    ·
      refine ⟨15128850725703711093738155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40343601935209896249968413 15128850725703711093738155)
      ·
        refine ⟨22693276088555566640607233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128850725703711093738155 22693276088555566640607233)
        ·
          refine ⟨17019957066416674980455425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22693276088555566640607233 17019957066416674980455425)
          ·
            refine ⟨12764967799812506235341569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17019957066416674980455425 12764967799812506235341569)
            ·
              refine ⟨9573725849859379676506177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764967799812506235341569 9573725849859379676506177)
              ·
                refine ⟨7180294387394534757379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573725849859379676506177 7180294387394534757379633)
                ·
                  refine ⟨5385220790545901068034725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180294387394534757379633 5385220790545901068034725)
                  ·
                    refine ⟨1009728898227356450256511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385220790545901068034725 1009728898227356450256511)
                    ·
                      rfl

theorem cell22_2949660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2949660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949660 prefixEnd_2949660 := by exact prefixLift 2949660
  have htrace : WordTrace (prefixWord ++ tailWord_2949660) baseStart_2949660 baseEnd_2949660 := by
    simpa [prefixWord, tailWord_2949660, baseEnd_2949660] using wordTrace_append hprefix tailTrace_2949660
  have hstable : (prefixWord ++ tailWord_2949660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949660).length < 2 ^ (prefixWord ++ tailWord_2949660).sum := by decide
  have hdescent : baseEnd_2949660 < baseStart_2949660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949688 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_2949688 : Nat := 118140960795 + 2949688 * 2 ^ 59
def prefixEnd_2949688 : Nat := 4983230072969 + 3 ^ 40 * 2949688 * 2
def baseEnd_2949688 : Nat := 1009738483199573710556425

theorem tailTrace_2949688 : CollatzResearch.WordTrace tailWord_2949688 prefixEnd_2949688 1009738483199573710556425 := by
  unfold tailWord_2949688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53791979868895808724300859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71722639825194411632401145 53791979868895808724300859)
  ·
    refine ⟨80687969803343713086451289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53791979868895808724300859 80687969803343713086451289)
    ·
      refine ⟨60515977352507784814838467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80687969803343713086451289 60515977352507784814838467)
      ·
        refine ⟨90773966028761677222257701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60515977352507784814838467 90773966028761677222257701)
        ·
          refine ⟨17020118630392814479173319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90773966028761677222257701 17020118630392814479173319)
          ·
            refine ⟨25530177945589221718759979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020118630392814479173319 25530177945589221718759979)
            ·
              refine ⟨38295266918383832578139969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530177945589221718759979 38295266918383832578139969)
              ·
                refine ⟨28721450188787874433604977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38295266918383832578139969 28721450188787874433604977)
                ·
                  refine ⟨21541087641590905825203733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28721450188787874433604977 21541087641590905825203733)
                  ·
                    refine ⟨1009738483199573710556425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21541087641590905825203733 1009738483199573710556425)
                    ·
                      rfl

theorem cell22_2949688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_2949688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949688 prefixEnd_2949688 := by exact prefixLift 2949688
  have htrace : WordTrace (prefixWord ++ tailWord_2949688) baseStart_2949688 baseEnd_2949688 := by
    simpa [prefixWord, tailWord_2949688, baseEnd_2949688] using wordTrace_append hprefix tailTrace_2949688
  have hstable : (prefixWord ++ tailWord_2949688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949688).length < 2 ^ (prefixWord ++ tailWord_2949688).sum := by decide
  have hdescent : baseEnd_2949688 < baseStart_2949688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949690 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_2949690 : Nat := 118140960795 + 2949690 * 2 ^ 59
def prefixEnd_2949690 : Nat := 4983230072969 + 3 ^ 40 * 2949690 * 2
def baseEnd_2949690 : Nat := 1009739167840446372006419

theorem tailTrace_2949690 : CollatzResearch.WordTrace tailWord_2949690 prefixEnd_2949690 1009739167840446372006419 := by
  unfold tailWord_2949690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896008170946092947543631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71722688455856247860116349 26896008170946092947543631)
  ·
    refine ⟨40344012256419139421315447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26896008170946092947543631 40344012256419139421315447)
    ·
      refine ⟨60516018384628709131973171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40344012256419139421315447 60516018384628709131973171)
      ·
        refine ⟨90774027576943063697959757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60516018384628709131973171 90774027576943063697959757)
        ·
          refine ⟨34040260341353648886734909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90774027576943063697959757 34040260341353648886734909)
          ·
            refine ⟨12765097628007618332525591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34040260341353648886734909 12765097628007618332525591)
            ·
              refine ⟨19147646442011427498788387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765097628007618332525591 19147646442011427498788387)
              ·
                refine ⟨28721469663017141248182581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147646442011427498788387 28721469663017141248182581)
                ·
                  refine ⟨2692637780907856992017117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28721469663017141248182581 2692637780907856992017117)
                  ·
                    refine ⟨1009739167840446372006419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692637780907856992017117 1009739167840446372006419)
                    ·
                      rfl

theorem cell22_2949690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_2949690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949690 prefixEnd_2949690 := by exact prefixLift 2949690
  have htrace : WordTrace (prefixWord ++ tailWord_2949690) baseStart_2949690 baseEnd_2949690 := by
    simpa [prefixWord, tailWord_2949690, baseEnd_2949690] using wordTrace_append hprefix tailTrace_2949690
  have hstable : (prefixWord ++ tailWord_2949690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949690).length < 2 ^ (prefixWord ++ tailWord_2949690).sum := by decide
  have hdescent : baseEnd_2949690 < baseStart_2949690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949700 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2949700 : Nat := 118140960795 + 2949700 * 2 ^ 59
def prefixEnd_2949700 : Nat := 4983230072969 + 3 ^ 40 * 2949700 * 2
def baseEnd_2949700 : Nat := 1009742591044809679256389

theorem tailTrace_2949700 : CollatzResearch.WordTrace tailWord_2949700 prefixEnd_2949700 1009742591044809679256389 := by
  unfold tailWord_2949700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792198706874071749019277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71722931609165428998692369 53792198706874071749019277)
  ·
    refine ⟨20172074515077776905882229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53792198706874071749019277 20172074515077776905882229)
    ·
      refine ⟨1891131985788541584926459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20172074515077776905882229 1891131985788541584926459)
      ·
        refine ⟨2836697978682812377389689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891131985788541584926459 2836697978682812377389689)
        ·
          refine ⟨2127523484012109283042267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836697978682812377389689 2127523484012109283042267)
          ·
            refine ⟨3191285226018163924563401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127523484012109283042267 3191285226018163924563401)
            ·
              refine ⟨2393463919513622943422551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191285226018163924563401 2393463919513622943422551)
              ·
                refine ⟨3590195879270434415133827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393463919513622943422551 3590195879270434415133827)
                ·
                  refine ⟨5385293818905651622700741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590195879270434415133827 5385293818905651622700741)
                  ·
                    refine ⟨1009742591044809679256389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385293818905651622700741 1009742591044809679256389)
                    ·
                      rfl

theorem cell22_2949700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2949700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949700 prefixEnd_2949700 := by exact prefixLift 2949700
  have htrace : WordTrace (prefixWord ++ tailWord_2949700) baseStart_2949700 baseEnd_2949700 := by
    simpa [prefixWord, tailWord_2949700, baseEnd_2949700] using wordTrace_append hprefix tailTrace_2949700
  have hstable : (prefixWord ++ tailWord_2949700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949700).length < 2 ^ (prefixWord ++ tailWord_2949700).sum := by decide
  have hdescent : baseEnd_2949700 < baseStart_2949700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949707 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 1, 3]
def baseStart_2949707 : Nat := 118140960795 + 2949707 * 2 ^ 59
def prefixEnd_2949707 : Nat := 4983230072969 + 3 ^ 40 * 2949707 * 2
def baseEnd_2949707 : Nat := 1009744987287863994331367

theorem tailTrace_2949707 : CollatzResearch.WordTrace tailWord_2949707 prefixEnd_2949707 1009744987287863994331367 := by
  unfold tailWord_2949707
  simp only [CollatzResearch.WordTrace]
  refine ⟨107584652724722783693543375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71723101816481855795695583 107584652724722783693543375)
  ·
    refine ⟨161376979087084175540315063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107584652724722783693543375 161376979087084175540315063)
    ·
      refine ⟨242065468630626263310472595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161376979087084175540315063 242065468630626263310472595)
      ·
        refine ⟨363098202945939394965708893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242065468630626263310472595 363098202945939394965708893)
        ·
          refine ⟨136161826104727273112140835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363098202945939394965708893 136161826104727273112140835)
          ·
            refine ⟨204242739157090909668211253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136161826104727273112140835 204242739157090909668211253)
            ·
              refine ⟨19147756795977272781394805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204242739157090909668211253 19147756795977272781394805)
              ·
                refine ⟨1795102199622869323255763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19147756795977272781394805 1795102199622869323255763)
                ·
                  refine ⟨2692653299434303984883645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795102199622869323255763 2692653299434303984883645)
                  ·
                    refine ⟨1009744987287863994331367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692653299434303984883645 1009744987287863994331367)
                    ·
                      rfl

theorem cell22_2949707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 3].length) (baseStart_2949707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949707 prefixEnd_2949707 := by exact prefixLift 2949707
  have htrace : WordTrace (prefixWord ++ tailWord_2949707) baseStart_2949707 baseEnd_2949707 := by
    simpa [prefixWord, tailWord_2949707, baseEnd_2949707] using wordTrace_append hprefix tailTrace_2949707
  have hstable : (prefixWord ++ tailWord_2949707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949707).length < 2 ^ (prefixWord ++ tailWord_2949707).sum := by decide
  have hdescent : baseEnd_2949707 < baseStart_2949707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949720 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_2949720 : Nat := 118140960795 + 2949720 * 2 ^ 59
def prefixEnd_2949720 : Nat := 4983230072969 + 3 ^ 40 * 2949720 * 2
def baseEnd_2949720 : Nat := 336583145817845431252109

theorem tailTrace_2949720 : CollatzResearch.WordTrace tailWord_2949720 prefixEnd_2949720 336583145817845431252109 := by
  unfold tailWord_2949720
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792563436837843456883307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71723417915783791275844409 53792563436837843456883307)
  ·
    refine ⟨80688845155256765185324961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53792563436837843456883307 80688845155256765185324961)
    ·
      refine ⟨60516633866442573888993721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80688845155256765185324961 60516633866442573888993721)
      ·
        refine ⟨45387475399831930416745291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60516633866442573888993721 45387475399831930416745291)
        ·
          refine ⟨68081213099747895625117937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45387475399831930416745291 68081213099747895625117937)
          ·
            refine ⟨51060909824810921718838453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68081213099747895625117937 51060909824810921718838453)
            ·
              refine ⟨4786960296076023911141105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51060909824810921718838453 4786960296076023911141105)
              ·
                refine ⟨3590220222057017933355829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786960296076023911141105 3590220222057017933355829)
                ·
                  refine ⟨336583145817845431252109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3590220222057017933355829 336583145817845431252109)
                  ·
                    rfl

theorem cell22_2949720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_2949720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949720 prefixEnd_2949720 := by exact prefixLift 2949720
  have htrace : WordTrace (prefixWord ++ tailWord_2949720) baseStart_2949720 baseEnd_2949720 := by
    simpa [prefixWord, tailWord_2949720, baseEnd_2949720] using wordTrace_append hprefix tailTrace_2949720
  have hstable : (prefixWord ++ tailWord_2949720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949720).length < 2 ^ (prefixWord ++ tailWord_2949720).sum := by decide
  have hdescent : baseEnd_2949720 < baseStart_2949720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949724 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2949724 : Nat := 118140960795 + 2949724 * 2 ^ 59
def prefixEnd_2949724 : Nat := 4983230072969 + 3 ^ 40 * 2949724 * 2
def baseEnd_2949724 : Nat := 1009750806735281616656315

theorem tailTrace_2949724 : CollatzResearch.WordTrace tailWord_2949724 prefixEnd_2949724 1009750806735281616656315 := by
  unfold tailWord_2949724
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792636382830597798456113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71723515177107463731274817 53792636382830597798456113)
  ·
    refine ⟨40344477287122948348842085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53792636382830597798456113 40344477287122948348842085)
    ·
      refine ⟨7564589491335552815407891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40344477287122948348842085 7564589491335552815407891)
      ·
        refine ⟨11346884237003329223111837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564589491335552815407891 11346884237003329223111837)
        ·
          refine ⟨4255081588876248458666939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11346884237003329223111837 4255081588876248458666939)
          ·
            refine ⟨6382622383314372688000409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255081588876248458666939 6382622383314372688000409)
            ·
              refine ⟨4786966787485779516000307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382622383314372688000409 4786966787485779516000307)
              ·
                refine ⟨7180450181228669274000461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786966787485779516000307 7180450181228669274000461)
                ·
                  refine ⟨2692668817960750977750173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7180450181228669274000461 2692668817960750977750173)
                  ·
                    refine ⟨1009750806735281616656315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692668817960750977750173 1009750806735281616656315)
                    ·
                      rfl

theorem cell22_2949724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2949724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949724 prefixEnd_2949724 := by exact prefixLift 2949724
  have htrace : WordTrace (prefixWord ++ tailWord_2949724) baseStart_2949724 baseEnd_2949724 := by
    simpa [prefixWord, tailWord_2949724, baseEnd_2949724] using wordTrace_append hprefix tailTrace_2949724
  have hstable : (prefixWord ++ tailWord_2949724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949724).length < 2 ^ (prefixWord ++ tailWord_2949724).sum := by decide
  have hdescent : baseEnd_2949724 < baseStart_2949724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949844 : List Nat := [2, 4, 1, 3, 2, 2, 1, 7]
def baseStart_2949844 : Nat := 118140960795 + 2949844 * 2 ^ 59
def prefixEnd_2949844 : Nat := 4983230072969 + 3 ^ 40 * 2949844 * 2
def baseEnd_2949844 : Nat := 112199098354182367072883

theorem tailTrace_2949844 : CollatzResearch.WordTrace tailWord_2949844 prefixEnd_2949844 112199098354182367072883 := by
  unfold tailWord_2949844
  simp only [CollatzResearch.WordTrace]
  refine ⟨53794824762613228045640293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71726433016817637394187057 53794824762613228045640293)
  ·
    refine ⟨10086529642989980258557555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53794824762613228045640293 10086529642989980258557555)
    ·
      refine ⟨15129794464484970387836333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10086529642989980258557555 15129794464484970387836333)
      ·
        refine ⟨5673672924181863895438625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15129794464484970387836333 5673672924181863895438625)
        ·
          refine ⟨4255254693136397921578969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5673672924181863895438625 4255254693136397921578969)
          ·
            refine ⟨3191441019852298441184227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255254693136397921578969 3191441019852298441184227)
            ·
              refine ⟨4787161529778447661776341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191441019852298441184227 4787161529778447661776341)
              ·
                refine ⟨112199098354182367072883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4787161529778447661776341 112199098354182367072883)
                ·
                  rfl

theorem cell22_2949844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_2949844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949844 prefixEnd_2949844 := by exact prefixLift 2949844
  have htrace : WordTrace (prefixWord ++ tailWord_2949844) baseStart_2949844 baseEnd_2949844 := by
    simpa [prefixWord, tailWord_2949844, baseEnd_2949844] using wordTrace_append hprefix tailTrace_2949844
  have hstable : (prefixWord ++ tailWord_2949844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949844).length < 2 ^ (prefixWord ++ tailWord_2949844).sum := by decide
  have hdescent : baseEnd_2949844 < baseStart_2949844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949859 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 3, 3]
def baseStart_2949859 : Nat := 118140960795 + 2949859 * 2 ^ 59
def prefixEnd_2949859 : Nat := 4983230072969 + 3 ^ 40 * 2949859 * 2
def baseEnd_2949859 : Nat := 1009797019994186264530901

theorem tailTrace_2949859 : CollatzResearch.WordTrace tailWord_2949859 prefixEnd_2949859 1009797019994186264530901 := by
  unfold tailWord_2949859
  simp only [CollatzResearch.WordTrace]
  refine ⟨107590196620172113653076631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71726797746781409102051087 107590196620172113653076631)
  ·
    refine ⟨161385294930258170479614947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107590196620172113653076631 161385294930258170479614947)
    ·
      refine ⟨242077942395387255719422421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161385294930258170479614947 242077942395387255719422421)
      ·
        refine ⟨5673701774891888805923963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 242077942395387255719422421 5673701774891888805923963)
        ·
          refine ⟨8510552662337833208885945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673701774891888805923963 8510552662337833208885945)
          ·
            refine ⟨6382914496753374906664459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8510552662337833208885945 6382914496753374906664459)
            ·
              refine ⟨9574371745130062359996689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382914496753374906664459 9574371745130062359996689)
              ·
                refine ⟨7180778808847546769997517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9574371745130062359996689 7180778808847546769997517)
                ·
                  refine ⟨2692792053317830038749069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7180778808847546769997517 2692792053317830038749069)
                  ·
                    refine ⟨1009797019994186264530901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692792053317830038749069 1009797019994186264530901)
                    ·
                      rfl

theorem cell22_2949859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].length) (baseStart_2949859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949859 prefixEnd_2949859 := by exact prefixLift 2949859
  have htrace : WordTrace (prefixWord ++ tailWord_2949859) baseStart_2949859 baseEnd_2949859 := by
    simpa [prefixWord, tailWord_2949859, baseEnd_2949859] using wordTrace_append hprefix tailTrace_2949859
  have hstable : (prefixWord ++ tailWord_2949859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949859).length < 2 ^ (prefixWord ++ tailWord_2949859).sum := by decide
  have hdescent : baseEnd_2949859 < baseStart_2949859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949919 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 1, 4]
def baseStart_2949919 : Nat := 118140960795 + 2949919 * 2 ^ 59
def prefixEnd_2949919 : Nat := 4983230072969 + 3 ^ 40 * 2949919 * 2
def baseEnd_2949919 : Nat := 1009817559220366108030717

theorem tailTrace_2949919 : CollatzResearch.WordTrace tailWord_2949919 prefixEnd_2949919 1009817559220366108030717 := by
  unfold tailWord_2949919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107592384999954743900260811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71728256666636495933507207 107592384999954743900260811)
  ·
    refine ⟨161388577499932115850391217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107592384999954743900260811 161388577499932115850391217)
    ·
      refine ⟨121041433124949086887793413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161388577499932115850391217 121041433124949086887793413)
      ·
        refine ⟨22695268710927953791461265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121041433124949086887793413 22695268710927953791461265)
        ·
          refine ⟨17021451533195965343595949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22695268710927953791461265 17021451533195965343595949)
          ·
            refine ⟨6383044324948487003848481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17021451533195965343595949 6383044324948487003848481)
            ·
              refine ⟨4787283243711365252886361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6383044324948487003848481 4787283243711365252886361)
              ·
                refine ⟨3590462432783523939664771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4787283243711365252886361 3590462432783523939664771)
                ·
                  refine ⟨5385693649175285909497157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590462432783523939664771 5385693649175285909497157)
                  ·
                    refine ⟨1009817559220366108030717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385693649175285909497157 1009817559220366108030717)
                    ·
                      rfl

theorem cell22_2949919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_2949919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949919 prefixEnd_2949919 := by exact prefixLift 2949919
  have htrace : WordTrace (prefixWord ++ tailWord_2949919) baseStart_2949919 baseEnd_2949919 := by
    simpa [prefixWord, tailWord_2949919, baseEnd_2949919] using wordTrace_append hprefix tailTrace_2949919
  have hstable : (prefixWord ++ tailWord_2949919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949919).length < 2 ^ (prefixWord ++ tailWord_2949919).sum := by decide
  have hdescent : baseEnd_2949919 < baseStart_2949919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949932 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_2949932 : Nat := 118140960795 + 2949932 * 2 ^ 59
def prefixEnd_2949932 : Nat := 4983230072969 + 3 ^ 40 * 2949932 * 2
def baseEnd_2949932 : Nat := 1009822009386038407455677

theorem tailTrace_2949932 : CollatzResearch.WordTrace tailWord_2949932 prefixEnd_2949932 1009822009386038407455677 := by
  unfold tailWord_2949932
  simp only [CollatzResearch.WordTrace]
  refine ⟨53796429574453823560242025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71728572765938431413656033 53796429574453823560242025)
  ·
    refine ⟨40347322180840367670181519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53796429574453823560242025 40347322180840367670181519)
    ·
      refine ⟨60520983271260551505272279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40347322180840367670181519 60520983271260551505272279)
      ·
        refine ⟨90781474906890827257908419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60520983271260551505272279 90781474906890827257908419)
        ·
          refine ⟨136172212360336240886862629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90781474906890827257908419 136172212360336240886862629)
          ·
            refine ⟨25532289817563045166286743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136172212360336240886862629 25532289817563045166286743)
            ·
              refine ⟨38298434726344567749430115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25532289817563045166286743 38298434726344567749430115)
              ·
                refine ⟨57447652089516851624145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38298434726344567749430115 57447652089516851624145173)
                ·
                  refine ⟨2692858691696102419881805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57447652089516851624145173 2692858691696102419881805)
                  ·
                    refine ⟨1009822009386038407455677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692858691696102419881805 1009822009386038407455677)
                    ·
                      rfl

theorem cell22_2949932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_2949932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949932 prefixEnd_2949932 := by exact prefixLift 2949932
  have htrace : WordTrace (prefixWord ++ tailWord_2949932) baseStart_2949932 baseEnd_2949932 := by
    simpa [prefixWord, tailWord_2949932, baseEnd_2949932] using wordTrace_append hprefix tailTrace_2949932
  have hstable : (prefixWord ++ tailWord_2949932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949932).length < 2 ^ (prefixWord ++ tailWord_2949932).sum := by decide
  have hdescent : baseEnd_2949932 < baseStart_2949932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949951 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 4]
def baseStart_2949951 : Nat := 118140960795 + 2949951 * 2 ^ 59
def prefixEnd_2949951 : Nat := 4983230072969 + 3 ^ 40 * 2949951 * 2
def baseEnd_2949951 : Nat := 336609504491442897076873

theorem tailTrace_2949951 : CollatzResearch.WordTrace tailWord_2949951 prefixEnd_2949951 336609504491442897076873 := by
  unfold tailWord_2949951
  simp only [CollatzResearch.WordTrace]
  refine ⟨107593552135838813365425707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71729034757225875576950471 107593552135838813365425707)
  ·
    refine ⟨161390328203758220048138561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107593552135838813365425707 161390328203758220048138561)
    ·
      refine ⟨121042746152818665036103921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161390328203758220048138561 121042746152818665036103921)
      ·
        refine ⟨90782059614613998777077941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121042746152818665036103921 90782059614613998777077941)
        ·
          refine ⟨8510818088870062385351057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90782059614613998777077941 8510818088870062385351057)
          ·
            refine ⟨6383113566652546789013293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8510818088870062385351057 6383113566652546789013293)
            ·
              refine ⟨2393667587494705045879985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6383113566652546789013293 2393667587494705045879985)
              ·
                refine ⟨1795250690621028784409989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393667587494705045879985 1795250690621028784409989)
                ·
                  refine ⟨336609504491442897076873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795250690621028784409989 336609504491442897076873)
                  ·
                    rfl

theorem cell22_2949951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 4].length) (baseStart_2949951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2949951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2949951 prefixEnd_2949951 := by exact prefixLift 2949951
  have htrace : WordTrace (prefixWord ++ tailWord_2949951) baseStart_2949951 baseEnd_2949951 := by
    simpa [prefixWord, tailWord_2949951, baseEnd_2949951] using wordTrace_append hprefix tailTrace_2949951
  have hstable : (prefixWord ++ tailWord_2949951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949951).length < 2 ^ (prefixWord ++ tailWord_2949951).sum := by decide
  have hdescent : baseEnd_2949951 < baseStart_2949951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950024 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_2950024 : Nat := 118140960795 + 2950024 * 2 ^ 59
def prefixEnd_2950024 : Nat := 4983230072969 + 3 ^ 40 * 2950024 * 2
def baseEnd_2950024 : Nat := 336617834288726944718465

theorem tailTrace_2950024 : CollatzResearch.WordTrace tailWord_2950024 prefixEnd_2950024 336617834288726944718465 := by
  unfold tailWord_2950024
  simp only [CollatzResearch.WordTrace]
  refine ⟨53798107332287173416416563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71730809776382897888555417 53798107332287173416416563)
  ·
    refine ⟨80697160998430760124624845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53798107332287173416416563 80697160998430760124624845)
    ·
      refine ⟨30261435374411535046734317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80697160998430760124624845 30261435374411535046734317)
      ·
        refine ⟨11348038265404325642525369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30261435374411535046734317 11348038265404325642525369)
        ·
          refine ⟨8511028699053244231894027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11348038265404325642525369 8511028699053244231894027)
          ·
            refine ⟨12766543048579866347841041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511028699053244231894027 12766543048579866347841041)
            ·
              refine ⟨9574907286434899760880781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12766543048579866347841041 9574907286434899760880781)
              ·
                refine ⟨3590590232413087410330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9574907286434899760880781 3590590232413087410330293)
                ·
                  refine ⟨336617834288726944718465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3590590232413087410330293 336617834288726944718465)
                  ·
                    rfl

theorem cell22_2950024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_2950024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950024 prefixEnd_2950024 := by exact prefixLift 2950024
  have htrace : WordTrace (prefixWord ++ tailWord_2950024) baseStart_2950024 baseEnd_2950024 := by
    simpa [prefixWord, tailWord_2950024, baseEnd_2950024] using wordTrace_append hprefix tailTrace_2950024
  have hstable : (prefixWord ++ tailWord_2950024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950024).length < 2 ^ (prefixWord ++ tailWord_2950024).sum := by decide
  have hdescent : baseEnd_2950024 < baseStart_2950024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950052 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2950052 : Nat := 118140960795 + 2950052 * 2 ^ 59
def prefixEnd_2950052 : Nat := 4983230072969 + 3 ^ 40 * 2950052 * 2
def baseEnd_2950052 : Nat := 336621029279466031485103

theorem tailTrace_2950052 : CollatzResearch.WordTrace tailWord_2950052 prefixEnd_2950052 336621029279466031485103 := by
  unfold tailWord_2950052
  simp only [CollatzResearch.WordTrace]
  refine ⟨53798617954236453807426205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71731490605648605076568273 53798617954236453807426205)
  ·
    refine ⟨20174481732838670177784827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53798617954236453807426205 20174481732838670177784827)
    ·
      refine ⟨30261722599258005266677241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20174481732838670177784827 30261722599258005266677241)
      ·
        refine ⟨22696291949443503950007931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30261722599258005266677241 22696291949443503950007931)
        ·
          refine ⟨34044437924165255925011897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22696291949443503950007931 34044437924165255925011897)
          ·
            refine ⟨25533328443123941943758923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34044437924165255925011897 25533328443123941943758923)
            ·
              refine ⟨38299992664685912915638385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25533328443123941943758923 38299992664685912915638385)
              ·
                refine ⟨28724994498514434686728789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38299992664685912915638385 28724994498514434686728789)
                ·
                  refine ⟨336621029279466031485103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28724994498514434686728789 336621029279466031485103)
                  ·
                    rfl

theorem cell22_2950052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2950052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950052 prefixEnd_2950052 := by exact prefixLift 2950052
  have htrace : WordTrace (prefixWord ++ tailWord_2950052) baseStart_2950052 baseEnd_2950052 := by
    simpa [prefixWord, tailWord_2950052, baseEnd_2950052] using wordTrace_append hprefix tailTrace_2950052
  have hstable : (prefixWord ++ tailWord_2950052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950052).length < 2 ^ (prefixWord ++ tailWord_2950052).sum := by decide
  have hdescent : baseEnd_2950052 < baseStart_2950052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950069 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 6]
def baseStart_2950069 : Nat := 118140960795 + 2950069 * 2 ^ 59
def prefixEnd_2950069 : Nat := 4983230072969 + 3 ^ 40 * 2950069 * 2
def baseEnd_2950069 : Nat := 336622969095271905593419

theorem tailTrace_2950069 : CollatzResearch.WordTrace tailWord_2950069 prefixEnd_2950069 336622969095271905593419 := by
  unfold tailWord_2950069
  simp only [CollatzResearch.WordTrace]
  refine ⟨107597855949411319518221261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71731903966274213012147507 107597855949411319518221261)
  ·
    refine ⟨40349195981029244819332973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107597855949411319518221261 40349195981029244819332973)
    ·
      refine ⟨15130948492885966807249865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40349195981029244819332973 15130948492885966807249865)
      ·
        refine ⟨11348211369664475105437399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15130948492885966807249865 11348211369664475105437399)
        ·
          refine ⟨17022317054496712658156099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11348211369664475105437399 17022317054496712658156099)
          ·
            refine ⟨25533475581745068987234149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17022317054496712658156099 25533475581745068987234149)
            ·
              refine ⟨4787526671577200435106403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25533475581745068987234149 4787526671577200435106403)
              ·
                refine ⟨7181290007365800652659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787526671577200435106403 7181290007365800652659605)
                ·
                  refine ⟨336622969095271905593419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7181290007365800652659605 336622969095271905593419)
                  ·
                    rfl

theorem cell22_2950069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_2950069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950069 prefixEnd_2950069 := by exact prefixLift 2950069
  have htrace : WordTrace (prefixWord ++ tailWord_2950069) baseStart_2950069 baseEnd_2950069 := by
    simpa [prefixWord, tailWord_2950069, baseEnd_2950069] using wordTrace_append hprefix tailTrace_2950069
  have hstable : (prefixWord ++ tailWord_2950069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950069).length < 2 ^ (prefixWord ++ tailWord_2950069).sum := by decide
  have hdescent : baseEnd_2950069 < baseStart_2950069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950097 : List Nat := [1, 2, 2, 1, 2, 1, 5, 8]
def baseStart_2950097 : Nat := 118140960795 + 2950097 * 2 ^ 59
def prefixEnd_2950097 : Nat := 4983230072969 + 3 ^ 40 * 2950097 * 2
def baseEnd_2950097 : Nat := 112208721362003664120019

theorem tailTrace_2950097 : CollatzResearch.WordTrace tailWord_2950097 prefixEnd_2950097 112208721362003664120019 := by
  unfold tailWord_2950097
  simp only [CollatzResearch.WordTrace]
  refine ⟨107598877193309880300240545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71732584795539920200160363 107598877193309880300240545)
  ·
    refine ⟨80699157894982410225180409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107598877193309880300240545 80699157894982410225180409)
    ·
      refine ⟨60524368421236807668885307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80699157894982410225180409 60524368421236807668885307)
      ·
        refine ⟨90786552631855211503327961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60524368421236807668885307 90786552631855211503327961)
        ·
          refine ⟨68089914473891408627495971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90786552631855211503327961 68089914473891408627495971)
          ·
            refine ⟨102134871710837112941243957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68089914473891408627495971 102134871710837112941243957)
            ·
              refine ⟨9575144222890979338241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102134871710837112941243957 9575144222890979338241621)
              ·
                refine ⟨112208721362003664120019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9575144222890979338241621 112208721362003664120019)
                ·
                  rfl

theorem cell22_2950097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 8].length) (baseStart_2950097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950097 prefixEnd_2950097 := by exact prefixLift 2950097
  have htrace : WordTrace (prefixWord ++ tailWord_2950097) baseStart_2950097 baseEnd_2950097 := by
    simpa [prefixWord, tailWord_2950097, baseEnd_2950097] using wordTrace_append hprefix tailTrace_2950097
  have hstable : (prefixWord ++ tailWord_2950097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950097).length < 2 ^ (prefixWord ++ tailWord_2950097).sum := by decide
  have hdescent : baseEnd_2950097 < baseStart_2950097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950180 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_2950180 : Nat := 118140960795 + 2950180 * 2 ^ 59
def prefixEnd_2950180 : Nat := 4983230072969 + 3 ^ 40 * 2950180 * 2
def baseEnd_2950180 : Nat := 1009906904854248427254917

theorem tailTrace_2950180 : CollatzResearch.WordTrace tailWord_2950180 prefixEnd_2950180 1009906904854248427254917 := by
  unfold tailWord_2950180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800952226004592737755997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71734602968006123650341329 53800952226004592737755997)
  ·
    refine ⟨20175357084751722276658499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53800952226004592737755997 20175357084751722276658499)
    ·
      refine ⟨30263035627127583414987749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20175357084751722276658499 30263035627127583414987749)
      ·
        refine ⟨5674319180086421890310203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30263035627127583414987749 5674319180086421890310203)
        ·
          refine ⟨8511478770129632835465305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674319180086421890310203 8511478770129632835465305)
          ·
            refine ⟨6383609077597224626598979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8511478770129632835465305 6383609077597224626598979)
            ·
              refine ⟨9575413616395836939898469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383609077597224626598979 9575413616395836939898469)
              ·
                refine ⟨1795390053074219426230963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9575413616395836939898469 1795390053074219426230963)
                ·
                  refine ⟨2693085079611329139346445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795390053074219426230963 2693085079611329139346445)
                  ·
                    refine ⟨1009906904854248427254917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693085079611329139346445 1009906904854248427254917)
                    ·
                      rfl

theorem cell22_2950180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_2950180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950180 prefixEnd_2950180 := by exact prefixLift 2950180
  have htrace : WordTrace (prefixWord ++ tailWord_2950180) baseStart_2950180 baseEnd_2950180 := by
    simpa [prefixWord, tailWord_2950180, baseEnd_2950180] using wordTrace_append hprefix tailTrace_2950180
  have hstable : (prefixWord ++ tailWord_2950180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950180).length < 2 ^ (prefixWord ++ tailWord_2950180).sum := by decide
  have hdescent : baseEnd_2950180 < baseStart_2950180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950204 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_2950204 : Nat := 118140960795 + 2950204 * 2 ^ 59
def prefixEnd_2950204 : Nat := 4983230072969 + 3 ^ 40 * 2950204 * 2
def baseEnd_2950204 : Nat := 336638373514906788218281

theorem tailTrace_2950204 : CollatzResearch.WordTrace tailWord_2950204 prefixEnd_2950204 336638373514906788218281 := by
  unfold tailWord_2950204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53801389901961118787192833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71735186535948158382923777 53801389901961118787192833)
  ·
    refine ⟨40351042426470839090394625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53801389901961118787192833 40351042426470839090394625)
    ·
      refine ⟨30263281819853129317795969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40351042426470839090394625 30263281819853129317795969)
      ·
        refine ⟨22697461364889846988346977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30263281819853129317795969 22697461364889846988346977)
        ·
          refine ⟨17023096023667385241260233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22697461364889846988346977 17023096023667385241260233)
          ·
            refine ⟨12767322017750538930945175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023096023667385241260233 12767322017750538930945175)
            ·
              refine ⟨19150983026625808396417763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767322017750538930945175 19150983026625808396417763)
              ·
                refine ⟨28726474539938712594626645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19150983026625808396417763 28726474539938712594626645)
                ·
                  refine ⟨336638373514906788218281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28726474539938712594626645 336638373514906788218281)
                  ·
                    rfl

theorem cell22_2950204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_2950204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950204 prefixEnd_2950204 := by exact prefixLift 2950204
  have htrace : WordTrace (prefixWord ++ tailWord_2950204) baseStart_2950204 baseEnd_2950204 := by
    simpa [prefixWord, tailWord_2950204, baseEnd_2950204] using wordTrace_append hprefix tailTrace_2950204
  have hstable : (prefixWord ++ tailWord_2950204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950204).length < 2 ^ (prefixWord ++ tailWord_2950204).sum := by decide
  have hdescent : baseEnd_2950204 < baseStart_2950204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950253 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_2950253 : Nat := 118140960795 + 2950253 * 2 ^ 59
def prefixEnd_2950253 : Nat := 4983230072969 + 3 ^ 40 * 2950253 * 2
def baseEnd_2950253 : Nat := 1009931894246100570179693

theorem tailTrace_2950253 : CollatzResearch.WordTrace tailWord_2950253 prefixEnd_2950253 1009931894246100570179693 := by
  unfold tailWord_2950253
  simp only [CollatzResearch.WordTrace]
  refine ⟨107604566980744718942919413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71736377987163145961946275 107604566980744718942919413)
  ·
    refine ⟨10087928154444817400898695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107604566980744718942919413 10087928154444817400898695)
    ·
      refine ⟨15131892231667226101348043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087928154444817400898695 15131892231667226101348043)
      ·
        refine ⟨22697838347500839152022065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131892231667226101348043 22697838347500839152022065)
        ·
          refine ⟨17023378760625629364016549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22697838347500839152022065 17023378760625629364016549)
          ·
            refine ⟨3191883517617305505753103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17023378760625629364016549 3191883517617305505753103)
            ·
              refine ⟨4787825276425958258629655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191883517617305505753103 4787825276425958258629655)
              ·
                refine ⟨7181737914638937387944483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787825276425958258629655 7181737914638937387944483)
                ·
                  refine ⟨10772606871958406081916725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181737914638937387944483 10772606871958406081916725)
                  ·
                    refine ⟨1009931894246100570179693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10772606871958406081916725 1009931894246100570179693)
                    ·
                      rfl

theorem cell22_2950253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_2950253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950253 prefixEnd_2950253 := by exact prefixLift 2950253
  have htrace : WordTrace (prefixWord ++ tailWord_2950253) baseStart_2950253 baseEnd_2950253 := by
    simpa [prefixWord, tailWord_2950253, baseEnd_2950253] using wordTrace_append hprefix tailTrace_2950253
  have hstable : (prefixWord ++ tailWord_2950253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950253).length < 2 ^ (prefixWord ++ tailWord_2950253).sum := by decide
  have hdescent : baseEnd_2950253 < baseStart_2950253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950279 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2950279 : Nat := 118140960795 + 2950279 * 2 ^ 59
def prefixEnd_2950279 : Nat := 4983230072969 + 3 ^ 40 * 2950279 * 2
def baseEnd_2950279 : Nat := 1009940794577445169029613

theorem tailTrace_2950279 : CollatzResearch.WordTrace tailWord_2950279 prefixEnd_2950279 1009940794577445169029613 := by
  unfold tailWord_2950279
  simp only [CollatzResearch.WordTrace]
  refine ⟨107605515278650525383365891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71737010185767016922243927 107605515278650525383365891)
  ·
    refine ⟨161408272917975788075048837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107605515278650525383365891 161408272917975788075048837)
    ·
      refine ⟨30264051172120460264071657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161408272917975788075048837 30264051172120460264071657)
      ·
        refine ⟨22698038379090345198053743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30264051172120460264071657 22698038379090345198053743)
        ·
          refine ⟨34047057568635517797080615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22698038379090345198053743 34047057568635517797080615)
          ·
            refine ⟨51070586352953276695620923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34047057568635517797080615 51070586352953276695620923)
            ·
              refine ⟨76605879529429915043431385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51070586352953276695620923 76605879529429915043431385)
              ·
                refine ⟨57454409647072436282573539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76605879529429915043431385 57454409647072436282573539)
                ·
                  refine ⟨86181614470608654423860309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57454409647072436282573539 86181614470608654423860309)
                  ·
                    refine ⟨1009940794577445169029613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86181614470608654423860309 1009940794577445169029613)
                    ·
                      rfl

theorem cell22_2950279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2950279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950279 prefixEnd_2950279 := by exact prefixLift 2950279
  have htrace : WordTrace (prefixWord ++ tailWord_2950279) baseStart_2950279 baseEnd_2950279 := by
    simpa [prefixWord, tailWord_2950279, baseEnd_2950279] using wordTrace_append hprefix tailTrace_2950279
  have hstable : (prefixWord ++ tailWord_2950279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950279).length < 2 ^ (prefixWord ++ tailWord_2950279).sum := by decide
  have hdescent : baseEnd_2950279 < baseStart_2950279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950339 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 10]
def baseStart_2950339 : Nat := 118140960795 + 2950339 * 2 ^ 59
def prefixEnd_2950339 : Nat := 4983230072969 + 3 ^ 40 * 2950339 * 2
def baseEnd_2950339 : Nat := 336653777934541670843143

theorem tailTrace_2950339 : CollatzResearch.WordTrace tailWord_2950339 prefixEnd_2950339 336653777934541670843143 := by
  unfold tailWord_2950339
  simp only [CollatzResearch.WordTrace]
  refine ⟨107607703658433155630550071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71738469105622103753700047 107607703658433155630550071)
  ·
    refine ⟨161411555487649733445825107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107607703658433155630550071 161411555487649733445825107)
    ·
      refine ⟨242117333231474600168737661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161411555487649733445825107 242117333231474600168737661)
      ·
        refine ⟨90793999961802975063276623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242117333231474600168737661 90793999961802975063276623)
        ·
          refine ⟨136190999942704462594914935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90793999961802975063276623 136190999942704462594914935)
          ·
            refine ⟨204286499914056693892372403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136190999942704462594914935 204286499914056693892372403)
            ·
              refine ⟨306429749871085040838558605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204286499914056693892372403 306429749871085040838558605)
              ·
                refine ⟨114911156201656890314459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306429749871085040838558605 114911156201656890314459477)
                ·
                  refine ⟨336653777934541670843143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114911156201656890314459477 336653777934541670843143)
                  ·
                    rfl

theorem cell22_2950339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_2950339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950339 prefixEnd_2950339 := by exact prefixLift 2950339
  have htrace : WordTrace (prefixWord ++ tailWord_2950339) baseStart_2950339 baseEnd_2950339 := by
    simpa [prefixWord, tailWord_2950339, baseEnd_2950339] using wordTrace_append hprefix tailTrace_2950339
  have hstable : (prefixWord ++ tailWord_2950339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950339).length < 2 ^ (prefixWord ++ tailWord_2950339).sum := by decide
  have hdescent : baseEnd_2950339 < baseStart_2950339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950373 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 6]
def baseStart_2950373 : Nat := 118140960795 + 2950373 * 2 ^ 59
def prefixEnd_2950373 : Nat := 4983230072969 + 3 ^ 40 * 2950373 * 2
def baseEnd_2950373 : Nat := 336657657566153419059775

theorem tailTrace_2950373 : CollatzResearch.WordTrace tailWord_2950373 prefixEnd_2950373 336657657566153419059775 := by
  unfold tailWord_2950373
  simp only [CollatzResearch.WordTrace]
  refine ⟨107608943740309979437287773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71739295826873319624858515 107608943740309979437287773)
  ·
    refine ⟨40353353902616242288982915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107608943740309979437287773 40353353902616242288982915)
    ·
      refine ⟨60530030853924363433474373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40353353902616242288982915 60530030853924363433474373)
      ·
        refine ⟨11349380785110818143776445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60530030853924363433474373 11349380785110818143776445)
        ·
          refine ⟨4256017794416556803916167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11349380785110818143776445 4256017794416556803916167)
          ·
            refine ⟨6384026691624835205874251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256017794416556803916167 6384026691624835205874251)
            ·
              refine ⟨9576040037437252808811377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384026691624835205874251 9576040037437252808811377)
              ·
                refine ⟨7182030028077939606608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9576040037437252808811377 7182030028077939606608533)
                ·
                  refine ⟨336657657566153419059775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7182030028077939606608533 336657657566153419059775)
                  ·
                    rfl

theorem cell22_2950373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_2950373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950373 prefixEnd_2950373 := by exact prefixLift 2950373
  have htrace : WordTrace (prefixWord ++ tailWord_2950373) baseStart_2950373 baseEnd_2950373 := by
    simpa [prefixWord, tailWord_2950373, baseEnd_2950373] using wordTrace_append hprefix tailTrace_2950373
  have hstable : (prefixWord ++ tailWord_2950373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950373).length < 2 ^ (prefixWord ++ tailWord_2950373).sum := by decide
  have hdescent : baseEnd_2950373 < baseStart_2950373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950401 : List Nat := [1, 2, 4, 1, 1, 4, 9]
def baseStart_2950401 : Nat := 118140960795 + 2950401 * 2 ^ 59
def prefixEnd_2950401 : Nat := 4983230072969 + 3 ^ 40 * 2950401 * 2
def baseEnd_2950401 : Nat := 37406761395210278425157

theorem tailTrace_2950401 : CollatzResearch.WordTrace tailWord_2950401 prefixEnd_2950401 37406761395210278425157 := by
  unfold tailWord_2950401
  simp only [CollatzResearch.WordTrace]
  refine ⟨107609964984208540219307057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71739976656139026812871371 107609964984208540219307057)
  ·
    refine ⟨80707473738156405164480293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107609964984208540219307057 80707473738156405164480293)
    ·
      refine ⟨15132651325904325968340055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80707473738156405164480293 15132651325904325968340055)
      ·
        refine ⟨22698976988856488952510083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132651325904325968340055 22698976988856488952510083)
        ·
          refine ⟨34048465483284733428765125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22698976988856488952510083 34048465483284733428765125)
          ·
            refine ⟨6384087278115887517893461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34048465483284733428765125 6384087278115887517893461)
            ·
              refine ⟨37406761395210278425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6384087278115887517893461 37406761395210278425157)
              ·
                rfl

theorem cell22_2950401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 9].length) (baseStart_2950401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950401 prefixEnd_2950401 := by exact prefixLift 2950401
  have htrace : WordTrace (prefixWord ++ tailWord_2950401) baseStart_2950401 baseEnd_2950401 := by
    simpa [prefixWord, tailWord_2950401, baseEnd_2950401] using wordTrace_append hprefix tailTrace_2950401
  have hstable : (prefixWord ++ tailWord_2950401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950401).length < 2 ^ (prefixWord ++ tailWord_2950401).sum := by decide
  have hdescent : baseEnd_2950401 < baseStart_2950401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950525 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 4]
def baseStart_2950525 : Nat := 118140960795 + 2950525 * 2 ^ 59
def prefixEnd_2950525 : Nat := 4983230072969 + 3 ^ 40 * 2950525 * 2
def baseEnd_2950525 : Nat := 336675001801594175792953

theorem tailTrace_2950525 : CollatzResearch.WordTrace tailWord_2950525 prefixEnd_2950525 336675001801594175792953 := by
  unfold tailWord_2950525
  simp only [CollatzResearch.WordTrace]
  refine ⟨107614487635759309396821029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71742991757172872931214019 107614487635759309396821029)
  ·
    refine ⟨20177716431704870511903943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107614487635759309396821029 20177716431704870511903943)
    ·
      refine ⟨30266574647557305767855915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20177716431704870511903943 30266574647557305767855915)
      ·
        refine ⟨45399861971335958651783873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30266574647557305767855915 45399861971335958651783873)
        ·
          refine ⟨34049896478501968988837905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45399861971335958651783873 34049896478501968988837905)
          ·
            refine ⟨25537422358876476741628429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34049896478501968988837905 25537422358876476741628429)
            ·
              refine ⟨9576533384578678778110661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25537422358876476741628429 9576533384578678778110661)
              ·
                refine ⟨1795600009608502270895749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9576533384578678778110661 1795600009608502270895749)
                ·
                  refine ⟨336675001801594175792953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795600009608502270895749 336675001801594175792953)
                  ·
                    rfl

theorem cell22_2950525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_2950525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950525 prefixEnd_2950525 := by exact prefixLift 2950525
  have htrace : WordTrace (prefixWord ++ tailWord_2950525) baseStart_2950525 baseEnd_2950525 := by
    simpa [prefixWord, tailWord_2950525, baseEnd_2950525] using wordTrace_append hprefix tailTrace_2950525
  have hstable : (prefixWord ++ tailWord_2950525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950525).length < 2 ^ (prefixWord ++ tailWord_2950525).sum := by decide
  have hdescent : baseEnd_2950525 < baseStart_2950525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950540 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_2950540 : Nat := 118140960795 + 2950540 * 2 ^ 59
def prefixEnd_2950540 : Nat := 4983230072969 + 3 ^ 40 * 2950540 * 2
def baseEnd_2950540 : Nat := 1010030140211327488253813

theorem tailTrace_2950540 : CollatzResearch.WordTrace tailWord_2950540 prefixEnd_2950540 1010030140211327488253813 := by
  unfold tailWord_2950540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53807517365352483479308537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71743356487136644639078049 53807517365352483479308537)
  ·
    refine ⟨40355638024014362609481403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53807517365352483479308537 40355638024014362609481403)
    ·
      refine ⟨60533457036021543914222105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40355638024014362609481403 60533457036021543914222105)
      ·
        refine ⟨45400092777016157935666579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60533457036021543914222105 45400092777016157935666579)
        ·
          refine ⟨68100139165524236903499869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45400092777016157935666579 68100139165524236903499869)
          ·
            refine ⟨25537552187071588838812451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68100139165524236903499869 25537552187071588838812451)
            ·
              refine ⟨38306328280607383258218677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25537552187071588838812451 38306328280607383258218677)
              ·
                refine ⟨3591218276306942180458001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38306328280607383258218677 3591218276306942180458001)
                ·
                  refine ⟨2693413707230206635343501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591218276306942180458001 2693413707230206635343501)
                  ·
                    refine ⟨1010030140211327488253813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693413707230206635343501 1010030140211327488253813)
                    ·
                      rfl

theorem cell22_2950540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_2950540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950540 prefixEnd_2950540 := by exact prefixLift 2950540
  have htrace : WordTrace (prefixWord ++ tailWord_2950540) baseStart_2950540 baseEnd_2950540 := by
    simpa [prefixWord, tailWord_2950540, baseEnd_2950540] using wordTrace_append hprefix tailTrace_2950540
  have hstable : (prefixWord ++ tailWord_2950540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950540).length < 2 ^ (prefixWord ++ tailWord_2950540).sum := by decide
  have hdescent : baseEnd_2950540 < baseStart_2950540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950643 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 6]
def baseStart_2950643 : Nat := 118140960795 + 2950643 * 2 ^ 59
def prefixEnd_2950643 : Nat := 4983230072969 + 3 ^ 40 * 2950643 * 2
def baseEnd_2950643 : Nat := 336688466405423184309499

theorem tailTrace_2950643 : CollatzResearch.WordTrace tailWord_2950643 prefixEnd_2950643 336688466405423184309499 := by
  unfold tailWord_2950643
  simp only [CollatzResearch.WordTrace]
  refine ⟨107618791449331815549616583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71745860966221210366411055 107618791449331815549616583)
  ·
    refine ⟨161428187173997723324424875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107618791449331815549616583 161428187173997723324424875)
    ·
      refine ⟨242142280760996584986637313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161428187173997723324424875 242142280760996584986637313)
      ·
        refine ⟨181606710570747438739977985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242142280760996584986637313 181606710570747438739977985)
        ·
          refine ⟨136205032928060579054983489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181606710570747438739977985 136205032928060579054983489)
          ·
            refine ⟨102153774696045434291237617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136205032928060579054983489 102153774696045434291237617)
            ·
              refine ⟨76615331022034075718428213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102153774696045434291237617 76615331022034075718428213)
              ·
                refine ⟨7182687283315694598602645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76615331022034075718428213 7182687283315694598602645)
                ·
                  refine ⟨336688466405423184309499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7182687283315694598602645 336688466405423184309499)
                  ·
                    rfl

theorem cell22_2950643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_2950643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950643 prefixEnd_2950643 := by exact prefixLift 2950643
  have htrace : WordTrace (prefixWord ++ tailWord_2950643) baseStart_2950643 baseEnd_2950643 := by
    simpa [prefixWord, tailWord_2950643, baseEnd_2950643] using wordTrace_append hprefix tailTrace_2950643
  have hstable : (prefixWord ++ tailWord_2950643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950643).length < 2 ^ (prefixWord ++ tailWord_2950643).sum := by decide
  have hdescent : baseEnd_2950643 < baseStart_2950643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950675 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_2950675 : Nat := 118140960795 + 2950675 * 2 ^ 59
def prefixEnd_2950675 : Nat := 4983230072969 + 3 ^ 40 * 2950675 * 2
def baseEnd_2950675 : Nat := 1010076353470232136128399

theorem tailTrace_2950675 : CollatzResearch.WordTrace tailWord_2950675 prefixEnd_2950675 1010076353470232136128399 := by
  unfold tailWord_2950675
  simp only [CollatzResearch.WordTrace]
  refine ⟨107619958585215885014781479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71746639056810590009854319 107619958585215885014781479)
  ·
    refine ⟨161429937877823827522172219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107619958585215885014781479 161429937877823827522172219)
    ·
      refine ⟨242144906816735741283258329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161429937877823827522172219 242144906816735741283258329)
      ·
        refine ⟨181608680112551805962443747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242144906816735741283258329 181608680112551805962443747)
        ·
          refine ⟨272413020168827708943665621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181608680112551805962443747 272413020168827708943665621)
          ·
            refine ⟨6384680160206899428367163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 272413020168827708943665621 6384680160206899428367163)
            ·
              refine ⟨9577020240310349142550745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384680160206899428367163 9577020240310349142550745)
              ·
                refine ⟨7182765180232761856913059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9577020240310349142550745 7182765180232761856913059)
                ·
                  refine ⟨10774147770349142785369589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182765180232761856913059 10774147770349142785369589)
                  ·
                    refine ⟨1010076353470232136128399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10774147770349142785369589 1010076353470232136128399)
                    ·
                      rfl

theorem cell22_2950675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_2950675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950675 prefixEnd_2950675 := by exact prefixLift 2950675
  have htrace : WordTrace (prefixWord ++ tailWord_2950675) baseStart_2950675 baseEnd_2950675 := by
    simpa [prefixWord, tailWord_2950675, baseEnd_2950675] using wordTrace_append hprefix tailTrace_2950675
  have hstable : (prefixWord ++ tailWord_2950675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950675).length < 2 ^ (prefixWord ++ tailWord_2950675).sum := by decide
  have hdescent : baseEnd_2950675 < baseStart_2950675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950788 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2950788 : Nat := 118140960795 + 2950788 * 2 ^ 59
def prefixEnd_2950788 : Nat := 4983230072969 + 3 ^ 40 * 2950788 * 2
def baseEnd_2950788 : Nat := 1010115035679537508053053

theorem tailTrace_2950788 : CollatzResearch.WordTrace tailWord_2950788 prefixEnd_2950788 1010115035679537508053053 := by
  unfold tailWord_2950788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53812040016903252656822509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71749386689204336875763345 53812040016903252656822509)
  ·
    refine ⟨20179515006338719746308441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53812040016903252656822509 20179515006338719746308441)
    ·
      refine ⟨15134636254754039809731331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20179515006338719746308441 15134636254754039809731331)
      ·
        refine ⟨22701954382131059714596997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15134636254754039809731331 22701954382131059714596997)
        ·
          refine ⟨4256616446649573696486937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22701954382131059714596997 4256616446649573696486937)
          ·
            refine ⟨3192462334987180272365203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256616446649573696486937 3192462334987180272365203)
            ·
              refine ⟨4788693502480770408547805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192462334987180272365203 4788693502480770408547805)
              ·
                refine ⟨1795760063430288903205427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4788693502480770408547805 1795760063430288903205427)
                ·
                  refine ⟨2693640095145433354808141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795760063430288903205427 2693640095145433354808141)
                  ·
                    refine ⟨1010115035679537508053053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693640095145433354808141 1010115035679537508053053)
                    ·
                      rfl

theorem cell22_2950788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2950788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950788 prefixEnd_2950788 := by exact prefixLift 2950788
  have htrace : WordTrace (prefixWord ++ tailWord_2950788) baseStart_2950788 baseEnd_2950788 := by
    simpa [prefixWord, tailWord_2950788, baseEnd_2950788] using wordTrace_append hprefix tailTrace_2950788
  have hstable : (prefixWord ++ tailWord_2950788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950788).length < 2 ^ (prefixWord ++ tailWord_2950788).sum := by decide
  have hdescent : baseEnd_2950788 < baseStart_2950788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950818 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2950818 : Nat := 118140960795 + 2950818 * 2 ^ 59
def prefixEnd_2950818 : Nat := 4983230072969 + 3 ^ 40 * 2950818 * 2
def baseEnd_2950818 : Nat := 336708435097542476600987

theorem tailTrace_2950818 : CollatzResearch.WordTrace tailWord_2950818 prefixEnd_2950818 336708435097542476600987 := by
  unfold tailWord_2950818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906293555924455109309277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71750116149131880291491405 26906293555924455109309277)
  ·
    refine ⟨10089860083471670665990979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26906293555924455109309277 10089860083471670665990979)
    ·
      refine ⟨15134790125207505998986469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089860083471670665990979 15134790125207505998986469)
      ·
        refine ⟨2837773148476407374809963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15134790125207505998986469 2837773148476407374809963)
        ·
          refine ⟨4256659722714611062214945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837773148476407374809963 4256659722714611062214945)
          ·
            refine ⟨3192494792035958296661209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256659722714611062214945 3192494792035958296661209)
            ·
              refine ⟨2394371094026968722495907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192494792035958296661209 2394371094026968722495907)
              ·
                refine ⟨3591556641040453083743861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394371094026968722495907 3591556641040453083743861)
                ·
                  refine ⟨336708435097542476600987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591556641040453083743861 336708435097542476600987)
                  ·
                    rfl

theorem cell22_2950818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2950818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950818 prefixEnd_2950818 := by exact prefixLift 2950818
  have htrace : WordTrace (prefixWord ++ tailWord_2950818) baseStart_2950818 baseEnd_2950818 := by
    simpa [prefixWord, tailWord_2950818, baseEnd_2950818] using wordTrace_append hprefix tailTrace_2950818
  have hstable : (prefixWord ++ tailWord_2950818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950818).length < 2 ^ (prefixWord ++ tailWord_2950818).sum := by decide
  have hdescent : baseEnd_2950818 < baseStart_2950818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950842 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2950842 : Nat := 118140960795 + 2950842 * 2 ^ 59
def prefixEnd_2950842 : Nat := 4983230072969 + 3 ^ 40 * 2950842 * 2
def baseEnd_2950842 : Nat := 1010133520983099367202887

theorem tailTrace_2950842 : CollatzResearch.WordTrace tailWord_2950842 prefixEnd_2950842 1010133520983099367202887 := by
  unfold tailWord_2950842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906512393902718134027695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71750699717073915024073853 26906512393902718134027695)
  ·
    refine ⟨40359768590854077201041543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26906512393902718134027695 40359768590854077201041543)
    ·
      refine ⟨60539652886281115801562315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40359768590854077201041543 60539652886281115801562315)
      ·
        refine ⟨90809479329421673702343473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60539652886281115801562315 90809479329421673702343473)
        ·
          refine ⟨68107109497066255276757605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90809479329421673702343473 68107109497066255276757605)
          ·
            refine ⟨12770083030699922864392051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68107109497066255276757605 12770083030699922864392051)
            ·
              refine ⟨19155124546049884296588077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770083030699922864392051 19155124546049884296588077)
              ·
                refine ⟨7183171704768706611220529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19155124546049884296588077 7183171704768706611220529)
                ·
                  refine ⟨5387378778576529958415397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183171704768706611220529 5387378778576529958415397)
                  ·
                    refine ⟨1010133520983099367202887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387378778576529958415397 1010133520983099367202887)
                    ·
                      rfl

theorem cell22_2950842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2950842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950842 prefixEnd_2950842 := by exact prefixLift 2950842
  have htrace : WordTrace (prefixWord ++ tailWord_2950842) baseStart_2950842 baseEnd_2950842 := by
    simpa [prefixWord, tailWord_2950842, baseEnd_2950842] using wordTrace_append hprefix tailTrace_2950842
  have hstable : (prefixWord ++ tailWord_2950842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950842).length < 2 ^ (prefixWord ++ tailWord_2950842).sum := by decide
  have hdescent : baseEnd_2950842 < baseStart_2950842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950919 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 7]
def baseStart_2950919 : Nat := 118140960795 + 2950919 * 2 ^ 59
def prefixEnd_2950919 : Nat := 4983230072969 + 3 ^ 40 * 2950919 * 2
def baseEnd_2950919 : Nat := 336719959885565611009217

theorem tailTrace_2950919 : CollatzResearch.WordTrace tailWord_2950919 prefixEnd_2950919 336719959885565611009217 := by
  unfold tailWord_2950919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107628857996331914686663811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71752571997554609791109207 107628857996331914686663811)
  ·
    refine ⟨161443286994497872029995717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107628857996331914686663811 161443286994497872029995717)
    ·
      refine ⟨30270616311468351005624197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161443286994497872029995717 30270616311468351005624197)
      ·
        refine ⟨5675740558400315813554537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30270616311468351005624197 5675740558400315813554537)
        ·
          refine ⟨4256805418800236860165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5675740558400315813554537 4256805418800236860165903)
          ·
            refine ⟨6385208128200355290248855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256805418800236860165903 6385208128200355290248855)
            ·
              refine ⟨9577812192300532935373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385208128200355290248855 9577812192300532935373283)
              ·
                refine ⟨14366718288450799403059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9577812192300532935373283 14366718288450799403059925)
                ·
                  refine ⟨336719959885565611009217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14366718288450799403059925 336719959885565611009217)
                  ·
                    rfl

theorem cell22_2950919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_2950919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950919 prefixEnd_2950919 := by exact prefixLift 2950919
  have htrace : WordTrace (prefixWord ++ tailWord_2950919) baseStart_2950919 baseEnd_2950919 := by
    simpa [prefixWord, tailWord_2950919, baseEnd_2950919] using wordTrace_append hprefix tailTrace_2950919
  have hstable : (prefixWord ++ tailWord_2950919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950919).length < 2 ^ (prefixWord ++ tailWord_2950919).sum := by decide
  have hdescent : baseEnd_2950919 < baseStart_2950919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950947 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 6]
def baseStart_2950947 : Nat := 118140960795 + 2950947 * 2 ^ 59
def prefixEnd_2950947 : Nat := 4983230072969 + 3 ^ 40 * 2950947 * 2
def baseEnd_2950947 : Nat := 336723154876304697775855

theorem tailTrace_2950947 : CollatzResearch.WordTrace tailWord_2950947 prefixEnd_2950947 336723154876304697775855 := by
  unfold tailWord_2950947
  simp only [CollatzResearch.WordTrace]
  refine ⟨107629879240230475468683095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71753252826820316979122063 107629879240230475468683095)
  ·
    refine ⟨161444818860345713203024643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107629879240230475468683095 161444818860345713203024643)
    ·
      refine ⟨242167228290518569804536965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161444818860345713203024643 242167228290518569804536965)
      ·
        refine ⟨45406355304472231838350681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242167228290518569804536965 45406355304472231838350681)
        ·
          refine ⟨34054766478354173878763011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45406355304472231838350681 34054766478354173878763011)
          ·
            refine ⟨51082149717531260818144517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34054766478354173878763011 51082149717531260818144517)
            ·
              refine ⟨9577903072037111403402097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51082149717531260818144517 9577903072037111403402097)
              ·
                refine ⟨7183427304027833552551573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9577903072037111403402097 7183427304027833552551573)
                ·
                  refine ⟨336723154876304697775855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7183427304027833552551573 336723154876304697775855)
                  ·
                    rfl

theorem cell22_2950947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_2950947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950947 prefixEnd_2950947 := by exact prefixLift 2950947
  have htrace : WordTrace (prefixWord ++ tailWord_2950947) baseStart_2950947 baseEnd_2950947 := by
    simpa [prefixWord, tailWord_2950947, baseEnd_2950947] using wordTrace_append hprefix tailTrace_2950947
  have hstable : (prefixWord ++ tailWord_2950947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950947).length < 2 ^ (prefixWord ++ tailWord_2950947).sum := by decide
  have hdescent : baseEnd_2950947 < baseStart_2950947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950949 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2950949 : Nat := 118140960795 + 2950949 * 2 ^ 59
def prefixEnd_2950949 : Nat := 4983230072969 + 3 ^ 40 * 2950949 * 2
def baseEnd_2950949 : Nat := 1010170149269786754777559

theorem tailTrace_2950949 : CollatzResearch.WordTrace tailWord_2950949 prefixEnd_2950949 1010170149269786754777559 := by
  unfold tailWord_2950949
  simp only [CollatzResearch.WordTrace]
  refine ⟨107629952186223229810255901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71753301457482153206837267 107629952186223229810255901)
  ·
    refine ⟨40361232069833711178845963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107629952186223229810255901 40361232069833711178845963)
    ·
      refine ⟨60541848104750566768268945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40361232069833711178845963 60541848104750566768268945)
      ·
        refine ⟨45406386078562925076201709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60541848104750566768268945 45406386078562925076201709)
        ·
          refine ⟨17027394779461096903575641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45406386078562925076201709 17027394779461096903575641)
          ·
            refine ⟨12770546084595822677681731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17027394779461096903575641 12770546084595822677681731)
            ·
              refine ⟨19155819126893734016522597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770546084595822677681731 19155819126893734016522597)
              ·
                refine ⟨3591716086292575128097987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19155819126893734016522597 3591716086292575128097987)
                ·
                  refine ⟨5387574129438862692146981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591716086292575128097987 5387574129438862692146981)
                  ·
                    refine ⟨1010170149269786754777559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387574129438862692146981 1010170149269786754777559)
                    ·
                      rfl

theorem cell22_2950949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2950949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950949 prefixEnd_2950949 := by exact prefixLift 2950949
  have htrace : WordTrace (prefixWord ++ tailWord_2950949) baseStart_2950949 baseEnd_2950949 := by
    simpa [prefixWord, tailWord_2950949, baseEnd_2950949] using wordTrace_append hprefix tailTrace_2950949
  have hstable : (prefixWord ++ tailWord_2950949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950949).length < 2 ^ (prefixWord ++ tailWord_2950949).sum := by decide
  have hdescent : baseEnd_2950949 < baseStart_2950949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950979 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 4, 3]
def baseStart_2950979 : Nat := 118140960795 + 2950979 * 2 ^ 59
def prefixEnd_2950979 : Nat := 4983230072969 + 3 ^ 40 * 2950979 * 2
def baseEnd_2950979 : Nat := 1010180418882876676527467

theorem tailTrace_2950979 : CollatzResearch.WordTrace tailWord_2950979 prefixEnd_2950979 1010180418882876676527467 := by
  unfold tailWord_2950979
  simp only [CollatzResearch.WordTrace]
  refine ⟨107631046376114544933847991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71754030917409696622565327 107631046376114544933847991)
  ·
    refine ⟨161446569564171817400771987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107631046376114544933847991 161446569564171817400771987)
    ·
      refine ⟨242169854346257726101157981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161446569564171817400771987 242169854346257726101157981)
      ·
        refine ⟨90813695379846647287934243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242169854346257726101157981 90813695379846647287934243)
        ·
          refine ⟨136220543069769970931901365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90813695379846647287934243 136220543069769970931901365)
          ·
            refine ⟨12770675912790934774865753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136220543069769970931901365 12770675912790934774865753)
            ·
              refine ⟨9578006934593201081149315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12770675912790934774865753 9578006934593201081149315)
              ·
                refine ⟨14367010401889801621723973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578006934593201081149315 14367010401889801621723973)
                ·
                  refine ⟨2693814450354337804073245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14367010401889801621723973 2693814450354337804073245)
                  ·
                    refine ⟨1010180418882876676527467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693814450354337804073245 1010180418882876676527467)
                    ·
                      rfl

theorem cell22_2950979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].length) (baseStart_2950979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950979 prefixEnd_2950979 := by exact prefixLift 2950979
  have htrace : WordTrace (prefixWord ++ tailWord_2950979) baseStart_2950979 baseEnd_2950979 := by
    simpa [prefixWord, tailWord_2950979, baseEnd_2950979] using wordTrace_append hprefix tailTrace_2950979
  have hstable : (prefixWord ++ tailWord_2950979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950979).length < 2 ^ (prefixWord ++ tailWord_2950979).sum := by decide
  have hdescent : baseEnd_2950979 < baseStart_2950979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950981 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 4]
def baseStart_2950981 : Nat := 118140960795 + 2950981 * 2 ^ 59
def prefixEnd_2950981 : Nat := 4983230072969 + 3 ^ 40 * 2950981 * 2
def baseEnd_2950981 : Nat := 336727034507916445992487

theorem tailTrace_2950981 : CollatzResearch.WordTrace tailWord_2950981 prefixEnd_2950981 336727034507916445992487 := by
  unfold tailWord_2950981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107631119322107299275420797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71754079548071532850280531 107631119322107299275420797)
  ·
    refine ⟨40361669745790237228282799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107631119322107299275420797 40361669745790237228282799)
    ·
      refine ⟨60542504618685355842424199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40361669745790237228282799 60542504618685355842424199)
      ·
        refine ⟨90813756928028033763636299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60542504618685355842424199 90813756928028033763636299)
        ·
          refine ⟨136220635392042050645454449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90813756928028033763636299 136220635392042050645454449)
          ·
            refine ⟨102165476544031537984090837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136220635392042050645454449 102165476544031537984090837)
            ·
              refine ⟨2394503356500739171502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102165476544031537984090837 2394503356500739171502129)
              ·
                refine ⟨1795877517375554378626597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394503356500739171502129 1795877517375554378626597)
                ·
                  refine ⟨336727034507916445992487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795877517375554378626597 336727034507916445992487)
                  ·
                    rfl

theorem cell22_2950981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_2950981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2950981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2950981 prefixEnd_2950981 := by exact prefixLift 2950981
  have htrace : WordTrace (prefixWord ++ tailWord_2950981) baseStart_2950981 baseEnd_2950981 := by
    simpa [prefixWord, tailWord_2950981, baseEnd_2950981] using wordTrace_append hprefix tailTrace_2950981
  have hstable : (prefixWord ++ tailWord_2950981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950981).length < 2 ^ (prefixWord ++ tailWord_2950981).sum := by decide
  have hdescent : baseEnd_2950981 < baseStart_2950981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951011 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_2951011 : Nat := 118140960795 + 2951011 * 2 ^ 59
def prefixEnd_2951011 : Nat := 4983230072969 + 3 ^ 40 * 2951011 * 2
def baseEnd_2951011 : Nat := 1010191373136839259727369

theorem tailTrace_2951011 : CollatzResearch.WordTrace tailWord_2951011 prefixEnd_2951011 1010191373136839259727369 := by
  unfold tailWord_2951011
  simp only [CollatzResearch.WordTrace]
  refine ⟨107632213511998614399012887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71754809007999076266008591 107632213511998614399012887)
  ·
    refine ⟨161448320267997921598519331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107632213511998614399012887 161448320267997921598519331)
    ·
      refine ⟨242172480401996882397778997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161448320267997921598519331 242172480401996882397778997)
      ·
        refine ⟨22703670037687207724791781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242172480401996882397778997 22703670037687207724791781)
        ·
          refine ⟨4256938132066351448398459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22703670037687207724791781 4256938132066351448398459)
          ·
            refine ⟨6385407198099527172597689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256938132066351448398459 6385407198099527172597689)
            ·
              refine ⟨4789055398574645379448267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385407198099527172597689 4789055398574645379448267)
              ·
                refine ⟨7183583097861968069172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789055398574645379448267 7183583097861968069172401)
                ·
                  refine ⟨5387687323396476051879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183583097861968069172401 5387687323396476051879301)
                  ·
                    refine ⟨1010191373136839259727369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387687323396476051879301 1010191373136839259727369)
                    ·
                      rfl

theorem cell22_2951011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_2951011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951011 prefixEnd_2951011 := by exact prefixLift 2951011
  have htrace : WordTrace (prefixWord ++ tailWord_2951011) baseStart_2951011 baseEnd_2951011 := by
    simpa [prefixWord, tailWord_2951011, baseEnd_2951011] using wordTrace_append hprefix tailTrace_2951011
  have hstable : (prefixWord ++ tailWord_2951011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951011).length < 2 ^ (prefixWord ++ tailWord_2951011).sum := by decide
  have hdescent : baseEnd_2951011 < baseStart_2951011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951030 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2951030 : Nat := 118140960795 + 2951030 * 2 ^ 59
def prefixEnd_2951030 : Nat := 4983230072969 + 3 ^ 40 * 2951030 * 2
def baseEnd_2951030 : Nat := 1010197877225129543502311

theorem tailTrace_2951030 : CollatzResearch.WordTrace tailWord_2951030 prefixEnd_2951030 1010197877225129543502311 := by
  unfold tailWord_2951030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727056656183111290247159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71755270999286520429303029 6727056656183111290247159)
  ·
    refine ⟨10090584984274666935370739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727056656183111290247159 10090584984274666935370739)
    ·
      refine ⟨15135877476412000403056109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090584984274666935370739 15135877476412000403056109)
      ·
        refine ⟨5675954053654500151146041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15135877476412000403056109 5675954053654500151146041)
        ·
          refine ⟨4256965540240875113359531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5675954053654500151146041 4256965540240875113359531)
          ·
            refine ⟨6385448310361312670039297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256965540240875113359531 6385448310361312670039297)
            ·
              refine ⟨4789086232770984502529473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385448310361312670039297 4789086232770984502529473)
              ·
                refine ⟨3591814674578238376897105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789086232770984502529473 3591814674578238376897105)
                ·
                  refine ⟨2693861005933678782672829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591814674578238376897105 2693861005933678782672829)
                  ·
                    refine ⟨1010197877225129543502311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693861005933678782672829 1010197877225129543502311)
                    ·
                      rfl

theorem cell22_2951030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2951030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951030 prefixEnd_2951030 := by exact prefixLift 2951030
  have htrace : WordTrace (prefixWord ++ tailWord_2951030) baseStart_2951030 baseEnd_2951030 := by
    simpa [prefixWord, tailWord_2951030, baseEnd_2951030] using wordTrace_append hprefix tailTrace_2951030
  have hstable : (prefixWord ++ tailWord_2951030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951030).length < 2 ^ (prefixWord ++ tailWord_2951030).sum := by decide
  have hdescent : baseEnd_2951030 < baseStart_2951030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951058 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2951058 : Nat := 118140960795 + 2951058 * 2 ^ 59
def prefixEnd_2951058 : Nat := 4983230072969 + 3 ^ 40 * 2951058 * 2
def baseEnd_2951058 : Nat := 1010207462197346803802225

theorem tailTrace_2951058 : CollatzResearch.WordTrace tailWord_2951058 prefixEnd_2951058 1010207462197346803802225 := by
  unfold tailWord_2951058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26908481935707085356493457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71755951828552227617315885 26908481935707085356493457)
  ·
    refine ⟨20181361451780314017370093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26908481935707085356493457 20181361451780314017370093)
    ·
      refine ⟨7568010544417617756513785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20181361451780314017370093 7568010544417617756513785)
      ·
        refine ⟨5676007908313213317385339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7568010544417617756513785 5676007908313213317385339)
        ·
          refine ⟨8514011862469819976078009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676007908313213317385339 8514011862469819976078009)
          ·
            refine ⟨6385508896852364982058507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8514011862469819976078009 6385508896852364982058507)
            ·
              refine ⟨9578263345278547473087761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385508896852364982058507 9578263345278547473087761)
              ·
                refine ⟨7183697508958910604815821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9578263345278547473087761 7183697508958910604815821)
                ·
                  refine ⟨2693886565859591476805933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7183697508958910604815821 2693886565859591476805933)
                  ·
                    refine ⟨1010207462197346803802225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693886565859591476805933 1010207462197346803802225)
                    ·
                      rfl

theorem cell22_2951058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2951058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951058 prefixEnd_2951058 := by exact prefixLift 2951058
  have htrace : WordTrace (prefixWord ++ tailWord_2951058) baseStart_2951058 baseEnd_2951058 := by
    simpa [prefixWord, tailWord_2951058, baseEnd_2951058] using wordTrace_append hprefix tailTrace_2951058
  have hstable : (prefixWord ++ tailWord_2951058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951058).length < 2 ^ (prefixWord ++ tailWord_2951058).sum := by decide
  have hdescent : baseEnd_2951058 < baseStart_2951058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951062 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2951062 : Nat := 118140960795 + 2951062 * 2 ^ 59
def prefixEnd_2951062 : Nat := 4983230072969 + 3 ^ 40 * 2951062 * 2
def baseEnd_2951062 : Nat := 1010208831479092126702213

theorem tailTrace_2951062 : CollatzResearch.WordTrace tailWord_2951062 prefixEnd_2951062 1010208831479092126702213 := by
  unfold tailWord_2951062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727129602175865631819965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71756049089875900072746293 6727129602175865631819965)
  ·
    refine ⟨2522673600815949611932487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6727129602175865631819965 2522673600815949611932487)
    ·
      refine ⟨3784010401223924417898731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522673600815949611932487 3784010401223924417898731)
      ·
        refine ⟨5676015601835886626848097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784010401223924417898731 5676015601835886626848097)
        ·
          refine ⟨4257011701376914970136073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5676015601835886626848097 4257011701376914970136073)
          ·
            refine ⟨3192758776032686227602055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257011701376914970136073 3192758776032686227602055)
            ·
              refine ⟨4789138164049029341403083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192758776032686227602055 4789138164049029341403083)
              ·
                refine ⟨7183707246073544012104625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789138164049029341403083 7183707246073544012104625)
                ·
                  refine ⟨5387780434555158009078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183707246073544012104625 5387780434555158009078469)
                  ·
                    refine ⟨1010208831479092126702213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387780434555158009078469 1010208831479092126702213)
                    ·
                      rfl

theorem cell22_2951062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2951062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951062 prefixEnd_2951062 := by exact prefixLift 2951062
  have htrace : WordTrace (prefixWord ++ tailWord_2951062) baseStart_2951062 baseEnd_2951062 := by
    simpa [prefixWord, tailWord_2951062, baseEnd_2951062] using wordTrace_append hprefix tailTrace_2951062
  have hstable : (prefixWord ++ tailWord_2951062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951062).length < 2 ^ (prefixWord ++ tailWord_2951062).sum := by decide
  have hdescent : baseEnd_2951062 < baseStart_2951062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951146 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2951146 : Nat := 118140960795 + 2951146 * 2 ^ 59
def prefixEnd_2951146 : Nat := 4983230072969 + 3 ^ 40 * 2951146 * 2
def baseEnd_2951146 : Nat := 1010237586395743907601955

theorem tailTrace_2951146 : CollatzResearch.WordTrace tailWord_2951146 prefixEnd_2951146 1010237586395743907601955 := by
  unfold tailWord_2951146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909284341627383113794323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71758091577673021636784861 26909284341627383113794323)
  ·
    refine ⟨40363926512441074670691485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26909284341627383113794323 40363926512441074670691485)
    ·
      refine ⟨15136472442165403001509307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40363926512441074670691485 15136472442165403001509307)
      ·
        refine ⟨22704708663248104502263961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136472442165403001509307 22704708663248104502263961)
        ·
          refine ⟨17028531497436078376697971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22704708663248104502263961 17028531497436078376697971)
          ·
            refine ⟨25542797246154117565046957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17028531497436078376697971 25542797246154117565046957)
            ·
              refine ⟨9578548967307794086892609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25542797246154117565046957 9578548967307794086892609)
              ·
                refine ⟨7183911725480845565169457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9578548967307794086892609 7183911725480845565169457)
                ·
                  refine ⟨5387933794110634173877093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183911725480845565169457 5387933794110634173877093)
                  ·
                    refine ⟨1010237586395743907601955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387933794110634173877093 1010237586395743907601955)
                    ·
                      rfl

theorem cell22_2951146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2951146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951146 prefixEnd_2951146 := by exact prefixLift 2951146
  have htrace : WordTrace (prefixWord ++ tailWord_2951146) baseStart_2951146 baseEnd_2951146 := by
    simpa [prefixWord, tailWord_2951146, baseEnd_2951146] using wordTrace_append hprefix tailTrace_2951146
  have hstable : (prefixWord ++ tailWord_2951146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951146).length < 2 ^ (prefixWord ++ tailWord_2951146).sum := by decide
  have hdescent : baseEnd_2951146 < baseStart_2951146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951150 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_2951150 : Nat := 118140960795 + 2951150 * 2 ^ 59
def prefixEnd_2951150 : Nat := 4983230072969 + 3 ^ 40 * 2951150 * 2
def baseEnd_2951150 : Nat := 336746318559163076833981

theorem tailTrace_2951150 : CollatzResearch.WordTrace tailWord_2951150 prefixEnd_2951150 336746318559163076833981 := by
  unfold tailWord_2951150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13454660407311880142290363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71758188838996694092215269 13454660407311880142290363)
  ·
    refine ⟨20181990610967820213435545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13454660407311880142290363 20181990610967820213435545)
    ·
      refine ⟨15136492958225865160076659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20181990610967820213435545 15136492958225865160076659)
      ·
        refine ⟨22704739437338797740114989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136492958225865160076659 22704739437338797740114989)
        ·
          refine ⟨8514277289002049152543121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22704739437338797740114989 8514277289002049152543121)
          ·
            refine ⟨6385707966751536864407341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8514277289002049152543121 6385707966751536864407341)
            ·
              refine ⟨2394640487531826324152753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6385707966751536864407341 2394640487531826324152753)
              ·
                refine ⟨1795980365648869743114565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394640487531826324152753 1795980365648869743114565)
                ·
                  refine ⟨336746318559163076833981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795980365648869743114565 336746318559163076833981)
                  ·
                    rfl

theorem cell22_2951150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_2951150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951150 prefixEnd_2951150 := by exact prefixLift 2951150
  have htrace : WordTrace (prefixWord ++ tailWord_2951150) baseStart_2951150 baseEnd_2951150 := by
    simpa [prefixWord, tailWord_2951150, baseEnd_2951150] using wordTrace_append hprefix tailTrace_2951150
  have hstable : (prefixWord ++ tailWord_2951150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951150).length < 2 ^ (prefixWord ++ tailWord_2951150).sum := by decide
  have hdescent : baseEnd_2951150 < baseStart_2951150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951176 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_2951176 : Nat := 118140960795 + 2951176 * 2 ^ 59
def prefixEnd_2951176 : Nat := 4983230072969 + 3 ^ 40 * 2951176 * 2
def baseEnd_2951176 : Nat := 1010247856008833829351863

theorem tailTrace_2951176 : CollatzResearch.WordTrace tailWord_2951176 prefixEnd_2951176 1010247856008833829351863 := by
  unfold tailWord_2951176
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819115778200423789384691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71758821037600565052512921 53819115778200423789384691)
  ·
    refine ⟨80728673667300635684077037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53819115778200423789384691 80728673667300635684077037)
    ·
      refine ⟨30273252625237738381528889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80728673667300635684077037 30273252625237738381528889)
      ·
        refine ⟨22704939468928303786146667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30273252625237738381528889 22704939468928303786146667)
        ·
          refine ⟨34057409203392455679220001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22704939468928303786146667 34057409203392455679220001)
          ·
            refine ⟨25543056902544341759415001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34057409203392455679220001 25543056902544341759415001)
            ·
              refine ⟨19157292676908256319561251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25543056902544341759415001 19157292676908256319561251)
              ·
                refine ⟨28735939015362384479341877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19157292676908256319561251 28735939015362384479341877)
                ·
                  refine ⟨2693994282690223544938301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28735939015362384479341877 2693994282690223544938301)
                  ·
                    refine ⟨1010247856008833829351863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693994282690223544938301 1010247856008833829351863)
                    ·
                      rfl

theorem cell22_2951176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_2951176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951176 prefixEnd_2951176 := by exact prefixLift 2951176
  have htrace : WordTrace (prefixWord ++ tailWord_2951176) baseStart_2951176 baseEnd_2951176 := by
    simpa [prefixWord, tailWord_2951176, baseEnd_2951176] using wordTrace_append hprefix tailTrace_2951176
  have hstable : (prefixWord ++ tailWord_2951176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951176).length < 2 ^ (prefixWord ++ tailWord_2951176).sum := by decide
  have hdescent : baseEnd_2951176 < baseStart_2951176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951193 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_2951193 : Nat := 118140960795 + 2951193 * 2 ^ 59
def prefixEnd_2951193 : Nat := 4983230072969 + 3 ^ 40 * 2951193 * 2
def baseEnd_2951193 : Nat := 1010253675456251451676811

theorem tailTrace_2951193 : CollatzResearch.WordTrace tailWord_2951193 prefixEnd_2951193 1010253675456251451676811 := by
  unfold tailWord_2951193
  simp only [CollatzResearch.WordTrace]
  refine ⟨107638851597339259482138233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71759234398226172988092155 107638851597339259482138233)
  ·
    refine ⟨80729138698004444611603675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107638851597339259482138233 80729138698004444611603675)
    ·
      refine ⟨121093708047006666917405513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80729138698004444611603675 121093708047006666917405513)
      ·
        refine ⟨90820281035255000188054135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121093708047006666917405513 90820281035255000188054135)
        ·
          refine ⟨136230421552882500282081203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90820281035255000188054135 136230421552882500282081203)
          ·
            refine ⟨204345632329323750423121805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136230421552882500282081203 204345632329323750423121805)
            ·
              refine ⟨76629612123496406408670677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204345632329323750423121805 76629612123496406408670677)
              ·
                refine ⟨1796006534144447025203219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76629612123496406408670677 1796006534144447025203219)
                ·
                  refine ⟨2694009801216670537804829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796006534144447025203219 2694009801216670537804829)
                  ·
                    refine ⟨1010253675456251451676811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694009801216670537804829 1010253675456251451676811)
                    ·
                      rfl

theorem cell22_2951193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_2951193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951193 prefixEnd_2951193 := by exact prefixLift 2951193
  have htrace : WordTrace (prefixWord ++ tailWord_2951193) baseStart_2951193 baseEnd_2951193 := by
    simpa [prefixWord, tailWord_2951193, baseEnd_2951193] using wordTrace_append hprefix tailTrace_2951193
  have hstable : (prefixWord ++ tailWord_2951193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951193).length < 2 ^ (prefixWord ++ tailWord_2951193).sum := by decide
  have hdescent : baseEnd_2951193 < baseStart_2951193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951238 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2951238 : Nat := 118140960795 + 2951238 * 2 ^ 59
def prefixEnd_2951238 : Nat := 4983230072969 + 3 ^ 40 * 2951238 * 2
def baseEnd_2951238 : Nat := 1010269079875886334301673

theorem tailTrace_2951238 : CollatzResearch.WordTrace tailWord_2951238 prefixEnd_2951238 1010269079875886334301673 := by
  unfold tailWord_2951238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363765402568007255235199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71760328588117488111684245 3363765402568007255235199)
  ·
    refine ⟨5045648103852010882852799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3363765402568007255235199 5045648103852010882852799)
    ·
      refine ⟨7568472155778016324279199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5045648103852010882852799 7568472155778016324279199)
      ·
        refine ⟨11352708233667024486418799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568472155778016324279199 11352708233667024486418799)
        ·
          refine ⟨17029062350500536729628199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11352708233667024486418799 17029062350500536729628199)
          ·
            refine ⟨25543593525750805094442299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029062350500536729628199 25543593525750805094442299)
            ·
              refine ⟨38315390288626207641663449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25543593525750805094442299 38315390288626207641663449)
              ·
                refine ⟨28736542716469655731247587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38315390288626207641663449 28736542716469655731247587)
                ·
                  refine ⟨43104814074704483596871381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28736542716469655731247587 43104814074704483596871381)
                  ·
                    refine ⟨1010269079875886334301673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43104814074704483596871381 1010269079875886334301673)
                    ·
                      rfl

theorem cell22_2951238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2951238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951238 prefixEnd_2951238 := by exact prefixLift 2951238
  have htrace : WordTrace (prefixWord ++ tailWord_2951238) baseStart_2951238 baseEnd_2951238 := by
    simpa [prefixWord, tailWord_2951238, baseEnd_2951238] using wordTrace_append hprefix tailTrace_2951238
  have hstable : (prefixWord ++ tailWord_2951238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951238).length < 2 ^ (prefixWord ++ tailWord_2951238).sum := by decide
  have hdescent : baseEnd_2951238 < baseStart_2951238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951253 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2951253 : Nat := 118140960795 + 2951253 * 2 ^ 59
def prefixEnd_2951253 : Nat := 4983230072969 + 3 ^ 40 * 2951253 * 2
def baseEnd_2951253 : Nat := 1010274214682431295176627

theorem tailTrace_2951253 : CollatzResearch.WordTrace tailWord_2951253 prefixEnd_2951253 1010274214682431295176627 := by
  unfold tailWord_2951253
  simp only [CollatzResearch.WordTrace]
  refine ⟨107641039977121889729322413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71760693318081259819548275 107641039977121889729322413)
  ·
    refine ⟨40365389991420708648495905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107641039977121889729322413 40365389991420708648495905)
    ·
      refine ⟨30274042493565531486371929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40365389991420708648495905 30274042493565531486371929)
      ·
        refine ⟨22705531870174148614778947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30274042493565531486371929 22705531870174148614778947)
        ·
          refine ⟨34058297805261222922168421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22705531870174148614778947 34058297805261222922168421)
          ·
            refine ⟨6385930838486479297906579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34058297805261222922168421 6385930838486479297906579)
            ·
              refine ⟨9578896257729718946859869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385930838486479297906579 9578896257729718946859869)
              ·
                refine ⟨3592086096648644605072451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9578896257729718946859869 3592086096648644605072451)
                ·
                  refine ⟨5388129144972966907608677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592086096648644605072451 5388129144972966907608677)
                  ·
                    refine ⟨1010274214682431295176627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5388129144972966907608677 1010274214682431295176627)
                    ·
                      rfl

theorem cell22_2951253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2951253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951253 prefixEnd_2951253 := by exact prefixLift 2951253
  have htrace : WordTrace (prefixWord ++ tailWord_2951253) baseStart_2951253 baseEnd_2951253 := by
    simpa [prefixWord, tailWord_2951253, baseEnd_2951253] using wordTrace_append hprefix tailTrace_2951253
  have hstable : (prefixWord ++ tailWord_2951253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951253).length < 2 ^ (prefixWord ++ tailWord_2951253).sum := by decide
  have hdescent : baseEnd_2951253 < baseStart_2951253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951268 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_2951268 : Nat := 118140960795 + 2951268 * 2 ^ 59
def prefixEnd_2951268 : Nat := 4983230072969 + 3 ^ 40 * 2951268 * 2
def baseEnd_2951268 : Nat := 336759783162992085350527

theorem tailTrace_2951268 : CollatzResearch.WordTrace tailWord_2951268 prefixEnd_2951268 336759783162992085350527 := by
  unfold tailWord_2951268
  simp only [CollatzResearch.WordTrace]
  refine ⟨53820793536033773645559229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71761058048045031527412305 53820793536033773645559229)
  ·
    refine ⟨20182797576012665117084711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53820793536033773645559229 20182797576012665117084711)
    ·
      refine ⟨30274196364018997675627067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20182797576012665117084711 30274196364018997675627067)
      ·
        refine ⟨45411294546028496513440601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30274196364018997675627067 45411294546028496513440601)
        ·
          refine ⟨34058470909521372385080451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45411294546028496513440601 34058470909521372385080451)
          ·
            refine ⟨51087706364282058577620677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34058470909521372385080451 51087706364282058577620677)
            ·
              refine ⟨9578944943302885983303877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51087706364282058577620677 9578944943302885983303877)
              ·
                refine ⟨1796052176869291121869477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9578944943302885983303877 1796052176869291121869477)
                ·
                  refine ⟨336759783162992085350527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796052176869291121869477 336759783162992085350527)
                  ·
                    rfl

theorem cell22_2951268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_2951268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951268 prefixEnd_2951268 := by exact prefixLift 2951268
  have htrace : WordTrace (prefixWord ++ tailWord_2951268) baseStart_2951268 baseEnd_2951268 := by
    simpa [prefixWord, tailWord_2951268, baseEnd_2951268] using wordTrace_append hprefix tailTrace_2951268
  have hstable : (prefixWord ++ tailWord_2951268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951268).length < 2 ^ (prefixWord ++ tailWord_2951268).sum := by decide
  have hdescent : baseEnd_2951268 < baseStart_2951268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951401 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_2951401 : Nat := 118140960795 + 2951401 * 2 ^ 59
def prefixEnd_2951401 : Nat := 4983230072969 + 3 ^ 40 * 2951401 * 2
def baseEnd_2951401 : Nat := 1010324878107008242476173

theorem tailTrace_2951401 : CollatzResearch.WordTrace tailWord_2951401 prefixEnd_2951401 1010324878107008242476173 := by
  unfold tailWord_2951401
  simp only [CollatzResearch.WordTrace]
  refine ⟨107646437980585711005710057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71764291987057140670473371 107646437980585711005710057)
  ·
    refine ⟨80734828485439283254282543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107646437980585711005710057 80734828485439283254282543)
    ·
      refine ⟨121102242728158924881423815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80734828485439283254282543 121102242728158924881423815)
      ·
        refine ⟨181653364092238387322135723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121102242728158924881423815 181653364092238387322135723)
        ·
          refine ⟨272480046138357580983203585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181653364092238387322135723 272480046138357580983203585)
          ·
            refine ⟨204360034603768185737402689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272480046138357580983203585 204360034603768185737402689)
            ·
              refine ⟨153270025952826139303052017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204360034603768185737402689 153270025952826139303052017)
              ·
                refine ⟨114952519464619604477289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153270025952826139303052017 114952519464619604477289013)
                ·
                  refine ⟨10776798699808087919745845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114952519464619604477289013 10776798699808087919745845)
                  ·
                    refine ⟨1010324878107008242476173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10776798699808087919745845 1010324878107008242476173)
                    ·
                      rfl

theorem cell22_2951401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_2951401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951401 prefixEnd_2951401 := by exact prefixLift 2951401
  have htrace : WordTrace (prefixWord ++ tailWord_2951401) baseStart_2951401 baseEnd_2951401 := by
    simpa [prefixWord, tailWord_2951401, baseEnd_2951401] using wordTrace_append hprefix tailTrace_2951401
  have hstable : (prefixWord ++ tailWord_2951401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951401).length < 2 ^ (prefixWord ++ tailWord_2951401).sum := by decide
  have hdescent : baseEnd_2951401 < baseStart_2951401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951418 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2951418 : Nat := 118140960795 + 2951418 * 2 ^ 59
def prefixEnd_2951418 : Nat := 4983230072969 + 3 ^ 40 * 2951418 * 2
def baseEnd_2951418 : Nat := 1010330697554425864801121

theorem tailTrace_2951418 : CollatzResearch.WordTrace tailWord_2951418 prefixEnd_2951418 1010330697554425864801121 := by
  unfold tailWord_2951418
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911764505381030727269727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71764705347682748606052605 26911764505381030727269727)
  ·
    refine ⟨40367646758071546090904591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26911764505381030727269727 40367646758071546090904591)
    ·
      refine ⟨60551470137107319136356887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40367646758071546090904591 60551470137107319136356887)
      ·
        refine ⟨90827205205660978704535331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60551470137107319136356887 90827205205660978704535331)
        ·
          refine ⟨136240807808491468056802997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90827205205660978704535331 136240807808491468056802997)
          ·
            refine ⟨12772575732046075130325281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136240807808491468056802997 12772575732046075130325281)
            ·
              refine ⟨9579431799034556347743961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12772575732046075130325281 9579431799034556347743961)
              ·
                refine ⟨7184573849275917260807971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9579431799034556347743961 7184573849275917260807971)
                ·
                  refine ⟨10776860773913875891211957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184573849275917260807971 10776860773913875891211957)
                  ·
                    refine ⟨1010330697554425864801121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10776860773913875891211957 1010330697554425864801121)
                    ·
                      rfl

theorem cell22_2951418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2951418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951418 prefixEnd_2951418 := by exact prefixLift 2951418
  have htrace : WordTrace (prefixWord ++ tailWord_2951418) baseStart_2951418 baseEnd_2951418 := by
    simpa [prefixWord, tailWord_2951418, baseEnd_2951418] using wordTrace_append hprefix tailTrace_2951418
  have hstable : (prefixWord ++ tailWord_2951418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951418).length < 2 ^ (prefixWord ++ tailWord_2951418).sum := by decide
  have hdescent : baseEnd_2951418 < baseStart_2951418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951420 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_2951420 : Nat := 118140960795 + 2951420 * 2 ^ 59
def prefixEnd_2951420 : Nat := 4983230072969 + 3 ^ 40 * 2951420 * 2
def baseEnd_2951420 : Nat := 336777127398432842083705

theorem tailTrace_2951420 : CollatzResearch.WordTrace tailWord_2951420 prefixEnd_2951420 336777127398432842083705 := by
  unfold tailWord_2951420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53823565483758438625325857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71764753978344584833767809 53823565483758438625325857)
  ·
    refine ⟨40367674112818828968994393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53823565483758438625325857 40367674112818828968994393)
    ·
      refine ⟨30275755584614121726745795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40367674112818828968994393 30275755584614121726745795)
      ·
        refine ⟨45413633376921182590118693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30275755584614121726745795 45413633376921182590118693)
        ·
          refine ⟨8515056258172721735647255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45413633376921182590118693 8515056258172721735647255)
          ·
            refine ⟨12772584387259082603470883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515056258172721735647255 12772584387259082603470883)
            ·
              refine ⟨19158876580888623905206325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772584387259082603470883 19158876580888623905206325)
              ·
                refine ⟨1796144679458308491113093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19158876580888623905206325 1796144679458308491113093)
                ·
                  refine ⟨336777127398432842083705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796144679458308491113093 336777127398432842083705)
                  ·
                    rfl

theorem cell22_2951420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_2951420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951420 prefixEnd_2951420 := by exact prefixLift 2951420
  have htrace : WordTrace (prefixWord ++ tailWord_2951420) baseStart_2951420 baseEnd_2951420 := by
    simpa [prefixWord, tailWord_2951420, baseEnd_2951420] using wordTrace_append hprefix tailTrace_2951420
  have hstable : (prefixWord ++ tailWord_2951420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951420).length < 2 ^ (prefixWord ++ tailWord_2951420).sum := by decide
  have hdescent : baseEnd_2951420 < baseStart_2951420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951518 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2951518 : Nat := 118140960795 + 2951518 * 2 ^ 59
def prefixEnd_2951518 : Nat := 4983230072969 + 3 ^ 40 * 2951518 * 2
def baseEnd_2951518 : Nat := 1010364929598058937300815

theorem tailTrace_2951518 : CollatzResearch.WordTrace tailWord_2951518 prefixEnd_2951518 1010364929598058937300815 := by
  unfold tailWord_2951518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456338165145229998464901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71767136880774559991812805 13456338165145229998464901)
  ·
    refine ⟨2523063405964730624712169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13456338165145229998464901 2523063405964730624712169)
    ·
      refine ⟨1892297554473547968534127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2523063405964730624712169 1892297554473547968534127)
      ·
        refine ⟨2838446331710321952801191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892297554473547968534127 2838446331710321952801191)
        ·
          refine ⟨4257669497565482929201787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838446331710321952801191 4257669497565482929201787)
          ·
            refine ⟨6386504246348224393802681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257669497565482929201787 6386504246348224393802681)
            ·
              refine ⟨4789878184761168295352011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386504246348224393802681 4789878184761168295352011)
              ·
                refine ⟨7184817277141752443028017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789878184761168295352011 7184817277141752443028017)
                ·
                  refine ⟨5388612957856314332271013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7184817277141752443028017 5388612957856314332271013)
                  ·
                    refine ⟨1010364929598058937300815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5388612957856314332271013 1010364929598058937300815)
                    ·
                      rfl

theorem cell22_2951518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2951518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951518 prefixEnd_2951518 := by exact prefixLift 2951518
  have htrace : WordTrace (prefixWord ++ tailWord_2951518) baseStart_2951518 baseEnd_2951518 := by
    simpa [prefixWord, tailWord_2951518, baseEnd_2951518] using wordTrace_append hprefix tailTrace_2951518
  have hstable : (prefixWord ++ tailWord_2951518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951518).length < 2 ^ (prefixWord ++ tailWord_2951518).sum := by decide
  have hdescent : baseEnd_2951518 < baseStart_2951518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951572 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2951572 : Nat := 118140960795 + 2951572 * 2 ^ 59
def prefixEnd_2951572 : Nat := 4983230072969 + 3 ^ 40 * 2951572 * 2
def baseEnd_2951572 : Nat := 336794471633873598816883

theorem tailTrace_2951572 : CollatzResearch.WordTrace tailWord_2951572 prefixEnd_2951572 336794471633873598816883 := by
  unfold tailWord_2951572
  simp only [CollatzResearch.WordTrace]
  refine ⟨53826337431483103605092485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71768449908644138140123313 53826337431483103605092485)
  ·
    refine ⟨10092438268403081925954841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53826337431483103605092485 10092438268403081925954841)
    ·
      refine ⟨7569328701302311444466131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10092438268403081925954841 7569328701302311444466131)
      ·
        refine ⟨11353993051953467166699197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569328701302311444466131 11353993051953467166699197)
        ·
          refine ⟨4257747394482550187512199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11353993051953467166699197 4257747394482550187512199)
          ·
            refine ⟨6386621091723825281268299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257747394482550187512199 6386621091723825281268299)
            ·
              refine ⟨9579931637585737921902449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386621091723825281268299 9579931637585737921902449)
              ·
                refine ⟨7184948728189303441426837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9579931637585737921902449 7184948728189303441426837)
                ·
                  refine ⟨336794471633873598816883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7184948728189303441426837 336794471633873598816883)
                  ·
                    rfl

theorem cell22_2951572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2951572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951572 prefixEnd_2951572 := by exact prefixLift 2951572
  have htrace : WordTrace (prefixWord ++ tailWord_2951572) baseStart_2951572 baseEnd_2951572 := by
    simpa [prefixWord, tailWord_2951572, baseEnd_2951572] using wordTrace_append hprefix tailTrace_2951572
  have hstable : (prefixWord ++ tailWord_2951572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951572).length < 2 ^ (prefixWord ++ tailWord_2951572).sum := by decide
  have hdescent : baseEnd_2951572 < baseStart_2951572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_2951643 : Nat := 118140960795 + 2951643 * 2 ^ 59
def prefixEnd_2951643 : Nat := 4983230072969 + 3 ^ 40 * 2951643 * 2
def baseEnd_2951643 : Nat := 1010407719652600277925431

theorem tailTrace_2951643 : CollatzResearch.WordTrace tailWord_2951643 prefixEnd_2951643 1010407719652600277925431 := by
  unfold tailWord_2951643
  simp only [CollatzResearch.WordTrace]
  refine ⟨107655264445708986336019583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71770176297139324224013055 107655264445708986336019583)
  ·
    refine ⟨161482896668563479504029375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107655264445708986336019583 161482896668563479504029375)
    ·
      refine ⟨242224345002845219256044063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161482896668563479504029375 242224345002845219256044063)
      ·
        refine ⟨363336517504267828884066095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242224345002845219256044063 363336517504267828884066095)
        ·
          refine ⟨545004776256401743326099143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363336517504267828884066095 545004776256401743326099143)
          ·
            refine ⟨817507164384602614989148715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545004776256401743326099143 817507164384602614989148715)
            ·
              refine ⟨1226260746576903922483723073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817507164384602614989148715 1226260746576903922483723073)
              ·
                refine ⟨919695559932677941862792305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226260746576903922483723073 919695559932677941862792305)
                ·
                  refine ⟨689771669949508456397094229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919695559932677941862792305 689771669949508456397094229)
                  ·
                    refine ⟨1010407719652600277925431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 689771669949508456397094229 1010407719652600277925431)
                    ·
                      rfl

theorem cell22_2951643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_2951643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951643 prefixEnd_2951643 := by exact prefixLift 2951643
  have htrace : WordTrace (prefixWord ++ tailWord_2951643) baseStart_2951643 baseEnd_2951643 := by
    simpa [prefixWord, tailWord_2951643, baseEnd_2951643] using wordTrace_append hprefix tailTrace_2951643
  have hstable : (prefixWord ++ tailWord_2951643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951643).length < 2 ^ (prefixWord ++ tailWord_2951643).sum := by decide
  have hdescent : baseEnd_2951643 < baseStart_2951643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951645 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2951645 : Nat := 118140960795 + 2951645 * 2 ^ 59
def prefixEnd_2951645 : Nat := 4983230072969 + 3 ^ 40 * 2951645 * 2
def baseEnd_2951645 : Nat := 336802801431157646458475

theorem tailTrace_2951645 : CollatzResearch.WordTrace tailWord_2951645 prefixEnd_2951645 336802801431157646458475 := by
  unfold tailWord_2951645
  simp only [CollatzResearch.WordTrace]
  refine ⟨107655337391701740677592389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71770224927801160451728259 107655337391701740677592389)
  ·
    refine ⟨20185375760944076377048573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107655337391701740677592389 20185375760944076377048573)
    ·
      refine ⟨7569515910354028641393215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20185375760944076377048573 7569515910354028641393215)
      ·
        refine ⟨11354273865531042962089823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569515910354028641393215 11354273865531042962089823)
        ·
          refine ⟨17031410798296564443134735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354273865531042962089823 17031410798296564443134735)
          ·
            refine ⟨25547116197444846664702103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031410798296564443134735 25547116197444846664702103)
            ·
              refine ⟨38320674296167269997053155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25547116197444846664702103 38320674296167269997053155)
              ·
                refine ⟨57481011444250904995579733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38320674296167269997053155 57481011444250904995579733)
                ·
                  refine ⟨336802801431157646458475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57481011444250904995579733 336802801431157646458475)
                  ·
                    rfl

theorem cell22_2951645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2951645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951645 prefixEnd_2951645 := by exact prefixLift 2951645
  have htrace : WordTrace (prefixWord ++ tailWord_2951645) baseStart_2951645 baseEnd_2951645 := by
    simpa [prefixWord, tailWord_2951645, baseEnd_2951645] using wordTrace_append hprefix tailTrace_2951645
  have hstable : (prefixWord ++ tailWord_2951645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951645).length < 2 ^ (prefixWord ++ tailWord_2951645).sum := by decide
  have hdescent : baseEnd_2951645 < baseStart_2951645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951666 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2951666 : Nat := 118140960795 + 2951666 * 2 ^ 59
def prefixEnd_2951666 : Nat := 4983230072969 + 3 ^ 40 * 2951666 * 2
def baseEnd_2951666 : Nat := 1010415593022635884600361

theorem tailTrace_2951666 : CollatzResearch.WordTrace tailWord_2951666 prefixEnd_2951666 1010415593022635884600361 := by
  unfold tailWord_2951666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914025831156415316026713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71770735549750440842737901 26914025831156415316026713)
  ·
    refine ⟨20185519373367311487020035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26914025831156415316026713 20185519373367311487020035)
    ·
      refine ⟨30278279060050967230530053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20185519373367311487020035 30278279060050967230530053)
      ·
        refine ⟨5677177323759556355724385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30278279060050967230530053 5677177323759556355724385)
        ·
          refine ⟨4257882992819667266793289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5677177323759556355724385 4257882992819667266793289)
          ·
            refine ⟨3193412244614750450094967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257882992819667266793289 3193412244614750450094967)
            ·
              refine ⟨4790118366922125675142451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193412244614750450094967 4790118366922125675142451)
              ·
                refine ⟨7185177550383188512713677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790118366922125675142451 7185177550383188512713677)
                ·
                  refine ⟨2694441581393695692267629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7185177550383188512713677 2694441581393695692267629)
                  ·
                    refine ⟨1010415593022635884600361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694441581393695692267629 1010415593022635884600361)
                    ·
                      rfl

theorem cell22_2951666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2951666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951666 prefixEnd_2951666 := by exact prefixLift 2951666
  have htrace : WordTrace (prefixWord ++ tailWord_2951666) baseStart_2951666 baseEnd_2951666 := by
    simpa [prefixWord, tailWord_2951666, baseEnd_2951666] using wordTrace_append hprefix tailTrace_2951666
  have hstable : (prefixWord ++ tailWord_2951666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951666).length < 2 ^ (prefixWord ++ tailWord_2951666).sum := by decide
  have hdescent : baseEnd_2951666 < baseStart_2951666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951690 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_2951690 : Nat := 118140960795 + 2951690 * 2 ^ 59
def prefixEnd_2951690 : Nat := 4983230072969 + 3 ^ 40 * 2951690 * 2
def baseEnd_2951690 : Nat := 336807936237702607333429

theorem tailTrace_2951690 : CollatzResearch.WordTrace tailWord_2951690 prefixEnd_2951690 336807936237702607333429 := by
  unfold tailWord_2951690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914244669134678340745131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71771319117692475575320349 26914244669134678340745131)
  ·
    refine ⟨40371367003702017511117697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914244669134678340745131 40371367003702017511117697)
    ·
      refine ⟨30278525252776513133338273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40371367003702017511117697 30278525252776513133338273)
      ·
        refine ⟨22708893939582384850003705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30278525252776513133338273 22708893939582384850003705)
        ·
          refine ⟨17031670454686788637502779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22708893939582384850003705 17031670454686788637502779)
          ·
            refine ⟨25547505682030182956254169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031670454686788637502779 25547505682030182956254169)
            ·
              refine ⟨19160629261522637217190627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25547505682030182956254169 19160629261522637217190627)
              ·
                refine ⟨28740943892283955825785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19160629261522637217190627 28740943892283955825785941)
                ·
                  refine ⟨336807936237702607333429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28740943892283955825785941 336807936237702607333429)
                  ·
                    rfl

theorem cell22_2951690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_2951690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951690 prefixEnd_2951690 := by exact prefixLift 2951690
  have htrace : WordTrace (prefixWord ++ tailWord_2951690) baseStart_2951690 baseEnd_2951690 := by
    simpa [prefixWord, tailWord_2951690, baseEnd_2951690] using wordTrace_append hprefix tailTrace_2951690
  have hstable : (prefixWord ++ tailWord_2951690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951690).length < 2 ^ (prefixWord ++ tailWord_2951690).sum := by decide
  have hdescent : baseEnd_2951690 < baseStart_2951690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951692 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2951692 : Nat := 118140960795 + 2951692 * 2 ^ 59
def prefixEnd_2951692 : Nat := 4983230072969 + 3 ^ 40 * 2951692 * 2
def baseEnd_2951692 : Nat := 1010424493353980483450281

theorem tailTrace_2951692 : CollatzResearch.WordTrace tailWord_2951692 prefixEnd_2951692 1010424493353980483450281 := by
  unfold tailWord_2951692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53828525811265733852276665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71771367748354311803035553 53828525811265733852276665)
  ·
    refine ⟨40371394358449300389207499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53828525811265733852276665 40371394358449300389207499)
    ·
      refine ⟨60557091537673950583811249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40371394358449300389207499 60557091537673950583811249)
      ·
        refine ⟨45417818653255462937858437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60557091537673950583811249 45417818653255462937858437)
        ·
          refine ⟨8515840997485399300848457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45417818653255462937858437 8515840997485399300848457)
          ·
            refine ⟨6386880748114049475636343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515840997485399300848457 6386880748114049475636343)
            ·
              refine ⟨9580321122171074213454515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386880748114049475636343 9580321122171074213454515)
              ·
                refine ⟨14370481683256611320181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9580321122171074213454515 14370481683256611320181773)
                ·
                  refine ⟨5388930631221229245068165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14370481683256611320181773 5388930631221229245068165)
                  ·
                    refine ⟨1010424493353980483450281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5388930631221229245068165 1010424493353980483450281)
                    ·
                      rfl

theorem cell22_2951692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2951692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951692 prefixEnd_2951692 := by exact prefixLift 2951692
  have htrace : WordTrace (prefixWord ++ tailWord_2951692) baseStart_2951692 baseEnd_2951692 := by
    simpa [prefixWord, tailWord_2951692, baseEnd_2951692] using wordTrace_append hprefix tailTrace_2951692
  have hstable : (prefixWord ++ tailWord_2951692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951692).length < 2 ^ (prefixWord ++ tailWord_2951692).sum := by decide
  have hdescent : baseEnd_2951692 < baseStart_2951692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951705 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_2951705 : Nat := 118140960795 + 2951705 * 2 ^ 59
def prefixEnd_2951705 : Nat := 4983230072969 + 3 ^ 40 * 2951705 * 2
def baseEnd_2951705 : Nat := 1010428943519652782875241

theorem tailTrace_2951705 : CollatzResearch.WordTrace tailWord_2951705 prefixEnd_2951705 1010428943519652782875241 := by
  unfold tailWord_2951705
  simp only [CollatzResearch.WordTrace]
  refine ⟨107657525771484370924776569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71771683847656247283184379 107657525771484370924776569)
  ·
    refine ⟨80743144328613278193582427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107657525771484370924776569 80743144328613278193582427)
    ·
      refine ⟨121114716492919917290373641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80743144328613278193582427 121114716492919917290373641)
      ·
        refine ⟨90836037369689937967780231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121114716492919917290373641 90836037369689937967780231)
        ·
          refine ⟨136254056054534906951670347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90836037369689937967780231 136254056054534906951670347)
          ·
            refine ⟨204381084081802360427505521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136254056054534906951670347 204381084081802360427505521)
            ·
              refine ⟨153285813061351770320629141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204381084081802360427505521 153285813061351770320629141)
              ·
                refine ⟨7185272487250864233779491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153285813061351770320629141 7185272487250864233779491)
                ·
                  refine ⟨10777908730876296350669237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185272487250864233779491 10777908730876296350669237)
                  ·
                    refine ⟨1010428943519652782875241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10777908730876296350669237 1010428943519652782875241)
                    ·
                      rfl

theorem cell22_2951705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_2951705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951705 prefixEnd_2951705 := by exact prefixLift 2951705
  have htrace : WordTrace (prefixWord ++ tailWord_2951705) baseStart_2951705 baseEnd_2951705 := by
    simpa [prefixWord, tailWord_2951705, baseEnd_2951705] using wordTrace_append hprefix tailTrace_2951705
  have hstable : (prefixWord ++ tailWord_2951705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951705).length < 2 ^ (prefixWord ++ tailWord_2951705).sum := by decide
  have hdescent : baseEnd_2951705 < baseStart_2951705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951754 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2951754 : Nat := 118140960795 + 2951754 * 2 ^ 59
def prefixEnd_2951754 : Nat := 4983230072969 + 3 ^ 40 * 2951754 * 2
def baseEnd_2951754 : Nat := 1010445717221032988400091

theorem tailTrace_2951754 : CollatzResearch.WordTrace tailWord_2951754 prefixEnd_2951754 1010445717221032988400091 := by
  unfold tailWord_2951754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914828237076713073327579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71772875298871234862206877 26914828237076713073327579)
  ·
    refine ⟨40372242355615069609991369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914828237076713073327579 40372242355615069609991369)
    ·
      refine ⟨30279181766711302207493527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40372242355615069609991369 30279181766711302207493527)
      ·
        refine ⟨45418772650066953311240291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30279181766711302207493527 45418772650066953311240291)
        ·
          refine ⟨68128158975100429966860437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45418772650066953311240291 68128158975100429966860437)
          ·
            refine ⟨3193507451957832654696583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68128158975100429966860437 3193507451957832654696583)
            ·
              refine ⟨4790261177936748982044875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193507451957832654696583 4790261177936748982044875)
              ·
                refine ⟨7185391766905123473067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790261177936748982044875 7185391766905123473067313)
                ·
                  refine ⟨5389043825178842604800485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185391766905123473067313 5389043825178842604800485)
                  ·
                    refine ⟨1010445717221032988400091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389043825178842604800485 1010445717221032988400091)
                    ·
                      rfl

theorem cell22_2951754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2951754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951754 prefixEnd_2951754 := by exact prefixLift 2951754
  have htrace : WordTrace (prefixWord ++ tailWord_2951754) baseStart_2951754 baseEnd_2951754 := by
    simpa [prefixWord, tailWord_2951754, baseEnd_2951754] using wordTrace_append hprefix tailTrace_2951754
  have hstable : (prefixWord ++ tailWord_2951754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951754).length < 2 ^ (prefixWord ++ tailWord_2951754).sum := by decide
  have hdescent : baseEnd_2951754 < baseStart_2951754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951767 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 5, 3]
def baseStart_2951767 : Nat := 118140960795 + 2951767 * 2 ^ 59
def prefixEnd_2951767 : Nat := 4983230072969 + 3 ^ 40 * 2951767 * 2
def baseEnd_2951767 : Nat := 1010450167386705287825051

theorem tailTrace_2951767 : CollatzResearch.WordTrace tailWord_2951767 prefixEnd_2951767 1010450167386705287825051 := by
  unfold tailWord_2951767
  simp only [CollatzResearch.WordTrace]
  refine ⟨107659787097259755513533555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71773191398173170342355703 107659787097259755513533555)
  ·
    refine ⟨161489680645889633270300333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107659787097259755513533555 161489680645889633270300333)
    ·
      refine ⟨60558630242208612476362625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161489680645889633270300333 60558630242208612476362625)
      ·
        refine ⟨45418972681656459357271969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60558630242208612476362625 45418972681656459357271969)
        ·
          refine ⟨34064229511242344517953977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45418972681656459357271969 34064229511242344517953977)
          ·
            refine ⟨25548172133431758388465483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34064229511242344517953977 25548172133431758388465483)
            ·
              refine ⟨38322258200147637582698225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548172133431758388465483 38322258200147637582698225)
              ·
                refine ⟨28741693650110728187023669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38322258200147637582698225 28741693650110728187023669)
                ·
                  refine ⟨2694533779697880767533469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28741693650110728187023669 2694533779697880767533469)
                  ·
                    refine ⟨1010450167386705287825051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694533779697880767533469 1010450167386705287825051)
                    ·
                      rfl

theorem cell22_2951767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_2951767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951767 prefixEnd_2951767 := by exact prefixLift 2951767
  have htrace : WordTrace (prefixWord ++ tailWord_2951767) baseStart_2951767 baseEnd_2951767 := by
    simpa [prefixWord, tailWord_2951767, baseEnd_2951767] using wordTrace_append hprefix tailTrace_2951767
  have hstable : (prefixWord ++ tailWord_2951767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951767).length < 2 ^ (prefixWord ++ tailWord_2951767).sum := by decide
  have hdescent : baseEnd_2951767 < baseStart_2951767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951795 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_2951795 : Nat := 118140960795 + 2951795 * 2 ^ 59
def prefixEnd_2951795 : Nat := 4983230072969 + 3 ^ 40 * 2951795 * 2
def baseEnd_2951795 : Nat := 1010459752358922548124965

theorem tailTrace_2951795 : CollatzResearch.WordTrace tailWord_2951795 prefixEnd_2951795 1010459752358922548124965 := by
  unfold tailWord_2951795
  simp only [CollatzResearch.WordTrace]
  refine ⟨107660808341158316295552839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71773872227438877530368559 107660808341158316295552839)
  ·
    refine ⟨161491212511737474443329259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107660808341158316295552839 161491212511737474443329259)
    ·
      refine ⟨242236818767606211664993889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161491212511737474443329259 242236818767606211664993889)
      ·
        refine ⟨181677614075704658748745417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242236818767606211664993889 181677614075704658748745417)
        ·
          refine ⟨136258210556778494061559063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181677614075704658748745417 136258210556778494061559063)
          ·
            refine ⟨204387315835167741092338595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136258210556778494061559063 204387315835167741092338595)
            ·
              refine ⟨306580973752751611638507893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204387315835167741092338595 306580973752751611638507893)
              ·
                refine ⟨28741966289320463591110115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306580973752751611638507893 28741966289320463591110115)
                ·
                  refine ⟨43112949433980695386665173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28741966289320463591110115 43112949433980695386665173)
                  ·
                    refine ⟨1010459752358922548124965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43112949433980695386665173 1010459752358922548124965)
                    ·
                      rfl

theorem cell22_2951795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_2951795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951795 prefixEnd_2951795 := by exact prefixLift 2951795
  have htrace : WordTrace (prefixWord ++ tailWord_2951795) baseStart_2951795 baseEnd_2951795 := by
    simpa [prefixWord, tailWord_2951795, baseEnd_2951795] using wordTrace_append hprefix tailTrace_2951795
  have hstable : (prefixWord ++ tailWord_2951795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951795).length < 2 ^ (prefixWord ++ tailWord_2951795).sum := by decide
  have hdescent : baseEnd_2951795 < baseStart_2951795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951861 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2951861 : Nat := 118140960795 + 2951861 * 2 ^ 59
def prefixEnd_2951861 : Nat := 4983230072969 + 3 ^ 40 * 2951861 * 2
def baseEnd_2951861 : Nat := 1010482345507720375974763

theorem tailTrace_2951861 : CollatzResearch.WordTrace tailWord_2951861 prefixEnd_2951861 1010482345507720375974763 := by
  unfold tailWord_2951861
  simp only [CollatzResearch.WordTrace]
  refine ⟨107663215558919209567455437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71775477039279473044970291 107663215558919209567455437)
  ·
    refine ⟨40373705834594703587795789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107663215558919209567455437 40373705834594703587795789)
    ·
      refine ⟨15140139687973013845423421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40373705834594703587795789 15140139687973013845423421)
      ·
        refine ⟨5677552382989880192033783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15140139687973013845423421 5677552382989880192033783)
        ·
          refine ⟨8516328574484820288050675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677552382989880192033783 8516328574484820288050675)
          ·
            refine ⟨12774492861727230432076013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8516328574484820288050675 12774492861727230432076013)
            ·
              refine ⟨4790434823147711412028505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12774492861727230432076013 4790434823147711412028505)
              ·
                refine ⟨3592826117360783559021379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790434823147711412028505 3592826117360783559021379)
                ·
                  refine ⟨5389239176041175338532069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592826117360783559021379 5389239176041175338532069)
                  ·
                    refine ⟨1010482345507720375974763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389239176041175338532069 1010482345507720375974763)
                    ·
                      rfl

theorem cell22_2951861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2951861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951861 prefixEnd_2951861 := by exact prefixLift 2951861
  have htrace : WordTrace (prefixWord ++ tailWord_2951861) baseStart_2951861 baseEnd_2951861 := by
    simpa [prefixWord, tailWord_2951861, baseEnd_2951861] using wordTrace_append hprefix tailTrace_2951861
  have hstable : (prefixWord ++ tailWord_2951861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951861).length < 2 ^ (prefixWord ++ tailWord_2951861).sum := by decide
  have hdescent : baseEnd_2951861 < baseStart_2951861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951893 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 4]
def baseStart_2951893 : Nat := 118140960795 + 2951893 * 2 ^ 59
def prefixEnd_2951893 : Nat := 4983230072969 + 3 ^ 40 * 2951893 * 2
def baseEnd_2951893 : Nat := 336831099920560986391555

theorem tailTrace_2951893 : CollatzResearch.WordTrace tailWord_2951893 prefixEnd_2951893 336831099920560986391555 := by
  unfold tailWord_2951893
  simp only [CollatzResearch.WordTrace]
  refine ⟨107664382694803279032620333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71776255129868852688413555 107664382694803279032620333)
  ·
    refine ⟨40374143510551229637232625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107664382694803279032620333 40374143510551229637232625)
    ·
      refine ⟨30280607632913422227924469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40374143510551229637232625 30280607632913422227924469)
      ·
        refine ⟨2838806965585633333867919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30280607632913422227924469 2838806965585633333867919)
        ·
          refine ⟨4258210448378450000801879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838806965585633333867919 4258210448378450000801879)
          ·
            refine ⟨6387315672567675001202819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258210448378450000801879 6387315672567675001202819)
            ·
              refine ⟨9580973508851512501804229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387315672567675001202819 9580973508851512501804229)
              ·
                refine ⟨1796432532909658594088293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9580973508851512501804229 1796432532909658594088293)
                ·
                  refine ⟨336831099920560986391555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796432532909658594088293 336831099920560986391555)
                  ·
                    rfl

theorem cell22_2951893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_2951893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951893 prefixEnd_2951893 := by exact prefixLift 2951893
  have htrace : WordTrace (prefixWord ++ tailWord_2951893) baseStart_2951893 baseEnd_2951893 := by
    simpa [prefixWord, tailWord_2951893, baseEnd_2951893] using wordTrace_append hprefix tailTrace_2951893
  have hstable : (prefixWord ++ tailWord_2951893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951893).length < 2 ^ (prefixWord ++ tailWord_2951893).sum := by decide
  have hdescent : baseEnd_2951893 < baseStart_2951893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951919 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 5, 3]
def baseStart_2951919 : Nat := 118140960795 + 2951919 * 2 ^ 59
def prefixEnd_2951919 : Nat := 4983230072969 + 3 ^ 40 * 2951919 * 2
def baseEnd_2951919 : Nat := 1010502200093027558024585

theorem tailTrace_2951919 : CollatzResearch.WordTrace tailWord_2951919 prefixEnd_2951919 1010502200093027558024585 := by
  unfold tailWord_2951919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107665330992709085473066811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71776887328472723648711207 107665330992709085473066811)
  ·
    refine ⟨161497996489063628209600217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107665330992709085473066811 161497996489063628209600217)
    ·
      refine ⟨121123497366797721157200163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161497996489063628209600217 121123497366797721157200163)
      ·
        refine ⟨181685246050196581735800245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121123497366797721157200163 181685246050196581735800245)
        ·
          refine ⟨17032991817205929537731273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181685246050196581735800245 17032991817205929537731273)
          ·
            refine ⟨12774743862904447153298455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17032991817205929537731273 12774743862904447153298455)
            ·
              refine ⟨19162115794356670729947683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12774743862904447153298455 19162115794356670729947683)
              ·
                refine ⟨28743173691535006094921525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19162115794356670729947683 28743173691535006094921525)
                ·
                  refine ⟨2694672533581406821398893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28743173691535006094921525 2694672533581406821398893)
                  ·
                    refine ⟨1010502200093027558024585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694672533581406821398893 1010502200093027558024585)
                    ·
                      rfl

theorem cell22_2951919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_2951919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951919 prefixEnd_2951919 := by exact prefixLift 2951919
  have htrace : WordTrace (prefixWord ++ tailWord_2951919) baseStart_2951919 baseEnd_2951919 := by
    simpa [prefixWord, tailWord_2951919, baseEnd_2951919] using wordTrace_append hprefix tailTrace_2951919
  have hstable : (prefixWord ++ tailWord_2951919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951919).length < 2 ^ (prefixWord ++ tailWord_2951919).sum := by decide
  have hdescent : baseEnd_2951919 < baseStart_2951919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951964 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2951964 : Nat := 118140960795 + 2951964 * 2 ^ 59
def prefixEnd_2951964 : Nat := 4983230072969 + 3 ^ 40 * 2951964 * 2
def baseEnd_2951964 : Nat := 1010517604512662440649447

theorem tailTrace_2951964 : CollatzResearch.WordTrace tailWord_2951964 prefixEnd_2951964 1010517604512662440649447 := by
  unfold tailWord_2951964
  simp only [CollatzResearch.WordTrace]
  refine ⟨53833486138773029079227473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71777981518364038772303297 53833486138773029079227473)
  ·
    refine ⟨40375114604079771809420605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53833486138773029079227473 40375114604079771809420605)
    ·
      refine ⟨15140667976529914428532727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40375114604079771809420605 15140667976529914428532727)
      ·
        refine ⟨22711001964794871642799091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15140667976529914428532727 22711001964794871642799091)
        ·
          refine ⟨34066502947192307464198637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22711001964794871642799091 34066502947192307464198637)
          ·
            refine ⟨12774938605197115299074489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34066502947192307464198637 12774938605197115299074489)
            ·
              refine ⟨9581203953897836474305867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12774938605197115299074489 9581203953897836474305867)
              ·
                refine ⟨14371805930846754711458801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581203953897836474305867 14371805930846754711458801)
                ·
                  refine ⟨10778854448135066033594101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14371805930846754711458801 10778854448135066033594101)
                  ·
                    refine ⟨1010517604512662440649447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10778854448135066033594101 1010517604512662440649447)
                    ·
                      rfl

theorem cell22_2951964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2951964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951964 prefixEnd_2951964 := by exact prefixLift 2951964
  have htrace : WordTrace (prefixWord ++ tailWord_2951964) baseStart_2951964 baseEnd_2951964 := by
    simpa [prefixWord, tailWord_2951964, baseEnd_2951964] using wordTrace_append hprefix tailTrace_2951964
  have hstable : (prefixWord ++ tailWord_2951964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951964).length < 2 ^ (prefixWord ++ tailWord_2951964).sum := by decide
  have hdescent : baseEnd_2951964 < baseStart_2951964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951979 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 1, 4]
def baseStart_2951979 : Nat := 118140960795 + 2951979 * 2 ^ 59
def prefixEnd_2951979 : Nat := 4983230072969 + 3 ^ 40 * 2951979 * 2
def baseEnd_2951979 : Nat := 1010522739319207401524401

theorem tailTrace_2951979 : CollatzResearch.WordTrace tailWord_2951979 prefixEnd_2951979 1010522739319207401524401 := by
  unfold tailWord_2951979
  simp only [CollatzResearch.WordTrace]
  refine ⟨107667519372491715720250991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71778346248327810480167327 107667519372491715720250991)
  ·
    refine ⟨161501279058737573580376487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107667519372491715720250991 161501279058737573580376487)
    ·
      refine ⟨242251918588106360370564731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161501279058737573580376487 242251918588106360370564731)
      ·
        refine ⟨363377877882159540555847097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242251918588106360370564731 363377877882159540555847097)
        ·
          refine ⟨272533408411619655416885323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363377877882159540555847097 272533408411619655416885323)
          ·
            refine ⟨408800112617429483125327985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272533408411619655416885323 408800112617429483125327985)
            ·
              refine ⟨306600084463072112343995989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408800112617429483125327985 306600084463072112343995989)
              ·
                refine ⟨3592969739801626316531203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 306600084463072112343995989 3592969739801626316531203)
                ·
                  refine ⟨5389454609702439474796805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592969739801626316531203 5389454609702439474796805)
                  ·
                    refine ⟨1010522739319207401524401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389454609702439474796805 1010522739319207401524401)
                    ·
                      rfl

theorem cell22_2951979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_2951979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2951979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2951979 prefixEnd_2951979 := by exact prefixLift 2951979
  have htrace : WordTrace (prefixWord ++ tailWord_2951979) baseStart_2951979 baseEnd_2951979 := by
    simpa [prefixWord, tailWord_2951979, baseEnd_2951979] using wordTrace_append hprefix tailTrace_2951979
  have hstable : (prefixWord ++ tailWord_2951979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951979).length < 2 ^ (prefixWord ++ tailWord_2951979).sum := by decide
  have hdescent : baseEnd_2951979 < baseStart_2951979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952004 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2952004 : Nat := 118140960795 + 2952004 * 2 ^ 59
def prefixEnd_2952004 : Nat := 4983230072969 + 3 ^ 40 * 2952004 * 2
def baseEnd_2952004 : Nat := 1010531297330115669649325

theorem tailTrace_2952004 : CollatzResearch.WordTrace tailWord_2952004 prefixEnd_2952004 1010531297330115669649325 := by
  unfold tailWord_2952004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53834215598700572494955533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71778954131600763326607377 53834215598700572494955533)
  ·
    refine ⟨20187830849512714685608325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53834215598700572494955533 20187830849512714685608325)
    ·
      refine ⟨3785218284283634003551561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20187830849512714685608325 3785218284283634003551561)
      ·
        refine ⟨2838913713212725502663671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3785218284283634003551561 2838913713212725502663671)
        ·
          refine ⟨4258370569819088253995507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838913713212725502663671 4258370569819088253995507)
          ·
            refine ⟨6387555854728632380993261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258370569819088253995507 6387555854728632380993261)
            ·
              refine ⟨2395333445523237142872473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6387555854728632380993261 2395333445523237142872473)
              ·
                refine ⟨1796500084142427857154355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395333445523237142872473 1796500084142427857154355)
                ·
                  refine ⟨2694750126213641785731533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796500084142427857154355 2694750126213641785731533)
                  ·
                    refine ⟨1010531297330115669649325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694750126213641785731533 1010531297330115669649325)
                    ·
                      rfl

theorem cell22_2952004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2952004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952004 prefixEnd_2952004 := by exact prefixLift 2952004
  have htrace : WordTrace (prefixWord ++ tailWord_2952004) baseStart_2952004 baseEnd_2952004 := by
    simpa [prefixWord, tailWord_2952004, baseEnd_2952004] using wordTrace_append hprefix tailTrace_2952004
  have hstable : (prefixWord ++ tailWord_2952004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952004).length < 2 ^ (prefixWord ++ tailWord_2952004).sum := by decide
  have hdescent : baseEnd_2952004 < baseStart_2952004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952039 : List Nat := [1, 1, 5, 1, 2, 2, 2, 8]
def baseStart_2952039 : Nat := 118140960795 + 2952039 * 2 ^ 59
def prefixEnd_2952039 : Nat := 4983230072969 + 3 ^ 40 * 2952039 * 2
def baseEnd_2952039 : Nat := 112282586505043027224913

theorem tailTrace_2952039 : CollatzResearch.WordTrace tailWord_2952039 prefixEnd_2952039 112282586505043027224913 := by
  unfold tailWord_2952039
  simp only [CollatzResearch.WordTrace]
  refine ⟨107669707752274345967435171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71779805168182897311623447 107669707752274345967435171)
  ·
    refine ⟨161504561628411518951152757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107669707752274345967435171 161504561628411518951152757)
    ·
      refine ⟨15141052652663579901670571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161504561628411518951152757 15141052652663579901670571)
      ·
        refine ⟨22711578978995369852505857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15141052652663579901670571 22711578978995369852505857)
        ·
          refine ⟨17033684234246527389379393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22711578978995369852505857 17033684234246527389379393)
          ·
            refine ⟨12775263175684895542034545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17033684234246527389379393 12775263175684895542034545)
            ·
              refine ⟨9581447381763671656525909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12775263175684895542034545 9581447381763671656525909)
              ·
                refine ⟨112282586505043027224913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9581447381763671656525909 112282586505043027224913)
                ·
                  rfl

theorem cell22_2952039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 8].length) (baseStart_2952039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952039 prefixEnd_2952039 := by exact prefixLift 2952039
  have htrace : WordTrace (prefixWord ++ tailWord_2952039) baseStart_2952039 baseEnd_2952039 := by
    simpa [prefixWord, tailWord_2952039, baseEnd_2952039] using wordTrace_append hprefix tailTrace_2952039
  have hstable : (prefixWord ++ tailWord_2952039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952039).length < 2 ^ (prefixWord ++ tailWord_2952039).sum := by decide
  have hdescent : baseEnd_2952039 < baseStart_2952039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952069 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2952069 : Nat := 118140960795 + 2952069 * 2 ^ 59
def prefixEnd_2952069 : Nat := 4983230072969 + 3 ^ 40 * 2952069 * 2
def baseEnd_2952069 : Nat := 1010553548158477166774125

theorem tailTrace_2952069 : CollatzResearch.WordTrace tailWord_2952069 prefixEnd_2952069 1010553548158477166774125 := by
  unfold tailWord_2952069
  simp only [CollatzResearch.WordTrace]
  refine ⟨107670801942165661091027261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71780534628110440727351507 107670801942165661091027261)
  ·
    refine ⟨40376550728312122909135223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107670801942165661091027261 40376550728312122909135223)
    ·
      refine ⟨60564826092468184363702835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40376550728312122909135223 60564826092468184363702835)
      ·
        refine ⟨90847239138702276545554253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60564826092468184363702835 90847239138702276545554253)
        ·
          refine ⟨34067714677013353704582845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90847239138702276545554253 34067714677013353704582845)
          ·
            refine ⟨12775393003880007639218567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34067714677013353704582845 12775393003880007639218567)
            ·
              refine ⟨19163089505820011458827851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12775393003880007639218567 19163089505820011458827851)
              ·
                refine ⟨28744634258730017188241777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19163089505820011458827851 28744634258730017188241777)
                ·
                  refine ⟨21558475694047512891181333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28744634258730017188241777 21558475694047512891181333)
                  ·
                    refine ⟨1010553548158477166774125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21558475694047512891181333 1010553548158477166774125)
                    ·
                      rfl

theorem cell22_2952069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2952069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952069 prefixEnd_2952069 := by exact prefixLift 2952069
  have htrace : WordTrace (prefixWord ++ tailWord_2952069) baseStart_2952069 baseEnd_2952069 := by
    simpa [prefixWord, tailWord_2952069, baseEnd_2952069] using wordTrace_append hprefix tailTrace_2952069
  have hstable : (prefixWord ++ tailWord_2952069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952069).length < 2 ^ (prefixWord ++ tailWord_2952069).sum := by decide
  have hdescent : baseEnd_2952069 < baseStart_2952069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952148 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2952148 : Nat := 118140960795 + 2952148 * 2 ^ 59
def prefixEnd_2952148 : Nat := 4983230072969 + 3 ^ 40 * 2952148 * 2
def baseEnd_2952148 : Nat := 1010580591472947294048883

theorem tailTrace_2952148 : CollatzResearch.WordTrace tailWord_2952148 prefixEnd_2952148 1010580591472947294048883 := by
  unfold tailWord_2952148
  simp only [CollatzResearch.WordTrace]
  refine ⟨53836841654439728791576549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71782455539252971722102065 53836841654439728791576549)
  ·
    refine ⟨10094407810207449148420603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53836841654439728791576549 10094407810207449148420603)
    ·
      refine ⟨15141611715311173722630905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10094407810207449148420603 15141611715311173722630905)
      ·
        refine ⟨11356208786483380291973179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15141611715311173722630905 11356208786483380291973179)
        ·
          refine ⟨17034313179725070437959769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356208786483380291973179 17034313179725070437959769)
          ·
            refine ⟨12775734884793802828469827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17034313179725070437959769 12775734884793802828469827)
            ·
              refine ⟨19163602327190704242704741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12775734884793802828469827 19163602327190704242704741)
              ·
                refine ⟨3593175436348257045507139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19163602327190704242704741 3593175436348257045507139)
                ·
                  refine ⟨5389763154522385568260709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593175436348257045507139 5389763154522385568260709)
                  ·
                    refine ⟨1010580591472947294048883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389763154522385568260709 1010580591472947294048883)
                    ·
                      rfl

theorem cell22_2952148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2952148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952148 prefixEnd_2952148 := by exact prefixLift 2952148
  have htrace : WordTrace (prefixWord ++ tailWord_2952148) baseStart_2952148 baseEnd_2952148 := by
    simpa [prefixWord, tailWord_2952148, baseEnd_2952148] using wordTrace_append hprefix tailTrace_2952148
  have hstable : (prefixWord ++ tailWord_2952148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952148).length < 2 ^ (prefixWord ++ tailWord_2952148).sum := by decide
  have hdescent : baseEnd_2952148 < baseStart_2952148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952240 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_2952240 : Nat := 118140960795 + 2952240 * 2 ^ 59
def prefixEnd_2952240 : Nat := 4983230072969 + 3 ^ 40 * 2952240 * 2
def baseEnd_2952240 : Nat := 1010612084953089720748601

theorem tailTrace_2952240 : CollatzResearch.WordTrace tailWord_2952240 prefixEnd_2952240 1010612084953089720748601 := by
  unfold tailWord_2952240
  simp only [CollatzResearch.WordTrace]
  refine ⟨53838519412273078647751087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71784692549697438197001449 53838519412273078647751087)
  ·
    refine ⟨80757779118409617971626631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53838519412273078647751087 80757779118409617971626631)
    ·
      refine ⟨121136668677614426957439947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80757779118409617971626631 121136668677614426957439947)
      ·
        refine ⟨181705003016421640436159921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121136668677614426957439947 181705003016421640436159921)
        ·
          refine ⟨136278752262316230327119941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181705003016421640436159921 136278752262316230327119941)
          ·
            refine ⟨25552266049184293186334989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136278752262316230327119941 25552266049184293186334989)
            ·
              refine ⟨9582099768444109944875621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25552266049184293186334989 9582099768444109944875621)
              ·
                refine ⟨1796643706583270614664179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9582099768444109944875621 1796643706583270614664179)
                ·
                  refine ⟨2694965559874905921996269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796643706583270614664179 2694965559874905921996269)
                  ·
                    refine ⟨1010612084953089720748601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694965559874905921996269 1010612084953089720748601)
                    ·
                      rfl

theorem cell22_2952240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_2952240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952240 prefixEnd_2952240 := by exact prefixLift 2952240
  have htrace : WordTrace (prefixWord ++ tailWord_2952240) baseStart_2952240 baseEnd_2952240 := by
    simpa [prefixWord, tailWord_2952240, baseEnd_2952240] using wordTrace_append hprefix tailTrace_2952240
  have hstable : (prefixWord ++ tailWord_2952240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952240).length < 2 ^ (prefixWord ++ tailWord_2952240).sum := by decide
  have hdescent : baseEnd_2952240 < baseStart_2952240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952253 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 5]
def baseStart_2952253 : Nat := 118140960795 + 2952253 * 2 ^ 59
def prefixEnd_2952253 : Nat := 4983230072969 + 3 ^ 40 * 2952253 * 2
def baseEnd_2952253 : Nat := 336872178372920673391187

theorem tailTrace_2952253 : CollatzResearch.WordTrace tailWord_2952253 prefixEnd_2952253 336872178372920673391187 := by
  unfold tailWord_2952253
  simp only [CollatzResearch.WordTrace]
  refine ⟨107677512973499060515725413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71785008648999373677150275 107677512973499060515725413)
  ·
    refine ⟨20189533682531073846698515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107677512973499060515725413 20189533682531073846698515)
    ·
      refine ⟨30284300523796610770047773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20189533682531073846698515 30284300523796610770047773)
      ·
        refine ⟨11356612696423729038767915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30284300523796610770047773 11356612696423729038767915)
        ·
          refine ⟨17034919044635593558151873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356612696423729038767915 17034919044635593558151873)
          ·
            refine ⟨12776189283476695168613905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17034919044635593558151873 12776189283476695168613905)
            ·
              refine ⟨9582141962607521376460429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12776189283476695168613905 9582141962607521376460429)
              ·
                refine ⟨3593303235977820516172661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9582141962607521376460429 3593303235977820516172661)
                ·
                  refine ⟨336872178372920673391187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3593303235977820516172661 336872178372920673391187)
                  ·
                    rfl

theorem cell22_2952253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_2952253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952253 prefixEnd_2952253 := by exact prefixLift 2952253
  have htrace : WordTrace (prefixWord ++ tailWord_2952253) baseStart_2952253 baseEnd_2952253 := by
    simpa [prefixWord, tailWord_2952253, baseEnd_2952253] using wordTrace_append hprefix tailTrace_2952253
  have hstable : (prefixWord ++ tailWord_2952253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952253).length < 2 ^ (prefixWord ++ tailWord_2952253).sum := by decide
  have hdescent : baseEnd_2952253 < baseStart_2952253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952298 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_2952298 : Nat := 118140960795 + 2952298 * 2 ^ 59
def prefixEnd_2952298 : Nat := 4983230072969 + 3 ^ 40 * 2952298 * 2
def baseEnd_2952298 : Nat := 336877313179465634266141

theorem tailTrace_2952298 : CollatzResearch.WordTrace tailWord_2952298 prefixEnd_2952298 336877313179465634266141 := by
  unfold tailWord_2952298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919788564584008300278387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71786102838890688800742365 26919788564584008300278387)
  ·
    refine ⟨40379682846876012450417581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26919788564584008300278387 40379682846876012450417581)
    ·
      refine ⟨15142381067578504668906593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40379682846876012450417581 15142381067578504668906593)
      ·
        refine ⟨11356785800683878501679945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15142381067578504668906593 11356785800683878501679945)
        ·
          refine ⟨8517589350512908876259959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11356785800683878501679945 8517589350512908876259959)
          ·
            refine ⟨12776384025769363314389939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517589350512908876259959 12776384025769363314389939)
            ·
              refine ⟨19164576038654044971584909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776384025769363314389939 19164576038654044971584909)
              ·
                refine ⟨7186716014495266864344341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19164576038654044971584909 7186716014495266864344341)
                ·
                  refine ⟨336877313179465634266141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7186716014495266864344341 336877313179465634266141)
                  ·
                    rfl

theorem cell22_2952298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_2952298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952298 prefixEnd_2952298 := by exact prefixLift 2952298
  have htrace : WordTrace (prefixWord ++ tailWord_2952298) baseStart_2952298 baseEnd_2952298 := by
    simpa [prefixWord, tailWord_2952298, baseEnd_2952298] using wordTrace_append hprefix tailTrace_2952298
  have hstable : (prefixWord ++ tailWord_2952298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952298).length < 2 ^ (prefixWord ++ tailWord_2952298).sum := by decide
  have hdescent : baseEnd_2952298 < baseStart_2952298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952311 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2952311 : Nat := 118140960795 + 2952311 * 2 ^ 59
def prefixEnd_2952311 : Nat := 4983230072969 + 3 ^ 40 * 2952311 * 2
def baseEnd_2952311 : Nat := 1010636389704069202223383

theorem tailTrace_2952311 : CollatzResearch.WordTrace tailWord_2952311 prefixEnd_2952311 1010636389704069202223383 := by
  unfold tailWord_2952311
  simp only [CollatzResearch.WordTrace]
  refine ⟨107679628407288936421336787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71786418938192624280891191 107679628407288936421336787)
  ·
    refine ⟨161519442610933404632005181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107679628407288936421336787 161519442610933404632005181)
    ·
      refine ⟨60569790979100026737001943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161519442610933404632005181 60569790979100026737001943)
      ·
        refine ⟨90854686468650040105502915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60569790979100026737001943 90854686468650040105502915)
        ·
          refine ⟨136282029702975060158254373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90854686468650040105502915 136282029702975060158254373)
          ·
            refine ⟨25552880569307823779672695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136282029702975060158254373 25552880569307823779672695)
            ·
              refine ⟨38329320853961735669509043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25552880569307823779672695 38329320853961735669509043)
              ·
                refine ⟨57493981280942603504263565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38329320853961735669509043 57493981280942603504263565)
                ·
                  refine ⟨21560242980353476314098837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57493981280942603504263565 21560242980353476314098837)
                  ·
                    refine ⟨1010636389704069202223383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21560242980353476314098837 1010636389704069202223383)
                    ·
                      rfl

theorem cell22_2952311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2952311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952311 prefixEnd_2952311 := by exact prefixLift 2952311
  have htrace : WordTrace (prefixWord ++ tailWord_2952311) baseStart_2952311 baseEnd_2952311 := by
    simpa [prefixWord, tailWord_2952311, baseEnd_2952311] using wordTrace_append hprefix tailTrace_2952311
  have hstable : (prefixWord ++ tailWord_2952311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952311).length < 2 ^ (prefixWord ++ tailWord_2952311).sum := by decide
  have hdescent : baseEnd_2952311 < baseStart_2952311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952343 : List Nat := [1, 1, 3, 3, 3, 3, 8]
def baseStart_2952343 : Nat := 118140960795 + 2952343 * 2 ^ 59
def prefixEnd_2952343 : Nat := 4983230072969 + 3 ^ 40 * 2952343 * 2
def baseEnd_2952343 : Nat := 37431383109556732793455

theorem tailTrace_2952343 : CollatzResearch.WordTrace tailWord_2952343 prefixEnd_2952343 37431383109556732793455 := by
  unfold tailWord_2952343
  simp only [CollatzResearch.WordTrace]
  refine ⟨107680795543173005886501683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71787197028782003924334455 107680795543173005886501683)
  ·
    refine ⟨161521193314759508829752525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107680795543173005886501683 161521193314759508829752525)
    ·
      refine ⟨60570447493034815811157197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161521193314759508829752525 60570447493034815811157197)
      ·
        refine ⟨22713917809888055929183949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60570447493034815811157197 22713917809888055929183949)
        ·
          refine ⟨8517719178708020973443981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22713917809888055929183949 8517719178708020973443981)
          ·
            refine ⟨3194144692015507865041493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8517719178708020973443981 3194144692015507865041493)
            ·
              refine ⟨37431383109556732793455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3194144692015507865041493 37431383109556732793455)
              ·
                rfl

theorem cell22_2952343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 8].length) (baseStart_2952343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952343 prefixEnd_2952343 := by exact prefixLift 2952343
  have htrace : WordTrace (prefixWord ++ tailWord_2952343) baseStart_2952343 baseEnd_2952343 := by
    simpa [prefixWord, tailWord_2952343, baseEnd_2952343] using wordTrace_append hprefix tailTrace_2952343
  have hstable : (prefixWord ++ tailWord_2952343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952343).length < 2 ^ (prefixWord ++ tailWord_2952343).sum := by decide
  have hdescent : baseEnd_2952343 < baseStart_2952343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952405 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 5]
def baseStart_2952405 : Nat := 118140960795 + 2952405 * 2 ^ 59
def prefixEnd_2952405 : Nat := 4983230072969 + 3 ^ 40 * 2952405 * 2
def baseEnd_2952405 : Nat := 336889522608361430124365

theorem tailTrace_2952405 : CollatzResearch.WordTrace tailWord_2952405 prefixEnd_2952405 336889522608361430124365 := by
  unfold tailWord_2952405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107683056868948390475258669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71788704579298926983505779 107683056868948390475258669)
  ·
    refine ⟨40381146325855646428222001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107683056868948390475258669 40381146325855646428222001)
    ·
      refine ⟨30285859744391734821166501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40381146325855646428222001 30285859744391734821166501)
      ·
        refine ⟨5678598702073450278968719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30285859744391734821166501 5678598702073450278968719)
        ·
          refine ⟨8517898053110175418453079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678598702073450278968719 8517898053110175418453079)
          ·
            refine ⟨12776847079665263127679619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517898053110175418453079 12776847079665263127679619)
            ·
              refine ⟨19165270619497894691519429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776847079665263127679619 19165270619497894691519429)
              ·
                refine ⟨3593488241155855254659893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19165270619497894691519429 3593488241155855254659893)
                ·
                  refine ⟨336889522608361430124365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3593488241155855254659893 336889522608361430124365)
                  ·
                    rfl

theorem cell22_2952405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_2952405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952405 prefixEnd_2952405 := by exact prefixLift 2952405
  have htrace : WordTrace (prefixWord ++ tailWord_2952405) baseStart_2952405 baseEnd_2952405 := by
    simpa [prefixWord, tailWord_2952405, baseEnd_2952405] using wordTrace_append hprefix tailTrace_2952405
  have hstable : (prefixWord ++ tailWord_2952405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952405).length < 2 ^ (prefixWord ++ tailWord_2952405).sum := by decide
  have hdescent : baseEnd_2952405 < baseStart_2952405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952452 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2952452 : Nat := 118140960795 + 2952452 * 2 ^ 59
def prefixEnd_2952452 : Nat := 4983230072969 + 3 ^ 40 * 2952452 * 2
def baseEnd_2952452 : Nat := 1010684656885591834447951

theorem tailTrace_2952452 : CollatzResearch.WordTrace tailWord_2952452 prefixEnd_2952452 1010684656885591834447951 := by
  unfold tailWord_2952452
  simp only [CollatzResearch.WordTrace]
  refine ⟨53842385549889058751109805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71789847399852078334813073 53842385549889058751109805)
  ·
    refine ⟨20190894581208397031666177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53842385549889058751109805 20190894581208397031666177)
    ·
      refine ⟨15143170935906297773749633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20190894581208397031666177 15143170935906297773749633)
      ·
        refine ⟨11357378201929723330312225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15143170935906297773749633 11357378201929723330312225)
        ·
          refine ⟨8518033651447292497734169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11357378201929723330312225 8518033651447292497734169)
          ·
            refine ⟨6388525238585469373300627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8518033651447292497734169 6388525238585469373300627)
            ·
              refine ⟨9582787857878204059950941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388525238585469373300627 9582787857878204059950941)
              ·
                refine ⟨3593545446704326522481603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9582787857878204059950941 3593545446704326522481603)
                ·
                  refine ⟨5390318170056489783722405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593545446704326522481603 5390318170056489783722405)
                  ·
                    refine ⟨1010684656885591834447951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390318170056489783722405 1010684656885591834447951)
                    ·
                      rfl

theorem cell22_2952452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2952452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952452 prefixEnd_2952452 := by exact prefixLift 2952452
  have htrace : WordTrace (prefixWord ++ tailWord_2952452) baseStart_2952452 baseEnd_2952452 := by
    simpa [prefixWord, tailWord_2952452, baseEnd_2952452] using wordTrace_append hprefix tailTrace_2952452
  have hstable : (prefixWord ++ tailWord_2952452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952452).length < 2 ^ (prefixWord ++ tailWord_2952452).sum := by decide
  have hdescent : baseEnd_2952452 < baseStart_2952452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952465 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_2952465 : Nat := 118140960795 + 2952465 * 2 ^ 59
def prefixEnd_2952465 : Nat := 4983230072969 + 3 ^ 40 * 2952465 * 2
def baseEnd_2952465 : Nat := 1010689107051264133872911

theorem tailTrace_2952465 : CollatzResearch.WordTrace tailWord_2952465 prefixEnd_2952465 1010689107051264133872911 := by
  unfold tailWord_2952465
  simp only [CollatzResearch.WordTrace]
  refine ⟨107685245248731020722442849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71790163499154013814961899 107685245248731020722442849)
  ·
    refine ⟨80763933936548265541832137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107685245248731020722442849 80763933936548265541832137)
    ·
      refine ⟨60572950452411199156374103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80763933936548265541832137 60572950452411199156374103)
      ·
        refine ⟨90859425678616798734561155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60572950452411199156374103 90859425678616798734561155)
        ·
          refine ⟨136289138517925198101841733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90859425678616798734561155 136289138517925198101841733)
          ·
            refine ⟨25554213472110974644095325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136289138517925198101841733 25554213472110974644095325)
            ·
              refine ⟨9582830052041615491535747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25554213472110974644095325 9582830052041615491535747)
              ·
                refine ⟨14374245078062423237303621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9582830052041615491535747 14374245078062423237303621)
                ·
                  refine ⟨2695170952136704356994429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14374245078062423237303621 2695170952136704356994429)
                  ·
                    refine ⟨1010689107051264133872911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695170952136704356994429 1010689107051264133872911)
                    ·
                      rfl

theorem cell22_2952465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_2952465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952465 prefixEnd_2952465 := by exact prefixLift 2952465
  have htrace : WordTrace (prefixWord ++ tailWord_2952465) baseStart_2952465 baseEnd_2952465 := by
    simpa [prefixWord, tailWord_2952465, baseEnd_2952465] using wordTrace_append hprefix tailTrace_2952465
  have hstable : (prefixWord ++ tailWord_2952465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952465).length < 2 ^ (prefixWord ++ tailWord_2952465).sum := by decide
  have hdescent : baseEnd_2952465 < baseStart_2952465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952518 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2952518 : Nat := 118140960795 + 2952518 * 2 ^ 59
def prefixEnd_2952518 : Nat := 4983230072969 + 3 ^ 40 * 2952518 * 2
def baseEnd_2952518 : Nat := 336902416678129887432583

theorem tailTrace_2952518 : CollatzResearch.WordTrace tailWord_2952518 prefixEnd_2952518 336902416678129887432583 := by
  unfold tailWord_2952518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365224322423094086691319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71791452211692673849414805 3365224322423094086691319)
  ·
    refine ⟨5047836483634641130036979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365224322423094086691319 5047836483634641130036979)
    ·
      refine ⟨7571754725451961695055469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5047836483634641130036979 7571754725451961695055469)
      ·
        refine ⟨2839408022044485635645801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7571754725451961695055469 2839408022044485635645801)
        ·
          refine ⟨2129556016533364226734351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839408022044485635645801 2129556016533364226734351)
          ·
            refine ⟨3194334024800046340101527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129556016533364226734351 3194334024800046340101527)
            ·
              refine ⟨4791501037200069510152291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194334024800046340101527 4791501037200069510152291)
              ·
                refine ⟨7187251555800104265228437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791501037200069510152291 7187251555800104265228437)
                ·
                  refine ⟨336902416678129887432583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7187251555800104265228437 336902416678129887432583)
                  ·
                    rfl

theorem cell22_2952518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2952518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952518 prefixEnd_2952518 := by exact prefixLift 2952518
  have htrace : WordTrace (prefixWord ++ tailWord_2952518) baseStart_2952518 baseEnd_2952518 := by
    simpa [prefixWord, tailWord_2952518, baseEnd_2952518] using wordTrace_append hprefix tailTrace_2952518
  have hstable : (prefixWord ++ tailWord_2952518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952518).length < 2 ^ (prefixWord ++ tailWord_2952518).sum := by decide
  have hdescent : baseEnd_2952518 < baseStart_2952518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952578 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2952578 : Nat := 118140960795 + 2952578 * 2 ^ 59
def prefixEnd_2952578 : Nat := 4983230072969 + 3 ^ 40 * 2952578 * 2
def baseEnd_2952578 : Nat := 1010727789260569505797565

theorem tailTrace_2952578 : CollatzResearch.WordTrace tailWord_2952578 prefixEnd_2952578 1010727789260569505797565 := by
  unfold tailWord_2952578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26922341674330410255326597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71792911131547760680870925 26922341674330410255326597)
  ·
    refine ⟨5047939063936951922873737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26922341674330410255326597 5047939063936951922873737)
    ·
      refine ⟨3785954297952713942155303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5047939063936951922873737 3785954297952713942155303)
      ·
        refine ⟨5678931446929070913232955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785954297952713942155303 5678931446929070913232955)
        ·
          refine ⟨8518397170393606369849433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678931446929070913232955 8518397170393606369849433)
          ·
            refine ⟨6388797877795204777387075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8518397170393606369849433 6388797877795204777387075)
            ·
              refine ⟨9583196816692807166080613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6388797877795204777387075 9583196816692807166080613)
              ·
                refine ⟨1796849403129901343640115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9583196816692807166080613 1796849403129901343640115)
                ·
                  refine ⟨2695274104694852015460173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796849403129901343640115 2695274104694852015460173)
                  ·
                    refine ⟨1010727789260569505797565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695274104694852015460173 1010727789260569505797565)
                    ·
                      rfl

theorem cell22_2952578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2952578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952578 prefixEnd_2952578 := by exact prefixLift 2952578
  have htrace : WordTrace (prefixWord ++ tailWord_2952578) baseStart_2952578 baseEnd_2952578 := by
    simpa [prefixWord, tailWord_2952578, baseEnd_2952578] using wordTrace_append hprefix tailTrace_2952578
  have hstable : (prefixWord ++ tailWord_2952578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952578).length < 2 ^ (prefixWord ++ tailWord_2952578).sum := by decide
  have hdescent : baseEnd_2952578 < baseStart_2952578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952621 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2952621 : Nat := 118140960795 + 2952621 * 2 ^ 59
def prefixEnd_2952621 : Nat := 4983230072969 + 3 ^ 40 * 2952621 * 2
def baseEnd_2952621 : Nat := 1010742509039331726972433

theorem tailTrace_2952621 : CollatzResearch.WordTrace tailWord_2952621 prefixEnd_2952621 1010742509039331726972433 := by
  unfold tailWord_2952621
  simp only [CollatzResearch.WordTrace]
  refine ⟨107690935036165859365121717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71793956690777239576747811 107690935036165859365121717)
  ·
    refine ⟨10096025159640549315480161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107690935036165859365121717 10096025159640549315480161)
    ·
      refine ⟨7572018869730411986610121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10096025159640549315480161 7572018869730411986610121)
      ·
        refine ⟨5679014152297808989957591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7572018869730411986610121 5679014152297808989957591)
        ·
          refine ⟨8518521228446713484936387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679014152297808989957591 8518521228446713484936387)
          ·
            refine ⟨12777781842670070227404581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518521228446713484936387 12777781842670070227404581)
            ·
              refine ⟨2395834095500638167638359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12777781842670070227404581 2395834095500638167638359)
              ·
                refine ⟨3593751143250957251457539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395834095500638167638359 3593751143250957251457539)
                ·
                  refine ⟨5390626714876435877186309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593751143250957251457539 5390626714876435877186309)
                  ·
                    refine ⟨1010742509039331726972433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390626714876435877186309 1010742509039331726972433)
                    ·
                      rfl

theorem cell22_2952621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2952621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952621 prefixEnd_2952621 := by exact prefixLift 2952621
  have htrace : WordTrace (prefixWord ++ tailWord_2952621) baseStart_2952621 baseEnd_2952621 := by
    simpa [prefixWord, tailWord_2952621, baseEnd_2952621] using wordTrace_append hprefix tailTrace_2952621
  have hstable : (prefixWord ++ tailWord_2952621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952621).length < 2 ^ (prefixWord ++ tailWord_2952621).sum := by decide
  have hdescent : baseEnd_2952621 < baseStart_2952621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952702 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2952702 : Nat := 118140960795 + 2952702 * 2 ^ 59
def prefixEnd_2952702 : Nat := 4983230072969 + 3 ^ 40 * 2952702 * 2
def baseEnd_2952702 : Nat := 1010770236994674515697185

theorem tailTrace_2952702 : CollatzResearch.WordTrace tailWord_2952702 prefixEnd_2952702 1010770236994674515697185 := by
  unfold tailWord_2952702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461736168609051274852545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71795926232581606799213573 13461736168609051274852545)
  ·
    refine ⟨10096302126456788456139409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13461736168609051274852545 10096302126456788456139409)
    ·
      refine ⟨7572226594842591342104557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10096302126456788456139409 7572226594842591342104557)
      ·
        refine ⟨2839584973065971753289209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7572226594842591342104557 2839584973065971753289209)
        ·
          refine ⟨2129688729799478814966907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839584973065971753289209 2129688729799478814966907)
          ·
            refine ⟨3194533094699218222450361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129688729799478814966907 3194533094699218222450361)
            ·
              refine ⟨2395899821024413666837771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194533094699218222450361 2395899821024413666837771)
              ·
                refine ⟨3593849731536620500256657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395899821024413666837771 3593849731536620500256657)
                ·
                  refine ⟨2695387298652465375192493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593849731536620500256657 2695387298652465375192493)
                  ·
                    refine ⟨1010770236994674515697185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695387298652465375192493 1010770236994674515697185)
                    ·
                      rfl

theorem cell22_2952702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2952702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952702 prefixEnd_2952702 := by exact prefixLift 2952702
  have htrace : WordTrace (prefixWord ++ tailWord_2952702) baseStart_2952702 baseEnd_2952702 := by
    simpa [prefixWord, tailWord_2952702, baseEnd_2952702] using wordTrace_append hprefix tailTrace_2952702
  have hstable : (prefixWord ++ tailWord_2952702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952702).length < 2 ^ (prefixWord ++ tailWord_2952702).sum := by decide
  have hdescent : baseEnd_2952702 < baseStart_2952702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952769 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2952769 : Nat := 118140960795 + 2952769 * 2 ^ 59
def prefixEnd_2952769 : Nat := 4983230072969 + 3 ^ 40 * 2952769 * 2
def baseEnd_2952769 : Nat := 1010793172463908674271979

theorem tailTrace_2952769 : CollatzResearch.WordTrace tailWord_2952769 prefixEnd_2952769 1010793172463908674271979 := by
  unfold tailWord_2952769
  simp only [CollatzResearch.WordTrace]
  refine ⟨107696333039629680641509361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71797555359753120427672907 107696333039629680641509361)
  ·
    refine ⟨80772249779722260481132021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107696333039629680641509361 80772249779722260481132021)
    ·
      refine ⟨7572398416848961920106127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80772249779722260481132021 7572398416848961920106127)
      ·
        refine ⟨11358597625273442880159191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572398416848961920106127 11358597625273442880159191)
        ·
          refine ⟨17037896437910164320238787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358597625273442880159191 17037896437910164320238787)
          ·
            refine ⟨25556844656865246480358181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037896437910164320238787 25556844656865246480358181)
            ·
              refine ⟨4791908373162233715067159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25556844656865246480358181 4791908373162233715067159)
              ·
                refine ⟨7187862559743350572600739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791908373162233715067159 7187862559743350572600739)
                ·
                  refine ⟨10781793839615025858901109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7187862559743350572600739 10781793839615025858901109)
                  ·
                    refine ⟨1010793172463908674271979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10781793839615025858901109 1010793172463908674271979)
                    ·
                      rfl

theorem cell22_2952769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2952769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952769 prefixEnd_2952769 := by exact prefixLift 2952769
  have htrace : WordTrace (prefixWord ++ tailWord_2952769) baseStart_2952769 baseEnd_2952769 := by
    simpa [prefixWord, tailWord_2952769, baseEnd_2952769] using wordTrace_append hprefix tailTrace_2952769
  have hstable : (prefixWord ++ tailWord_2952769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952769).length < 2 ^ (prefixWord ++ tailWord_2952769).sum := by decide
  have hdescent : baseEnd_2952769 < baseStart_2952769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952790 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2952790 : Nat := 118140960795 + 2952790 * 2 ^ 59
def prefixEnd_2952790 : Nat := 4983230072969 + 3 ^ 40 * 2952790 * 2
def baseEnd_2952790 : Nat := 1010800361193071619496915

theorem tailTrace_2952790 : CollatzResearch.WordTrace tailWord_2952790 prefixEnd_2952790 1010800361193071619496915 := by
  unfold tailWord_2952790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731068685784600076751489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71798065981702400818682549 6731068685784600076751489)
  ·
    refine ⟨5048301514338450057563617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6731068685784600076751489 5048301514338450057563617)
    ·
      refine ⟨3786226135753837543172713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048301514338450057563617 3786226135753837543172713)
      ·
        refine ⟨2839669601815378157379535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786226135753837543172713 2839669601815378157379535)
        ·
          refine ⟨4259504402723067236069303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839669601815378157379535 4259504402723067236069303)
          ·
            refine ⟨6389256604084600854103955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259504402723067236069303 6389256604084600854103955)
            ·
              refine ⟨9583884906126901281155933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389256604084600854103955 9583884906126901281155933)
              ·
                refine ⟨3593956839797587980433475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9583884906126901281155933 3593956839797587980433475)
                ·
                  refine ⟨5390935259696381970650213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593956839797587980433475 5390935259696381970650213)
                  ·
                    refine ⟨1010800361193071619496915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390935259696381970650213 1010800361193071619496915)
                    ·
                      rfl

theorem cell22_2952790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2952790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952790 prefixEnd_2952790 := by exact prefixLift 2952790
  have htrace : WordTrace (prefixWord ++ tailWord_2952790) baseStart_2952790 baseEnd_2952790 := by
    simpa [prefixWord, tailWord_2952790, baseEnd_2952790] using wordTrace_append hprefix tailTrace_2952790
  have hstable : (prefixWord ++ tailWord_2952790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952790).length < 2 ^ (prefixWord ++ tailWord_2952790).sum := by decide
  have hdescent : baseEnd_2952790 < baseStart_2952790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952865 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_2952865 : Nat := 118140960795 + 2952865 * 2 ^ 59
def prefixEnd_2952865 : Nat := 4983230072969 + 3 ^ 40 * 2952865 * 2
def baseEnd_2952865 : Nat := 1010826035225796423871685

theorem tailTrace_2952865 : CollatzResearch.WordTrace tailWord_2952865 prefixEnd_2952865 1010826035225796423871685 := by
  unfold tailWord_2952865
  simp only [CollatzResearch.WordTrace]
  refine ⟨107699834447281889037004049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71799889631521259358002699 107699834447281889037004049)
  ·
    refine ⟨80774875835461416777753037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107699834447281889037004049 80774875835461416777753037)
    ·
      refine ⟨30290578438298031291657389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80774875835461416777753037 30290578438298031291657389)
      ·
        refine ⟨11358966914361761734371521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30290578438298031291657389 11358966914361761734371521)
        ·
          refine ⟨8519225185771321300778641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11358966914361761734371521 8519225185771321300778641)
          ·
            refine ⟨6389418889328490975583981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519225185771321300778641 6389418889328490975583981)
            ·
              refine ⟨2396032083498184115843993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6389418889328490975583981 2396032083498184115843993)
              ·
                refine ⟨1797024062623638086882995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396032083498184115843993 1797024062623638086882995)
                ·
                  refine ⟨2695536093935457130324493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797024062623638086882995 2695536093935457130324493)
                  ·
                    refine ⟨1010826035225796423871685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695536093935457130324493 1010826035225796423871685)
                    ·
                      rfl

theorem cell22_2952865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_2952865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952865 prefixEnd_2952865 := by exact prefixLift 2952865
  have htrace : WordTrace (prefixWord ++ tailWord_2952865) baseStart_2952865 baseEnd_2952865 := by
    simpa [prefixWord, tailWord_2952865, baseEnd_2952865] using wordTrace_append hprefix tailTrace_2952865
  have hstable : (prefixWord ++ tailWord_2952865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952865).length < 2 ^ (prefixWord ++ tailWord_2952865).sum := by decide
  have hdescent : baseEnd_2952865 < baseStart_2952865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952878 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_2952878 : Nat := 118140960795 + 2952878 * 2 ^ 59
def prefixEnd_2952878 : Nat := 4983230072969 + 3 ^ 40 * 2952878 * 2
def baseEnd_2952878 : Nat := 336943495130489574432215

theorem tailTrace_2952878 : CollatzResearch.WordTrace tailWord_2952878 prefixEnd_2952878 336943495130489574432215 := by
  unfold tailWord_2952878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462538574529349032153411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71800205730823194838151525 13462538574529349032153411)
  ·
    refine ⟨20193807861794023548230117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13462538574529349032153411 20193807861794023548230117)
    ·
      refine ⟨3786338974086379415293147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20193807861794023548230117 3786338974086379415293147)
      ·
        refine ⟨5679508461129569122939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786338974086379415293147 5679508461129569122939721)
        ·
          refine ⟨4259631345847176842204791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679508461129569122939721 4259631345847176842204791)
          ·
            refine ⟨6389447018770765263307187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259631345847176842204791 6389447018770765263307187)
            ·
              refine ⟨9584170528156147894960781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389447018770765263307187 9584170528156147894960781)
              ·
                refine ⟨3594063948058555460610293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9584170528156147894960781 3594063948058555460610293)
                ·
                  refine ⟨336943495130489574432215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594063948058555460610293 336943495130489574432215)
                  ·
                    rfl

theorem cell22_2952878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_2952878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952878 prefixEnd_2952878 := by exact prefixLift 2952878
  have htrace : WordTrace (prefixWord ++ tailWord_2952878) baseStart_2952878 baseEnd_2952878 := by
    simpa [prefixWord, tailWord_2952878, baseEnd_2952878] using wordTrace_append hprefix tailTrace_2952878
  have hstable : (prefixWord ++ tailWord_2952878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952878).length < 2 ^ (prefixWord ++ tailWord_2952878).sum := by decide
  have hdescent : baseEnd_2952878 < baseStart_2952878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952904 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_2952904 : Nat := 118140960795 + 2952904 * 2 ^ 59
def prefixEnd_2952904 : Nat := 4983230072969 + 3 ^ 40 * 2952904 * 2
def baseEnd_2952904 : Nat := 1010839385722813322146565

theorem tailTrace_2952904 : CollatzResearch.WordTrace tailWord_2952904 prefixEnd_2952904 1010839385722813322146565 := by
  unfold tailWord_2952904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53850628447070299348836883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71800837929427065798449177 53850628447070299348836883)
  ·
    refine ⟨80775942670605449023255325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53850628447070299348836883 80775942670605449023255325)
    ·
      refine ⟨30290978501477043383720747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80775942670605449023255325 30290978501477043383720747)
      ·
        refine ⟨45436467752215565075581121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30290978501477043383720747 45436467752215565075581121)
        ·
          refine ⟨34077350814161673806685841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45436467752215565075581121 34077350814161673806685841)
          ·
            refine ⟨25558013110621255355014381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34077350814161673806685841 25558013110621255355014381)
            ·
              refine ⟨9584254916482970758130393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25558013110621255355014381 9584254916482970758130393)
              ·
                refine ⟨7188191187362228068597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584254916482970758130393 7188191187362228068597795)
                ·
                  refine ⟨10782286781043342102896693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7188191187362228068597795 10782286781043342102896693)
                  ·
                    refine ⟨1010839385722813322146565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10782286781043342102896693 1010839385722813322146565)
                    ·
                      rfl

theorem cell22_2952904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_2952904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952904 prefixEnd_2952904 := by exact prefixLift 2952904
  have htrace : WordTrace (prefixWord ++ tailWord_2952904) baseStart_2952904 baseEnd_2952904 := by
    simpa [prefixWord, tailWord_2952904, baseEnd_2952904] using wordTrace_append hprefix tailTrace_2952904
  have hstable : (prefixWord ++ tailWord_2952904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952904).length < 2 ^ (prefixWord ++ tailWord_2952904).sum := by decide
  have hdescent : baseEnd_2952904 < baseStart_2952904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952917 : List Nat := [1, 3, 2, 16]
def baseStart_2952917 : Nat := 118140960795 + 2952917 * 2 ^ 59
def prefixEnd_2952917 : Nat := 4983230072969 + 3 ^ 40 * 2952917 * 2
def baseEnd_2952917 : Nat := 1386617058831941867725

theorem tailTrace_2952917 : CollatzResearch.WordTrace tailWord_2952917 prefixEnd_2952917 1386617058831941867725 := by
  unfold tailWord_2952917
  simp only [CollatzResearch.WordTrace]
  refine ⟨107701731043093501917897005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71801154028729001278598003 107701731043093501917897005)
  ·
    refine ⟨40388149141160063219211377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107701731043093501917897005 40388149141160063219211377)
    ·
      refine ⟨30291111855870047414408533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40388149141160063219211377 30291111855870047414408533)
      ·
        refine ⟨1386617058831941867725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 30291111855870047414408533 1386617058831941867725)
        ·
          rfl

theorem cell22_2952917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 16].length) (baseStart_2952917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952917 prefixEnd_2952917 := by exact prefixLift 2952917
  have htrace : WordTrace (prefixWord ++ tailWord_2952917) baseStart_2952917 baseEnd_2952917 := by
    simpa [prefixWord, tailWord_2952917, baseEnd_2952917] using wordTrace_append hprefix tailTrace_2952917
  have hstable : (prefixWord ++ tailWord_2952917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952917).length < 2 ^ (prefixWord ++ tailWord_2952917).sum := by decide
  have hdescent : baseEnd_2952917 < baseStart_2952917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952919 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_2952919 : Nat := 118140960795 + 2952919 * 2 ^ 59
def prefixEnd_2952919 : Nat := 4983230072969 + 3 ^ 40 * 2952919 * 2
def baseEnd_2952919 : Nat := 1010844520529358283021519

theorem tailTrace_2952919 : CollatzResearch.WordTrace tailWord_2952919 prefixEnd_2952919 1010844520529358283021519 := by
  unfold tailWord_2952919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107701803989086256259469811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71801202659390837506313207 107701803989086256259469811)
  ·
    refine ⟨161552705983629384389204717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107701803989086256259469811 161552705983629384389204717)
    ·
      refine ⟨60582264743861019145951769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161552705983629384389204717 60582264743861019145951769)
      ·
        refine ⟨45436698557895764359463827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60582264743861019145951769 45436698557895764359463827)
        ·
          refine ⟨68155047836843646539195741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45436698557895764359463827 68155047836843646539195741)
          ·
            refine ⟨25558142938816367452198403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68155047836843646539195741 25558142938816367452198403)
            ·
              refine ⟨38337214408224551178297605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25558142938816367452198403 38337214408224551178297605)
              ·
                refine ⟨7188227701542103345930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38337214408224551178297605 7188227701542103345930801)
                ·
                  refine ⟨5391170776156577509448101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188227701542103345930801 5391170776156577509448101)
                  ·
                    refine ⟨1010844520529358283021519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391170776156577509448101 1010844520529358283021519)
                    ·
                      rfl

theorem cell22_2952919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_2952919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952919 prefixEnd_2952919 := by exact prefixLift 2952919
  have htrace : WordTrace (prefixWord ++ tailWord_2952919) baseStart_2952919 baseEnd_2952919 := by
    simpa [prefixWord, tailWord_2952919, baseEnd_2952919] using wordTrace_append hprefix tailTrace_2952919
  have hstable : (prefixWord ++ tailWord_2952919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952919).length < 2 ^ (prefixWord ++ tailWord_2952919).sum := by decide
  have hdescent : baseEnd_2952919 < baseStart_2952919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952921 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_2952921 : Nat := 118140960795 + 2952921 * 2 ^ 59
def prefixEnd_2952921 : Nat := 4983230072969 + 3 ^ 40 * 2952921 * 2
def baseEnd_2952921 : Nat := 1010845205170230944471513

theorem tailTrace_2952921 : CollatzResearch.WordTrace tailWord_2952921 prefixEnd_2952921 1010845205170230944471513 := by
  unfold tailWord_2952921
  simp only [CollatzResearch.WordTrace]
  refine ⟨107701876935079010601042617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71801251290052673734028411 107701876935079010601042617)
  ·
    refine ⟨80776407701309257950781963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107701876935079010601042617 80776407701309257950781963)
    ·
      refine ⟨121164611551963886926172945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80776407701309257950781963 121164611551963886926172945)
      ·
        refine ⟨90873458663972915194629709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121164611551963886926172945 90873458663972915194629709)
        ·
          refine ⟨34077546998989843197986141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90873458663972915194629709 34077546998989843197986141)
          ·
            refine ⟨12779080124621191199244803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34077546998989843197986141 12779080124621191199244803)
            ·
              refine ⟨19168620186931786798867205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12779080124621191199244803 19168620186931786798867205)
              ·
                refine ⟨3594116285049710024787601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19168620186931786798867205 3594116285049710024787601)
                ·
                  refine ⟨2695587213787282518590701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594116285049710024787601 2695587213787282518590701)
                  ·
                    refine ⟨1010845205170230944471513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695587213787282518590701 1010845205170230944471513)
                    ·
                      rfl

theorem cell22_2952921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_2952921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952921 prefixEnd_2952921 := by exact prefixLift 2952921
  have htrace : WordTrace (prefixWord ++ tailWord_2952921) baseStart_2952921 baseEnd_2952921 := by
    simpa [prefixWord, tailWord_2952921, baseEnd_2952921] using wordTrace_append hprefix tailTrace_2952921
  have hstable : (prefixWord ++ tailWord_2952921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952921).length < 2 ^ (prefixWord ++ tailWord_2952921).sum := by decide
  have hdescent : baseEnd_2952921 < baseStart_2952921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952979 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 5]
def baseStart_2952979 : Nat := 118140960795 + 2952979 * 2 ^ 59
def prefixEnd_2952979 : Nat := 4983230072969 + 3 ^ 40 * 2952979 * 2
def baseEnd_2952979 : Nat := 336955019918512708840445

theorem tailTrace_2952979 : CollatzResearch.WordTrace tailWord_2952979 prefixEnd_2952979 336955019918512708840445 := by
  unfold tailWord_2952979
  simp only [CollatzResearch.WordTrace]
  refine ⟨107703992368868886506653991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71802661579245924337769327 107703992368868886506653991)
  ·
    refine ⟨161555988553303329759980987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107703992368868886506653991 161555988553303329759980987)
    ·
      refine ⟨242333982829954994639971481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161555988553303329759980987 242333982829954994639971481)
      ·
        refine ⟨181750487122466245979978611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242333982829954994639971481 181750487122466245979978611)
        ·
          refine ⟨272625730683699368969967917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181750487122466245979978611 272625730683699368969967917)
          ·
            refine ⟨102234649006387263363737969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272625730683699368969967917 102234649006387263363737969)
            ·
              refine ⟨76675986754790447522803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102234649006387263363737969 76675986754790447522803477)
              ·
                refine ⟨3594186879130802227631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76675986754790447522803477 3594186879130802227631413)
                ·
                  refine ⟨336955019918512708840445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594186879130802227631413 336955019918512708840445)
                  ·
                    rfl

theorem cell22_2952979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 5].length) (baseStart_2952979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952979 prefixEnd_2952979 := by exact prefixLift 2952979
  have htrace : WordTrace (prefixWord ++ tailWord_2952979) baseStart_2952979 baseEnd_2952979 := by
    simpa [prefixWord, tailWord_2952979, baseEnd_2952979] using wordTrace_append hprefix tailTrace_2952979
  have hstable : (prefixWord ++ tailWord_2952979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952979).length < 2 ^ (prefixWord ++ tailWord_2952979).sum := by decide
  have hdescent : baseEnd_2952979 < baseStart_2952979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2952983 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 3, 3]
def baseStart_2952983 : Nat := 118140960795 + 2952983 * 2 ^ 59
def prefixEnd_2952983 : Nat := 4983230072969 + 3 ^ 40 * 2952983 * 2
def baseEnd_2952983 : Nat := 1010866429037283449421323

theorem tailTrace_2952983 : CollatzResearch.WordTrace tailWord_2952983 prefixEnd_2952983 1010866429037283449421323 := by
  unfold tailWord_2952983
  simp only [CollatzResearch.WordTrace]
  refine ⟨107704138260854395189799603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71802758840569596793199735 107704138260854395189799603)
  ·
    refine ⟨161556207391281592784699405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107704138260854395189799603 161556207391281592784699405)
    ·
      refine ⟨60583577771730597294262277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161556207391281592784699405 60583577771730597294262277)
      ·
        refine ⟨11359420832199486992674177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60583577771730597294262277 11359420832199486992674177)
        ·
          refine ⟨8519565624149615244505633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11359420832199486992674177 8519565624149615244505633)
          ·
            refine ⟨6389674218112211433379225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519565624149615244505633 6389674218112211433379225)
            ·
              refine ⟨4792255663584158575034419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6389674218112211433379225 4792255663584158575034419)
              ·
                refine ⟨7188383495376237862551629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792255663584158575034419 7188383495376237862551629)
                ·
                  refine ⟨2695643810766089198456861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7188383495376237862551629 2695643810766089198456861)
                  ·
                    refine ⟨1010866429037283449421323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695643810766089198456861 1010866429037283449421323)
                    ·
                      rfl

theorem cell22_2952983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_2952983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2952983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2952983 prefixEnd_2952983 := by exact prefixLift 2952983
  have htrace : WordTrace (prefixWord ++ tailWord_2952983) baseStart_2952983 baseEnd_2952983 := by
    simpa [prefixWord, tailWord_2952983, baseEnd_2952983] using wordTrace_append hprefix tailTrace_2952983
  have hstable : (prefixWord ++ tailWord_2952983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2952983).length < 2 ^ (prefixWord ++ tailWord_2952983).sum := by decide
  have hdescent : baseEnd_2952983 < baseStart_2952983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2952983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953041 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 6]
def baseStart_2953041 : Nat := 118140960795 + 2953041 * 2 ^ 59
def prefixEnd_2953041 : Nat := 4983230072969 + 3 ^ 40 * 2953041 * 2
def baseEnd_2953041 : Nat := 336962094540863543823715

theorem tailTrace_2953041 : CollatzResearch.WordTrace tailWord_2953041 prefixEnd_2953041 336962094540863543823715 := by
  unfold tailWord_2953041
  simp only [CollatzResearch.WordTrace]
  refine ⟨107706253694644271095410977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71804169129762847396940651 107706253694644271095410977)
  ·
    refine ⟨80779690270983203321558233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107706253694644271095410977 80779690270983203321558233)
    ·
      refine ⟨60584767703237402491168675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80779690270983203321558233 60584767703237402491168675)
      ·
        refine ⟨90877151554856103736753013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60584767703237402491168675 90877151554856103736753013)
        ·
          refine ⟨8519732958267759725320595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90877151554856103736753013 8519732958267759725320595)
          ·
            refine ⟨12779599437401639587980893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519732958267759725320595 12779599437401639587980893)
            ·
              refine ⟨4792349789025614845492835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12779599437401639587980893 4792349789025614845492835)
              ·
                refine ⟨7188524683538422268239253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792349789025614845492835 7188524683538422268239253)
                ·
                  refine ⟨336962094540863543823715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7188524683538422268239253 336962094540863543823715)
                  ·
                    rfl

theorem cell22_2953041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_2953041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953041 prefixEnd_2953041 := by exact prefixLift 2953041
  have htrace : WordTrace (prefixWord ++ tailWord_2953041) baseStart_2953041 baseEnd_2953041 := by
    simpa [prefixWord, tailWord_2953041, baseEnd_2953041] using wordTrace_append hprefix tailTrace_2953041
  have hstable : (prefixWord ++ tailWord_2953041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953041).length < 2 ^ (prefixWord ++ tailWord_2953041).sum := by decide
  have hdescent : baseEnd_2953041 < baseStart_2953041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953060 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_2953060 : Nat := 118140960795 + 2953060 * 2 ^ 59
def prefixEnd_2953060 : Nat := 4983230072969 + 3 ^ 40 * 2953060 * 2
def baseEnd_2953060 : Nat := 1010892787710880915246087

theorem tailTrace_2953060 : CollatzResearch.WordTrace tailWord_2953060 prefixEnd_2953060 1010892787710880915246087 := by
  unfold tailWord_2953060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53853473340787718670176317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71804631121050291560235089 53853473340787718670176317)
  ·
    refine ⟨20195052502795394501316119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53853473340787718670176317 20195052502795394501316119)
    ·
      refine ⟨30292578754193091751974179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20195052502795394501316119 30292578754193091751974179)
      ·
        refine ⟨45438868131289637627961269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30292578754193091751974179 45438868131289637627961269)
        ·
          refine ⟨4259893887308403527621369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45438868131289637627961269 4259893887308403527621369)
          ·
            refine ⟨3194920415481302645716027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4259893887308403527621369 3194920415481302645716027)
            ·
              refine ⟨4792380623221953968574041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194920415481302645716027 4792380623221953968574041)
              ·
                refine ⟨3594285467416465476430531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4792380623221953968574041 3594285467416465476430531)
                ·
                  refine ⟨5391428201124698214645797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594285467416465476430531 5391428201124698214645797)
                  ·
                    refine ⟨1010892787710880915246087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391428201124698214645797 1010892787710880915246087)
                    ·
                      rfl

theorem cell22_2953060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_2953060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953060 prefixEnd_2953060 := by exact prefixLift 2953060
  have htrace : WordTrace (prefixWord ++ tailWord_2953060) baseStart_2953060 baseEnd_2953060 := by
    simpa [prefixWord, tailWord_2953060, baseEnd_2953060] using wordTrace_append hprefix tailTrace_2953060
  have hstable : (prefixWord ++ tailWord_2953060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953060).length < 2 ^ (prefixWord ++ tailWord_2953060).sum := by decide
  have hdescent : baseEnd_2953060 < baseStart_2953060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953122 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2953122 : Nat := 118140960795 + 2953122 * 2 ^ 59
def prefixEnd_2953122 : Nat := 4983230072969 + 3 ^ 40 * 2953122 * 2
def baseEnd_2953122 : Nat := 1010914011577933420195897

theorem tailTrace_2953122 : CollatzResearch.WordTrace tailWord_2953122 prefixEnd_2953122 1010914011577933420195897 := by
  unfold tailWord_2953122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927302001837705482277405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71806138671567214619406413 26927302001837705482277405)
  ·
    refine ⟨10097738250689139555854027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26927302001837705482277405 10097738250689139555854027)
    ·
      refine ⟨15146607376033709333781041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10097738250689139555854027 15146607376033709333781041)
      ·
        refine ⟨11359955532025282000335781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15146607376033709333781041 11359955532025282000335781)
        ·
          refine ⟨2129991662254740375062959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11359955532025282000335781 2129991662254740375062959)
          ·
            refine ⟨3194987493382110562594439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129991662254740375062959 3194987493382110562594439)
            ·
              refine ⟨4792481240073165843891659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194987493382110562594439 4792481240073165843891659)
              ·
                refine ⟨7188721860109748765837489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792481240073165843891659 7188721860109748765837489)
                ·
                  refine ⟨5391541395082311574378117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7188721860109748765837489 5391541395082311574378117)
                  ·
                    refine ⟨1010914011577933420195897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391541395082311574378117 1010914011577933420195897)
                    ·
                      rfl

theorem cell22_2953122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2953122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953122 prefixEnd_2953122 := by exact prefixLift 2953122
  have htrace : WordTrace (prefixWord ++ tailWord_2953122) baseStart_2953122 baseEnd_2953122 := by
    simpa [prefixWord, tailWord_2953122, baseEnd_2953122] using wordTrace_append hprefix tailTrace_2953122
  have hstable : (prefixWord ++ tailWord_2953122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953122).length < 2 ^ (prefixWord ++ tailWord_2953122).sum := by decide
  have hdescent : baseEnd_2953122 < baseStart_2953122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953135 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 1, 3]
def baseStart_2953135 : Nat := 118140960795 + 2953135 * 2 ^ 59
def prefixEnd_2953135 : Nat := 4983230072969 + 3 ^ 40 * 2953135 * 2
def baseEnd_2953135 : Nat := 1010918461743605719620857

theorem tailTrace_2953135 : CollatzResearch.WordTrace tailWord_2953135 prefixEnd_2953135 1010918461743605719620857 := by
  unfold tailWord_2953135
  simp only [CollatzResearch.WordTrace]
  refine ⟨107709682156303725149332859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71806454770869150099555239 107709682156303725149332859)
  ·
    refine ⟨161564523234455587723999289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107709682156303725149332859 161564523234455587723999289)
    ·
      refine ⟨121173392425841690792999467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161564523234455587723999289 121173392425841690792999467)
      ·
        refine ⟨181760088638762536189499201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121173392425841690792999467 181760088638762536189499201)
        ·
          refine ⟨136320066479071902142124401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181760088638762536189499201 136320066479071902142124401)
          ·
            refine ⟨102240049859303926606593301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136320066479071902142124401 102240049859303926606593301)
            ·
              refine ⟨4792502337154871559684061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102240049859303926606593301 4792502337154871559684061)
              ·
                refine ⟨1797188376433076834881523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792502337154871559684061 1797188376433076834881523)
                ·
                  refine ⟨2695782564649615252322285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797188376433076834881523 2695782564649615252322285)
                  ·
                    refine ⟨1010918461743605719620857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695782564649615252322285 1010918461743605719620857)
                    ·
                      rfl

theorem cell22_2953135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_2953135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953135 prefixEnd_2953135 := by exact prefixLift 2953135
  have htrace : WordTrace (prefixWord ++ tailWord_2953135) baseStart_2953135 baseEnd_2953135 := by
    simpa [prefixWord, tailWord_2953135, baseEnd_2953135] using wordTrace_append hprefix tailTrace_2953135
  have hstable : (prefixWord ++ tailWord_2953135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953135).length < 2 ^ (prefixWord ++ tailWord_2953135).sum := by decide
  have hdescent : baseEnd_2953135 < baseStart_2953135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953176 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_2953176 : Nat := 118140960795 + 2953176 * 2 ^ 59
def prefixEnd_2953176 : Nat := 4983230072969 + 3 ^ 40 * 2953176 * 2
def baseEnd_2953176 : Nat := 336977498960498426448577

theorem tailTrace_2953176 : CollatzResearch.WordTrace tailWord_2953176 prefixEnd_2953176 336977498960498426448577 := by
  unfold tailWord_2953176
  simp only [CollatzResearch.WordTrace]
  refine ⟨53855588774577594575787691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71807451699436792767716921 53855588774577594575787691)
  ·
    refine ⟨80783383161866391863681537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53855588774577594575787691 80783383161866391863681537)
    ·
      refine ⟨60587537371399793897761153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80783383161866391863681537 60587537371399793897761153)
      ·
        refine ⟨45440653028549845423320865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60587537371399793897761153 45440653028549845423320865)
        ·
          refine ⟨34080489771412384067490649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45440653028549845423320865 34080489771412384067490649)
          ·
            refine ⟨25560367328559288050617987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34080489771412384067490649 25560367328559288050617987)
            ·
              refine ⟨38340550992838932075926981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25560367328559288050617987 38340550992838932075926981)
              ·
                refine ⟨7188853311157299764236309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38340550992838932075926981 7188853311157299764236309)
                ·
                  refine ⟨336977498960498426448577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7188853311157299764236309 336977498960498426448577)
                  ·
                    rfl

theorem cell22_2953176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_2953176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953176 prefixEnd_2953176 := by exact prefixLift 2953176
  have htrace : WordTrace (prefixWord ++ tailWord_2953176) baseStart_2953176 baseEnd_2953176 := by
    simpa [prefixWord, tailWord_2953176, baseEnd_2953176] using wordTrace_append hprefix tailTrace_2953176
  have hstable : (prefixWord ++ tailWord_2953176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953176).length < 2 ^ (prefixWord ++ tailWord_2953176).sum := by decide
  have hdescent : baseEnd_2953176 < baseStart_2953176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953186 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2953186 : Nat := 118140960795 + 2953186 * 2 ^ 59
def prefixEnd_2953186 : Nat := 4983230072969 + 3 ^ 40 * 2953186 * 2
def baseEnd_2953186 : Nat := 1010935920085858586595701

theorem tailTrace_2953186 : CollatzResearch.WordTrace tailWord_2953186 prefixEnd_2953186 1010935920085858586595701 := by
  unfold tailWord_2953186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927885569779740214859853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71807694852745973906292941 26927885569779740214859853)
  ·
    refine ⟨10097957088667402580572445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26927885569779740214859853 10097957088667402580572445)
    ·
      refine ⟨3786733908250275967714667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10097957088667402580572445 3786733908250275967714667)
      ·
        refine ⟨5680100862375413951572001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786733908250275967714667 5680100862375413951572001)
        ·
          refine ⟨4260075646781560463679001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680100862375413951572001 4260075646781560463679001)
          ·
            refine ⟨3195056735086170347759251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260075646781560463679001 3195056735086170347759251)
            ·
              refine ⟨4792585102629255521638877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195056735086170347759251 4792585102629255521638877)
              ·
                refine ⟨1797219413485970820614579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792585102629255521638877 1797219413485970820614579)
                ·
                  refine ⟨2695829120228956230921869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797219413485970820614579 2695829120228956230921869)
                  ·
                    refine ⟨1010935920085858586595701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695829120228956230921869 1010935920085858586595701)
                    ·
                      rfl

theorem cell22_2953186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2953186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953186 prefixEnd_2953186 := by exact prefixLift 2953186
  have htrace : WordTrace (prefixWord ++ tailWord_2953186) baseStart_2953186 baseEnd_2953186 := by
    simpa [prefixWord, tailWord_2953186, baseEnd_2953186] using wordTrace_append hprefix tailTrace_2953186
  have hstable : (prefixWord ++ tailWord_2953186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953186).length < 2 ^ (prefixWord ++ tailWord_2953186).sum := by decide
  have hdescent : baseEnd_2953186 < baseStart_2953186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2953208 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_2953208 : Nat := 118140960795 + 2953208 * 2 ^ 59
def prefixEnd_2953208 : Nat := 4983230072969 + 3 ^ 40 * 2953208 * 2
def baseEnd_2953208 : Nat := 1010943451135457862545633

theorem tailTrace_2953208 : CollatzResearch.WordTrace tailWord_2953208 prefixEnd_2953208 1010943451135457862545633 := by
  unfold tailWord_2953208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53856172342519629308370139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71808229790026172411160185 53856172342519629308370139)
  ·
    refine ⟨80784258513779443962555209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53856172342519629308370139 80784258513779443962555209)
    ·
      refine ⟨60588193885334582971916407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80784258513779443962555209 60588193885334582971916407)
      ·
        refine ⟨90882290828001874457874611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60588193885334582971916407 90882290828001874457874611)
        ·
          refine ⟨136323436242002811686811917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90882290828001874457874611 136323436242002811686811917)
          ·
            refine ⟨51121288590751054382554469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136323436242002811686811917 51121288590751054382554469)
            ·
              refine ⟨9585241610765822696728963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51121288590751054382554469 9585241610765822696728963)
              ·
                refine ⟨14377862416148734045093445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585241610765822696728963 14377862416148734045093445)
                ·
                  refine ⟨2695849203027887633455021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14377862416148734045093445 2695849203027887633455021)
                  ·
                    refine ⟨1010943451135457862545633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695849203027887633455021 1010943451135457862545633)
                    ·
                      rfl

theorem cell22_2953208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_2953208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2953208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2953208 prefixEnd_2953208 := by exact prefixLift 2953208
  have htrace : WordTrace (prefixWord ++ tailWord_2953208) baseStart_2953208 baseEnd_2953208 := by
    simpa [prefixWord, tailWord_2953208, baseEnd_2953208] using wordTrace_append hprefix tailTrace_2953208
  have hstable : (prefixWord ++ tailWord_2953208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2953208).length < 2 ^ (prefixWord ++ tailWord_2953208).sum := by decide
  have hdescent : baseEnd_2953208 < baseStart_2953208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2953208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
