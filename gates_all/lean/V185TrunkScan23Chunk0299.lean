import V185TrunkScan23Chunk0298

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1768319 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 5, 2, 2]
def baseStart_1768319 : Nat := 118140960795 + 1768319 * 2 ^ 59
def prefixEnd_1768319 : Nat := 4983230072969 + 3 ^ 40 * 1768319 * 2
def baseEnd_1768319 : Nat := 907997597477972177480155

theorem tailTrace_1768319 : CollatzResearch.WordTrace tailWord_1768319 prefixEnd_1768319 907997597477972177480155 := by
  unfold tailWord_1768319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64495892480689742686476011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42997261653793161790984007 64495892480689742686476011)
  ·
    refine ⟨96743838721034614029714017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64495892480689742686476011 96743838721034614029714017)
    ·
      refine ⟨72557879040775960522285513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96743838721034614029714017 72557879040775960522285513)
      ·
        refine ⟨54418409280581970391714135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72557879040775960522285513 54418409280581970391714135)
        ·
          refine ⟨81627613920872955587571203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54418409280581970391714135 81627613920872955587571203)
          ·
            refine ⟨122441420881309433381356805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81627613920872955587571203 122441420881309433381356805)
            ·
              refine ⟨22957766415245518759004401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122441420881309433381356805 22957766415245518759004401)
              ·
                refine ⟨17218324811434139069253301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22957766415245518759004401 17218324811434139069253301)
                ·
                  refine ⟨1614217951071950537742497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17218324811434139069253301 1614217951071950537742497)
                  ·
                    refine ⟨1210663463303962903306873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614217951071950537742497 1210663463303962903306873)
                    ·
                      refine ⟨907997597477972177480155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210663463303962903306873 907997597477972177480155)
                      ·
                        rfl

theorem cell23_1768319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_1768319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768319 prefixEnd_1768319 := by exact prefixLift 1768319
  have htrace : WordTrace (prefixWord ++ tailWord_1768319) baseStart_1768319 baseEnd_1768319 := by
    simpa [prefixWord, tailWord_1768319, baseEnd_1768319] using wordTrace_append hprefix tailTrace_1768319
  have hstable : (prefixWord ++ tailWord_1768319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768319).length < 2 ^ (prefixWord ++ tailWord_1768319).sum := by decide
  have hdescent : baseEnd_1768319 < baseStart_1768319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768325 : List Nat := [1, 3, 1, 1, 3, 3, 11]
def baseStart_1768325 : Nat := 118140960795 + 1768325 * 2 ^ 59
def prefixEnd_1768325 : Nat := 4983230072969 + 3 ^ 40 * 1768325 * 2
def baseEnd_1768325 : Nat := 11209884918048137703767

theorem tailTrace_1768325 : CollatzResearch.WordTrace tailWord_1768325 prefixEnd_1768325 11209884918048137703767 := by
  unfold tailWord_1768325
  simp only [CollatzResearch.WordTrace]
  refine ⟨64496111318668005711194429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42997407545778670474129619 64496111318668005711194429)
  ·
    refine ⟨24186041744500502141697911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64496111318668005711194429 24186041744500502141697911)
    ·
      refine ⟨36279062616750753212546867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24186041744500502141697911 36279062616750753212546867)
      ·
        refine ⟨54418593925126129818820301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36279062616750753212546867 54418593925126129818820301)
        ·
          refine ⟨20406972721922298682057613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54418593925126129818820301 20406972721922298682057613)
          ·
            refine ⟨7652614770720862005771605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20406972721922298682057613 7652614770720862005771605)
            ·
              refine ⟨11209884918048137703767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7652614770720862005771605 11209884918048137703767)
              ·
                rfl

theorem cell23_1768325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 11].length) (baseStart_1768325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768325 prefixEnd_1768325 := by exact prefixLift 1768325
  have htrace : WordTrace (prefixWord ++ tailWord_1768325) baseStart_1768325 baseEnd_1768325 := by
    simpa [prefixWord, tailWord_1768325, baseEnd_1768325] using wordTrace_append hprefix tailTrace_1768325
  have hstable : (prefixWord ++ tailWord_1768325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768325).length < 2 ^ (prefixWord ++ tailWord_1768325).sum := by decide
  have hdescent : baseEnd_1768325 < baseStart_1768325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768330 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1768330 : Nat := 118140960795 + 1768330 * 2 ^ 59
def prefixEnd_1768330 : Nat := 4983230072969 + 3 ^ 40 * 1768330 * 2
def baseEnd_1768330 : Nat := 908003245765171634442605

theorem tailTrace_1768330 : CollatzResearch.WordTrace tailWord_1768330 prefixEnd_1768330 908003245765171634442605 := by
  unfold tailWord_1768330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124073420912472891281611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42997529122433261043417629 16124073420912472891281611)
  ·
    refine ⟨24186110131368709336922417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124073420912472891281611 24186110131368709336922417)
    ·
      refine ⟨18139582598526532002691813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24186110131368709336922417 18139582598526532002691813)
      ·
        refine ⟨3401171737223724750504715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18139582598526532002691813 3401171737223724750504715)
        ·
          refine ⟨5101757605835587125757073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401171737223724750504715 5101757605835587125757073)
          ·
            refine ⟨3826318204376690344317805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101757605835587125757073 3826318204376690344317805)
            ·
              refine ⟨1434869326641258879119177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826318204376690344317805 1434869326641258879119177)
              ·
                refine ⟨1076151994980944159339383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434869326641258879119177 1076151994980944159339383)
                ·
                  refine ⟨1614227992471416239009075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076151994980944159339383 1614227992471416239009075)
                  ·
                    refine ⟨2421341988707124358513613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614227992471416239009075 2421341988707124358513613)
                    ·
                      refine ⟨908003245765171634442605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421341988707124358513613 908003245765171634442605)
                      ·
                        rfl

theorem cell23_1768330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1768330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768330 prefixEnd_1768330 := by exact prefixLift 1768330
  have htrace : WordTrace (prefixWord ++ tailWord_1768330) baseStart_1768330 baseEnd_1768330 := by
    simpa [prefixWord, tailWord_1768330, baseEnd_1768330] using wordTrace_append hprefix tailTrace_1768330
  have hstable : (prefixWord ++ tailWord_1768330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768330).length < 2 ^ (prefixWord ++ tailWord_1768330).sum := by decide
  have hdescent : baseEnd_1768330 < baseStart_1768330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768345 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1768345 : Nat := 118140960795 + 1768345 * 2 ^ 59
def prefixEnd_1768345 : Nat := 4983230072969 + 3 ^ 40 * 1768345 * 2
def baseEnd_1768345 : Nat := 908010947974989075755035

theorem tailTrace_1768345 : CollatzResearch.WordTrace tailWord_1768345 prefixEnd_1768345 908010947974989075755035 := by
  unfold tailWord_1768345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64496840778595549126922489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42997893852397032751281659 64496840778595549126922489)
  ·
    refine ⟨48372630583946661845191867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64496840778595549126922489 48372630583946661845191867)
    ·
      refine ⟨72558945875919992767787801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48372630583946661845191867 72558945875919992767787801)
      ·
        refine ⟨54419209406939994575840851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72558945875919992767787801 54419209406939994575840851)
        ·
          refine ⟨81628814110409991863761277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54419209406939994575840851 81628814110409991863761277)
          ·
            refine ⟨30610805291403746948910479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81628814110409991863761277 30610805291403746948910479)
            ·
              refine ⟨45916207937105620423365719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30610805291403746948910479 45916207937105620423365719)
              ·
                refine ⟨68874311905658430635048579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45916207937105620423365719 68874311905658430635048579)
                ·
                  refine ⟨103311467858487645952572869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68874311905658430635048579 103311467858487645952572869)
                  ·
                    refine ⟨19370900223466433616107413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103311467858487645952572869 19370900223466433616107413)
                    ·
                      refine ⟨908010947974989075755035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19370900223466433616107413 908010947974989075755035)
                      ·
                        rfl

theorem cell23_1768345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1768345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768345 prefixEnd_1768345 := by exact prefixLift 1768345
  have htrace : WordTrace (prefixWord ++ tailWord_1768345) baseStart_1768345 baseEnd_1768345 := by
    simpa [prefixWord, tailWord_1768345, baseEnd_1768345] using wordTrace_append hprefix tailTrace_1768345
  have hstable : (prefixWord ++ tailWord_1768345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768345).length < 2 ^ (prefixWord ++ tailWord_1768345).sum := by decide
  have hdescent : baseEnd_1768345 < baseStart_1768345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768346 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_1768346 : Nat := 118140960795 + 1768346 * 2 ^ 59
def prefixEnd_1768346 : Nat := 4983230072969 + 3 ^ 40 * 1768346 * 2
def baseEnd_1768346 : Nat := 302670487151881190614177

theorem tailTrace_1768346 : CollatzResearch.WordTrace tailWord_1768346 prefixEnd_1768346 302670487151881190614177 := by
  unfold tailWord_1768346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124219312897981574427223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42997918167727950865139261 16124219312897981574427223)
  ·
    refine ⟨24186328969346972361640835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124219312897981574427223 24186328969346972361640835)
    ·
      refine ⟨36279493454020458542461253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24186328969346972361640835 36279493454020458542461253)
      ·
        refine ⟨6802405022628835976711485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36279493454020458542461253 6802405022628835976711485)
        ·
          refine ⟨2550901883485813491266807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6802405022628835976711485 2550901883485813491266807)
          ·
            refine ⟨3826352825228720236900211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550901883485813491266807 3826352825228720236900211)
            ·
              refine ⟨5739529237843080355350317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826352825228720236900211 5739529237843080355350317)
              ·
                refine ⟨2152323464191155133256369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5739529237843080355350317 2152323464191155133256369)
                ·
                  refine ⟨1614242598143366349942277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152323464191155133256369 1614242598143366349942277)
                  ·
                    refine ⟨302670487151881190614177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1614242598143366349942277 302670487151881190614177)
                    ·
                      rfl

theorem cell23_1768346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_1768346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768346 prefixEnd_1768346 := by exact prefixLift 1768346
  have htrace : WordTrace (prefixWord ++ tailWord_1768346) baseStart_1768346 baseEnd_1768346 := by
    simpa [prefixWord, tailWord_1768346, baseEnd_1768346] using wordTrace_append hprefix tailTrace_1768346
  have hstable : (prefixWord ++ tailWord_1768346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768346).length < 2 ^ (prefixWord ++ tailWord_1768346).sum := by decide
  have hdescent : baseEnd_1768346 < baseStart_1768346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768426 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_1768426 : Nat := 118140960795 + 1768426 * 2 ^ 59
def prefixEnd_1768426 : Nat := 4983230072969 + 3 ^ 40 * 1768426 * 2
def baseEnd_1768426 : Nat := 908052539908003258842163

theorem tailTrace_1768426 : CollatzResearch.WordTrace tailWord_1768426 prefixEnd_1768426 908052539908003258842163 := by
  unfold tailWord_1768426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124948772825524990155283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42999863394201399973747421 16124948772825524990155283)
  ·
    refine ⟨24187423159238287485232925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124948772825524990155283 24187423159238287485232925)
    ·
      refine ⟨9070283684714357806962347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24187423159238287485232925 9070283684714357806962347)
      ·
        refine ⟨13605425527071536710443521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070283684714357806962347 13605425527071536710443521)
        ·
          refine ⟨10204069145303652532832641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13605425527071536710443521 10204069145303652532832641)
          ·
            refine ⟨7653051858977739399624481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204069145303652532832641 7653051858977739399624481)
            ·
              refine ⟨5739788894233304549718361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653051858977739399624481 5739788894233304549718361)
              ·
                refine ⟨4304841670674978412288771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5739788894233304549718361 4304841670674978412288771)
                ·
                  refine ⟨6457262506012467618433157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304841670674978412288771 6457262506012467618433157)
                  ·
                    refine ⟨1210736719877337678456217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457262506012467618433157 1210736719877337678456217)
                    ·
                      refine ⟨908052539908003258842163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210736719877337678456217 908052539908003258842163)
                      ·
                        rfl

theorem cell23_1768426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_1768426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768426 prefixEnd_1768426 := by exact prefixLift 1768426
  have htrace : WordTrace (prefixWord ++ tailWord_1768426) baseStart_1768426 baseEnd_1768426 := by
    simpa [prefixWord, tailWord_1768426, baseEnd_1768426] using wordTrace_append hprefix tailTrace_1768426
  have hstable : (prefixWord ++ tailWord_1768426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768426).length < 2 ^ (prefixWord ++ tailWord_1768426).sum := by decide
  have hdescent : baseEnd_1768426 < baseStart_1768426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768437 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1768437 : Nat := 118140960795 + 1768437 * 2 ^ 59
def prefixEnd_1768437 : Nat := 4983230072969 + 3 ^ 40 * 1768437 * 2
def baseEnd_1768437 : Nat := 908058188195202715804613

theorem tailTrace_1768437 : CollatzResearch.WordTrace tailWord_1768437 prefixEnd_1768437 908058188195202715804613 := by
  unfold tailWord_1768437
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500196294262248839271565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43000130862841499226181043 64500196294262248839271565)
  ·
    refine ⟨24187573610348343314726837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64500196294262248839271565 24187573610348343314726837)
    ·
      refine ⟨2267585025970157185755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24187573610348343314726837 2267585025970157185755641)
      ·
        refine ⟨1700688769477617889316731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267585025970157185755641 1700688769477617889316731)
        ·
          refine ⟨2551033154216426833975097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700688769477617889316731 2551033154216426833975097)
          ·
            refine ⟨1913274865662320125481323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551033154216426833975097 1913274865662320125481323)
            ·
              refine ⟨2869912298493480188221985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913274865662320125481323 2869912298493480188221985)
              ·
                refine ⟨2152434223870110141166489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869912298493480188221985 2152434223870110141166489)
                ·
                  refine ⟨1614325667902582605874867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152434223870110141166489 1614325667902582605874867)
                  ·
                    refine ⟨2421488501853873908812301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614325667902582605874867 2421488501853873908812301)
                    ·
                      refine ⟨908058188195202715804613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421488501853873908812301 908058188195202715804613)
                      ·
                        rfl

theorem cell23_1768437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1768437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768437 prefixEnd_1768437 := by exact prefixLift 1768437
  have htrace : WordTrace (prefixWord ++ tailWord_1768437) baseStart_1768437 baseEnd_1768437 := by
    simpa [prefixWord, tailWord_1768437, baseEnd_1768437] using wordTrace_append hprefix tailTrace_1768437
  have hstable : (prefixWord ++ tailWord_1768437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768437).length < 2 ^ (prefixWord ++ tailWord_1768437).sum := by decide
  have hdescent : baseEnd_1768437 < baseStart_1768437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768449 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 7]
def baseStart_1768449 : Nat := 118140960795 + 1768449 * 2 ^ 59
def prefixEnd_1768449 : Nat := 4983230072969 + 3 ^ 40 * 1768449 * 2
def baseEnd_1768449 : Nat := 100896038884784074317173

theorem tailTrace_1768449 : CollatzResearch.WordTrace tailWord_1768449 prefixEnd_1768449 100896038884784074317173 := by
  unfold tailWord_1768449
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500633970218774888708401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43000422646812516592472267 64500633970218774888708401)
  ·
    refine ⟨48375475477664081166531301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64500633970218774888708401 48375475477664081166531301)
    ·
      refine ⟨9070401652062015218724619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48375475477664081166531301 9070401652062015218724619)
      ·
        refine ⟨13605602478093022828086929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070401652062015218724619 13605602478093022828086929)
        ·
          refine ⟨10204201858569767121065197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13605602478093022828086929 10204201858569767121065197)
          ·
            refine ⟨3826575696963662670399449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10204201858569767121065197 3826575696963662670399449)
            ·
              refine ⟨2869931772722747002799587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826575696963662670399449 2869931772722747002799587)
              ·
                refine ⟨4304897659084120504199381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869931772722747002799587 4304897659084120504199381)
                ·
                  refine ⟨100896038884784074317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4304897659084120504199381 100896038884784074317173)
                  ·
                    rfl

theorem cell23_1768449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_1768449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768449 prefixEnd_1768449 := by exact prefixLift 1768449
  have htrace : WordTrace (prefixWord ++ tailWord_1768449) baseStart_1768449 baseEnd_1768449 := by
    simpa [prefixWord, tailWord_1768449, baseEnd_1768449] using wordTrace_append hprefix tailTrace_1768449
  have hstable : (prefixWord ++ tailWord_1768449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768449).length < 2 ^ (prefixWord ++ tailWord_1768449).sum := by decide
  have hdescent : baseEnd_1768449 < baseStart_1768449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768459 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3]
def baseStart_1768459 : Nat := 118140960795 + 1768459 * 2 ^ 59
def prefixEnd_1768459 : Nat := 4983230072969 + 3 ^ 40 * 1768459 * 2
def baseEnd_1768459 : Nat := 908069484769601629729511

theorem tailTrace_1768459 : CollatzResearch.WordTrace tailWord_1768459 prefixEnd_1768459 908069484769601629729511 := by
  unfold tailWord_1768459
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500998700182546596572431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43000665800121697731048287 64500998700182546596572431)
  ·
    refine ⟨96751498050273819894858647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64500998700182546596572431 96751498050273819894858647)
    ·
      refine ⟨145127247075410729842287971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96751498050273819894858647 145127247075410729842287971)
      ·
        refine ⟨217690870613116094763431957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145127247075410729842287971 217690870613116094763431957)
        ·
          refine ⟨10204259559989816942035873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 217690870613116094763431957 10204259559989816942035873)
          ·
            refine ⟨7653194669992362706526905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204259559989816942035873 7653194669992362706526905)
            ·
              refine ⟨5739896002494272029895179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653194669992362706526905 5739896002494272029895179)
              ·
                refine ⟨8609844003741408044842769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739896002494272029895179 8609844003741408044842769)
                ·
                  refine ⟨6457383002806056033632077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8609844003741408044842769 6457383002806056033632077)
                  ·
                    refine ⟨2421518626052271012612029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6457383002806056033632077 2421518626052271012612029)
                    ·
                      refine ⟨908069484769601629729511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421518626052271012612029 908069484769601629729511)
                      ·
                        rfl

theorem cell23_1768459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].length) (baseStart_1768459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768459 prefixEnd_1768459 := by exact prefixLift 1768459
  have htrace : WordTrace (prefixWord ++ tailWord_1768459) baseStart_1768459 baseEnd_1768459 := by
    simpa [prefixWord, tailWord_1768459, baseEnd_1768459] using wordTrace_append hprefix tailTrace_1768459
  have hstable : (prefixWord ++ tailWord_1768459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768459).length < 2 ^ (prefixWord ++ tailWord_1768459).sum := by decide
  have hdescent : baseEnd_1768459 < baseStart_1768459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768460 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_1768460 : Nat := 118140960795 + 1768460 * 2 ^ 59
def prefixEnd_1768460 : Nat := 4983230072969 + 3 ^ 40 * 1768460 * 2
def baseEnd_1768460 : Nat := 908069998250256125817007

theorem tailTrace_1768460 : CollatzResearch.WordTrace tailWord_1768460 prefixEnd_1768460 908069998250256125817007 := by
  unfold tailWord_1768460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250517586589461883679417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43000690115452615844905889 32250517586589461883679417)
  ·
    refine ⟨24187888189942096412759563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32250517586589461883679417 24187888189942096412759563)
    ·
      refine ⟨36281832284913144619139345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24187888189942096412759563 36281832284913144619139345)
      ·
        refine ⟨27211374213684858464354509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36281832284913144619139345 27211374213684858464354509)
        ·
          refine ⟨10204265330131821924132941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27211374213684858464354509 10204265330131821924132941)
          ·
            refine ⟨3826599498799433221549853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10204265330131821924132941 3826599498799433221549853)
            ·
              refine ⟨1434974812049787458081195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826599498799433221549853 1434974812049787458081195)
              ·
                refine ⟨2152462218074681187121793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434974812049787458081195 2152462218074681187121793)
                ·
                  refine ⟨1614346663556010890341345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2152462218074681187121793 1614346663556010890341345)
                  ·
                    refine ⟨1210759997667008167756009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614346663556010890341345 1210759997667008167756009)
                    ·
                      refine ⟨908069998250256125817007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210759997667008167756009 908069998250256125817007)
                      ·
                        rfl

theorem cell23_1768460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_1768460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768460 prefixEnd_1768460 := by exact prefixLift 1768460
  have htrace : WordTrace (prefixWord ++ tailWord_1768460) baseStart_1768460 baseEnd_1768460 := by
    simpa [prefixWord, tailWord_1768460, baseEnd_1768460] using wordTrace_append hprefix tailTrace_1768460
  have hstable : (prefixWord ++ tailWord_1768460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768460).length < 2 ^ (prefixWord ++ tailWord_1768460).sum := by decide
  have hdescent : baseEnd_1768460 < baseStart_1768460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768500 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1768500 : Nat := 118140960795 + 1768500 * 2 ^ 59
def prefixEnd_1768500 : Nat := 4983230072969 + 3 ^ 40 * 1768500 * 2
def baseEnd_1768500 : Nat := 100898948608492885479647

theorem tailTrace_1768500 : CollatzResearch.WordTrace tailWord_1768500 prefixEnd_1768500 100898948608492885479647 := by
  unfold tailWord_1768500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251247046517005299407477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43001662728689340399209969 32251247046517005299407477)
  ·
    refine ⟨3023554410610969246819451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32251247046517005299407477 3023554410610969246819451)
    ·
      refine ⟨4535331615916453870229177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023554410610969246819451 4535331615916453870229177)
      ·
        refine ⟨3401498711937340402671883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535331615916453870229177 3401498711937340402671883)
        ·
          refine ⟨5102248067906010604007825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401498711937340402671883 5102248067906010604007825)
          ·
            refine ⟨3826686050929507953005869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102248067906010604007825 3826686050929507953005869)
            ·
              refine ⟨1435007269098565482377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826686050929507953005869 1435007269098565482377201)
              ·
                refine ⟨1076255451823924111782901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435007269098565482377201 1076255451823924111782901)
                ·
                  refine ⟨100898948608492885479647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076255451823924111782901 100898948608492885479647)
                  ·
                    rfl

theorem cell23_1768500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1768500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768500 prefixEnd_1768500 := by exact prefixLift 1768500
  have htrace : WordTrace (prefixWord ++ tailWord_1768500) baseStart_1768500 baseEnd_1768500 := by
    simpa [prefixWord, tailWord_1768500, baseEnd_1768500] using wordTrace_append hprefix tailTrace_1768500
  have hstable : (prefixWord ++ tailWord_1768500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768500).length < 2 ^ (prefixWord ++ tailWord_1768500).sum := by decide
  have hdescent : baseEnd_1768500 < baseStart_1768500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768536 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1768536 : Nat := 118140960795 + 1768536 * 2 ^ 59
def prefixEnd_1768536 : Nat := 4983230072969 + 3 ^ 40 * 1768536 * 2
def baseEnd_1768536 : Nat := 908109022779997828466657

theorem tailTrace_1768536 : CollatzResearch.WordTrace tailWord_1768536 prefixEnd_1768536 908109022779997828466657 := by
  unfold tailWord_1768536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32251903560451794373562731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43002538080602392498083641 32251903560451794373562731)
  ·
    refine ⟨48377855340677691560344097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32251903560451794373562731 48377855340677691560344097)
    ·
      refine ⟨36283391505508268670258073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48377855340677691560344097 36283391505508268670258073)
      ·
        refine ⟨27212543629131201502693555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36283391505508268670258073 27212543629131201502693555)
        ·
          refine ⟨40818815443696802254040333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27212543629131201502693555 40818815443696802254040333)
          ·
            refine ⟨15307055791386300845265125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40818815443696802254040333 15307055791386300845265125)
            ·
              refine ⟨2870072960884931408487211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15307055791386300845265125 2870072960884931408487211)
              ·
                refine ⟨4305109441327397112730817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870072960884931408487211 4305109441327397112730817)
                ·
                  refine ⟨3228832080995547834548113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305109441327397112730817 3228832080995547834548113)
                  ·
                    refine ⟨2421624060746660875911085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3228832080995547834548113 2421624060746660875911085)
                    ·
                      refine ⟨908109022779997828466657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421624060746660875911085 908109022779997828466657)
                      ·
                        rfl

theorem cell23_1768536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1768536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768536 prefixEnd_1768536 := by exact prefixLift 1768536
  have htrace : WordTrace (prefixWord ++ tailWord_1768536) baseStart_1768536 baseEnd_1768536 := by
    simpa [prefixWord, tailWord_1768536, baseEnd_1768536] using wordTrace_append hprefix tailTrace_1768536
  have hstable : (prefixWord ++ tailWord_1768536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768536).length < 2 ^ (prefixWord ++ tailWord_1768536).sum := by decide
  have hdescent : baseEnd_1768536 < baseStart_1768536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768576 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2]
def baseStart_1768576 : Nat := 118140960795 + 1768576 * 2 ^ 59
def prefixEnd_1768576 : Nat := 4983230072969 + 3 ^ 40 * 1768576 * 2
def baseEnd_1768576 : Nat := 908129562006177671966473

theorem tailTrace_1768576 : CollatzResearch.WordTrace tailWord_1768576 prefixEnd_1768576 908129562006177671966473 := by
  unfold tailWord_1768576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252633020379337789290791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43003510693839117052387721 32252633020379337789290791)
  ·
    refine ⟨48378949530569006683936187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32252633020379337789290791 48378949530569006683936187)
    ·
      refine ⟨72568424295853510025904281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48378949530569006683936187 72568424295853510025904281)
      ·
        refine ⟨54426318221890132519428211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72568424295853510025904281 54426318221890132519428211)
        ·
          refine ⟨81639477332835198779142317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54426318221890132519428211 81639477332835198779142317)
          ·
            refine ⟨30614803999813199542178369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81639477332835198779142317 30614803999813199542178369)
            ·
              refine ⟨22961102999859899656633777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30614803999813199542178369 22961102999859899656633777)
              ·
                refine ⟨17220827249894924742475333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22961102999859899656633777 17220827249894924742475333)
                ·
                  refine ⟨3228905109355298389214125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17220827249894924742475333 3228905109355298389214125)
                  ·
                    refine ⟨1210839416008236895955297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228905109355298389214125 1210839416008236895955297)
                    ·
                      refine ⟨908129562006177671966473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210839416008236895955297 908129562006177671966473)
                      ·
                        rfl

theorem cell23_1768576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_1768576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768576 prefixEnd_1768576 := by exact prefixLift 1768576
  have htrace : WordTrace (prefixWord ++ tailWord_1768576) baseStart_1768576 baseEnd_1768576 := by
    simpa [prefixWord, tailWord_1768576, baseEnd_1768576] using wordTrace_append hprefix tailTrace_1768576
  have hstable : (prefixWord ++ tailWord_1768576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768576).length < 2 ^ (prefixWord ++ tailWord_1768576).sum := by decide
  have hdescent : baseEnd_1768576 < baseStart_1768576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768586 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1768586 : Nat := 118140960795 + 1768586 * 2 ^ 59
def prefixEnd_1768586 : Nat := 4983230072969 + 3 ^ 40 * 1768586 * 2
def baseEnd_1768586 : Nat := 302711565604240877613809

theorem tailTrace_1768586 : CollatzResearch.WordTrace tailWord_1768586 prefixEnd_1768586 302711565604240877613809 := by
  unfold tailWord_1768586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126407692680611821611403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43003753847148298190963741 16126407692680611821611403)
  ·
    refine ⟨24189611539020917732417105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16126407692680611821611403 24189611539020917732417105)
    ·
      refine ⟨18142208654265688299312829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24189611539020917732417105 18142208654265688299312829)
      ·
        refine ⟨6803328245349633112242311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18142208654265688299312829 6803328245349633112242311)
        ·
          refine ⟨10204992368024449668363467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803328245349633112242311 10204992368024449668363467)
          ·
            refine ⟨15307488552036674502545201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204992368024449668363467 15307488552036674502545201)
            ·
              refine ⟨11480616414027505876908901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15307488552036674502545201 11480616414027505876908901)
              ·
                refine ⟨2152615577630157351920419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11480616414027505876908901 2152615577630157351920419)
                ·
                  refine ⟨3228923366445236027880629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152615577630157351920419 3228923366445236027880629)
                  ·
                    refine ⟨302711565604240877613809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3228923366445236027880629 302711565604240877613809)
                    ·
                      rfl

theorem cell23_1768586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1768586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768586 prefixEnd_1768586 := by exact prefixLift 1768586
  have htrace : WordTrace (prefixWord ++ tailWord_1768586) baseStart_1768586 baseEnd_1768586 := by
    simpa [prefixWord, tailWord_1768586, baseEnd_1768586] using wordTrace_append hprefix tailTrace_1768586
  have hstable : (prefixWord ++ tailWord_1768586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768586).length < 2 ^ (prefixWord ++ tailWord_1768586).sum := by decide
  have hdescent : baseEnd_1768586 < baseStart_1768586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768600 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1768600 : Nat := 118140960795 + 1768600 * 2 ^ 59
def prefixEnd_1768600 : Nat := 4983230072969 + 3 ^ 40 * 1768600 * 2
def baseEnd_1768600 : Nat := 908141885541885578066363

theorem tailTrace_1768600 : CollatzResearch.WordTrace tailWord_1768600 prefixEnd_1768600 908141885541885578066363 := by
  unfold tailWord_1768600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253070696335863838727627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43004094261781151784970169 32253070696335863838727627)
  ·
    refine ⟨48379606044503795758091441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32253070696335863838727627 48379606044503795758091441)
    ·
      refine ⟨36284704533377846818568581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48379606044503795758091441 36284704533377846818568581)
      ·
        refine ⟨6803382100008346278481609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36284704533377846818568581 6803382100008346278481609)
        ·
          refine ⟨5102536575006259708861207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6803382100008346278481609 5102536575006259708861207)
          ·
            refine ⟨7653804862509389563291811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102536575006259708861207 7653804862509389563291811)
            ·
              refine ⟨11480707293764084344937717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653804862509389563291811 11480707293764084344937717)
              ·
                refine ⟨1076316308790382907337911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11480707293764084344937717 1076316308790382907337911)
                ·
                  refine ⟨1614474463185574361006867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076316308790382907337911 1614474463185574361006867)
                  ·
                    refine ⟨2421711694778361541510301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614474463185574361006867 2421711694778361541510301)
                    ·
                      refine ⟨908141885541885578066363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421711694778361541510301 908141885541885578066363)
                      ·
                        rfl

theorem cell23_1768600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1768600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768600 prefixEnd_1768600 := by exact prefixLift 1768600
  have htrace : WordTrace (prefixWord ++ tailWord_1768600) baseStart_1768600 baseEnd_1768600 := by
    simpa [prefixWord, tailWord_1768600, baseEnd_1768600] using wordTrace_append hprefix tailTrace_1768600
  have hstable : (prefixWord ++ tailWord_1768600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768600).length < 2 ^ (prefixWord ++ tailWord_1768600).sum := by decide
  have hdescent : baseEnd_1768600 < baseStart_1768600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768623 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 3, 2, 2]
def baseStart_1768623 : Nat := 118140960795 + 1768623 * 2 ^ 59
def prefixEnd_1768623 : Nat := 4983230072969 + 3 ^ 40 * 1768623 * 2
def baseEnd_1768623 : Nat := 908153695596938988078757

theorem tailTrace_1768623 : CollatzResearch.WordTrace tailWord_1768623 prefixEnd_1768623 908153695596938988078757 := by
  unfold tailWord_1768623
  simp only [CollatzResearch.WordTrace]
  refine ⟨64506980271588402605542523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43004653514392268403695015 64506980271588402605542523)
  ·
    refine ⟨96760470407382603908313785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64506980271588402605542523 96760470407382603908313785)
    ·
      refine ⟨72570352805536952931235339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96760470407382603908313785 72570352805536952931235339)
      ·
        refine ⟨108855529208305429396853009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72570352805536952931235339 108855529208305429396853009)
        ·
          refine ⟨81641646906229072047639757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108855529208305429396853009 81641646906229072047639757)
          ·
            refine ⟨30615617589835902017864909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81641646906229072047639757 30615617589835902017864909)
            ·
              refine ⟨11480856596188463256699341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30615617589835902017864909 11480856596188463256699341)
              ·
                refine ⟨4305321223570673721262253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11480856596188463256699341 4305321223570673721262253)
                ·
                  refine ⟨1614495458839002645473345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4305321223570673721262253 1614495458839002645473345)
                  ·
                    refine ⟨1210871594129251984105009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614495458839002645473345 1210871594129251984105009)
                    ·
                      refine ⟨908153695596938988078757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210871594129251984105009 908153695596938988078757)
                      ·
                        rfl

theorem cell23_1768623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2, 2].length) (baseStart_1768623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768623 prefixEnd_1768623 := by exact prefixLift 1768623
  have htrace : WordTrace (prefixWord ++ tailWord_1768623) baseStart_1768623 baseEnd_1768623 := by
    simpa [prefixWord, tailWord_1768623, baseEnd_1768623] using wordTrace_append hprefix tailTrace_1768623
  have hstable : (prefixWord ++ tailWord_1768623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768623).length < 2 ^ (prefixWord ++ tailWord_1768623).sum := by decide
  have hdescent : baseEnd_1768623 < baseStart_1768623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768626 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1768626 : Nat := 118140960795 + 1768626 * 2 ^ 59
def prefixEnd_1768626 : Nat := 4983230072969 + 3 ^ 40 * 1768626 * 2
def baseEnd_1768626 : Nat := 908155236038902476341243

theorem tailTrace_1768626 : CollatzResearch.WordTrace tailWord_1768626 prefixEnd_1768626 908155236038902476341243 := by
  unfold tailWord_1768626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126772422644383529475433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43004726460385022745267821 16126772422644383529475433)
  ·
    refine ⟨12095079316983287647106575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16126772422644383529475433 12095079316983287647106575)
    ·
      refine ⟨18142618975474931470659863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095079316983287647106575 18142618975474931470659863)
      ·
        refine ⟨27213928463212397205989795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142618975474931470659863 27213928463212397205989795)
        ·
          refine ⟨40820892694818595808984693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27213928463212397205989795 40820892694818595808984693)
          ·
            refine ⟨3826958690139243357092315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40820892694818595808984693 3826958690139243357092315)
            ·
              refine ⟨5740438035208865035638473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826958690139243357092315 5740438035208865035638473)
              ·
                refine ⟨4305328526406648776728855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740438035208865035638473 4305328526406648776728855)
                ·
                  refine ⟨6457992789609973165093283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305328526406648776728855 6457992789609973165093283)
                  ·
                    refine ⟨9686989184414959747639925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457992789609973165093283 9686989184414959747639925)
                    ·
                      refine ⟨908155236038902476341243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9686989184414959747639925 908155236038902476341243)
                      ·
                        rfl

theorem cell23_1768626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1768626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768626 prefixEnd_1768626 := by exact prefixLift 1768626
  have htrace : WordTrace (prefixWord ++ tailWord_1768626) baseStart_1768626 baseEnd_1768626 := by
    simpa [prefixWord, tailWord_1768626, baseEnd_1768626] using wordTrace_append hprefix tailTrace_1768626
  have hstable : (prefixWord ++ tailWord_1768626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768626).length < 2 ^ (prefixWord ++ tailWord_1768626).sum := by decide
  have hdescent : baseEnd_1768626 < baseStart_1768626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768636 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1768636 : Nat := 118140960795 + 1768636 * 2 ^ 59
def prefixEnd_1768636 : Nat := 4983230072969 + 3 ^ 40 * 1768636 * 2
def baseEnd_1768636 : Nat := 908160370845447437216197

theorem tailTrace_1768636 : CollatzResearch.WordTrace tailWord_1768636 prefixEnd_1768636 908160370845447437216197 := by
  unfold tailWord_1768636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32253727210270652912882881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43004969613694203883843841 32253727210270652912882881)
  ·
    refine ⟨24190295407702989684662161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32253727210270652912882881 24190295407702989684662161)
    ·
      refine ⟨18142721555777242263496621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24190295407702989684662161 18142721555777242263496621)
      ·
        refine ⟨6803520583416465848811233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18142721555777242263496621 6803520583416465848811233)
        ·
          refine ⟨5102640437562349386608425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6803520583416465848811233 5102640437562349386608425)
          ·
            refine ⟨3826980328171762039956319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5102640437562349386608425 3826980328171762039956319)
            ·
              refine ⟨5740470492257643059934479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826980328171762039956319 5740470492257643059934479)
              ·
                refine ⟨8610705738386464589901719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740470492257643059934479 8610705738386464589901719)
                ·
                  refine ⟨12916058607579696884852579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8610705738386464589901719 12916058607579696884852579)
                  ·
                    refine ⟨19374087911369545327278869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12916058607579696884852579 19374087911369545327278869)
                    ·
                      refine ⟨908160370845447437216197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19374087911369545327278869 908160370845447437216197)
                      ·
                        rfl

theorem cell23_1768636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1768636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768636 prefixEnd_1768636 := by exact prefixLift 1768636
  have htrace : WordTrace (prefixWord ++ tailWord_1768636) baseStart_1768636 baseEnd_1768636 := by
    simpa [prefixWord, tailWord_1768636, baseEnd_1768636] using wordTrace_append hprefix tailTrace_1768636
  have hstable : (prefixWord ++ tailWord_1768636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768636).length < 2 ^ (prefixWord ++ tailWord_1768636).sum := by decide
  have hdescent : baseEnd_1768636 < baseStart_1768636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768660 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1768660 : Nat := 118140960795 + 1768660 * 2 ^ 59
def prefixEnd_1768660 : Nat := 4983230072969 + 3 ^ 40 * 1768660 * 2
def baseEnd_1768660 : Nat := 908172694381155343316087

theorem tailTrace_1768660 : CollatzResearch.WordTrace tailWord_1768660 prefixEnd_1768660 908172694381155343316087 := by
  unfold tailWord_1768660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32254164886227178962319717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43005553181636238616426289 32254164886227178962319717)
  ·
    refine ⟨6047655916167596055434947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32254164886227178962319717 6047655916167596055434947)
    ·
      refine ⟨9071483874251394083152421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047655916167596055434947 9071483874251394083152421)
      ·
        refine ⟨1700903226422136390591079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9071483874251394083152421 1700903226422136390591079)
        ·
          refine ⟨2551354839633204585886619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700903226422136390591079 2551354839633204585886619)
          ·
            refine ⟨3827032259449806878829929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551354839633204585886619 3827032259449806878829929)
            ·
              refine ⟨2870274194587355159122447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827032259449806878829929 2870274194587355159122447)
              ·
                refine ⟨4305411291881032738683671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870274194587355159122447 4305411291881032738683671)
                ·
                  refine ⟨6458116937821549108025507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305411291881032738683671 6458116937821549108025507)
                  ·
                    refine ⟨9687175406732323662038261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458116937821549108025507 9687175406732323662038261)
                    ·
                      refine ⟨908172694381155343316087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9687175406732323662038261 908172694381155343316087)
                      ·
                        rfl

theorem cell23_1768660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1768660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768660 prefixEnd_1768660 := by exact prefixLift 1768660
  have htrace : WordTrace (prefixWord ++ tailWord_1768660) baseStart_1768660 baseEnd_1768660 := by
    simpa [prefixWord, tailWord_1768660, baseEnd_1768660] using wordTrace_append hprefix tailTrace_1768660
  have hstable : (prefixWord ++ tailWord_1768660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768660).length < 2 ^ (prefixWord ++ tailWord_1768660).sum := by decide
  have hdescent : baseEnd_1768660 < baseStart_1768660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768673 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1768673 : Nat := 118140960795 + 1768673 * 2 ^ 59
def prefixEnd_1768673 : Nat := 4983230072969 + 3 ^ 40 * 1768673 * 2
def baseEnd_1768673 : Nat := 908179369629663792453527

theorem tailTrace_1768673 : CollatzResearch.WordTrace tailWord_1768673 prefixEnd_1768673 908179369629663792453527 := by
  unfold tailWord_1768673
  simp only [CollatzResearch.WordTrace]
  refine ⟨64508803921407261144862673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43005869280938174096575115 64508803921407261144862673)
  ·
    refine ⟨48381602941055445858647005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64508803921407261144862673 48381602941055445858647005)
    ·
      refine ⟨18143101102895792196992627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48381602941055445858647005 18143101102895792196992627)
      ·
        refine ⟨27214651654343688295488941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18143101102895792196992627 27214651654343688295488941)
        ·
          refine ⟨10205494370378883110808353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27214651654343688295488941 10205494370378883110808353)
          ·
            refine ⟨7654120777784162333106265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10205494370378883110808353 7654120777784162333106265)
            ·
              refine ⟨5740590583338121749829699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654120777784162333106265 5740590583338121749829699)
              ·
                refine ⟨8610885875007182624744549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740590583338121749829699 8610885875007182624744549)
                ·
                  refine ⟨1614541101563846742139603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8610885875007182624744549 1614541101563846742139603)
                  ·
                    refine ⟨2421811652345770113209405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614541101563846742139603 2421811652345770113209405)
                    ·
                      refine ⟨908179369629663792453527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421811652345770113209405 908179369629663792453527)
                      ·
                        rfl

theorem cell23_1768673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1768673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768673 prefixEnd_1768673 := by exact prefixLift 1768673
  have htrace : WordTrace (prefixWord ++ tailWord_1768673) baseStart_1768673 baseEnd_1768673 := by
    simpa [prefixWord, tailWord_1768673, baseEnd_1768673] using wordTrace_append hprefix tailTrace_1768673
  have hstable : (prefixWord ++ tailWord_1768673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768673).length < 2 ^ (prefixWord ++ tailWord_1768673).sum := by decide
  have hdescent : baseEnd_1768673 < baseStart_1768673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768689 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1768689 : Nat := 118140960795 + 1768689 * 2 ^ 59
def prefixEnd_1768689 : Nat := 4983230072969 + 3 ^ 40 * 1768689 * 2
def baseEnd_1768689 : Nat := 302729195106711909951151

theorem tailTrace_1768689 : CollatzResearch.WordTrace tailWord_1768689 prefixEnd_1768689 302729195106711909951151 := by
  unfold tailWord_1768689
  simp only [CollatzResearch.WordTrace]
  refine ⟨64509387489349295877445121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43006258326232863918296747 64509387489349295877445121)
  ·
    refine ⟨48382040617011971908083841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64509387489349295877445121 48382040617011971908083841)
    ·
      refine ⟨36286530462758978931062881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48382040617011971908083841 36286530462758978931062881)
      ·
        refine ⟨27214897847069234198297161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36286530462758978931062881 27214897847069234198297161)
        ·
          refine ⟨20411173385301925648722871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27214897847069234198297161 20411173385301925648722871)
          ·
            refine ⟨30616760077952888473084307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20411173385301925648722871 30616760077952888473084307)
            ·
              refine ⟨45925140116929332709626461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30616760077952888473084307 45925140116929332709626461)
              ·
                refine ⟨17221927543848499766109923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45925140116929332709626461 17221927543848499766109923)
                ·
                  refine ⟨25832891315772749649164885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17221927543848499766109923 25832891315772749649164885)
                  ·
                    refine ⟨302729195106711909951151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25832891315772749649164885 302729195106711909951151)
                    ·
                      rfl

theorem cell23_1768689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1768689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768689 prefixEnd_1768689 := by exact prefixLift 1768689
  have htrace : WordTrace (prefixWord ++ tailWord_1768689) baseStart_1768689 baseEnd_1768689 := by
    simpa [prefixWord, tailWord_1768689, baseEnd_1768689] using wordTrace_append hprefix tailTrace_1768689
  have hstable : (prefixWord ++ tailWord_1768689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768689).length < 2 ^ (prefixWord ++ tailWord_1768689).sum := by decide
  have hdescent : baseEnd_1768689 < baseStart_1768689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768700 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_1768700 : Nat := 118140960795 + 1768700 * 2 ^ 59
def prefixEnd_1768700 : Nat := 4983230072969 + 3 ^ 40 * 1768700 * 2
def baseEnd_1768700 : Nat := 908193233607335186815903

theorem tailTrace_1768700 : CollatzResearch.WordTrace tailWord_1768700 prefixEnd_1768700 908193233607335186815903 := by
  unfold tailWord_1768700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32254894346154722378047777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43006525794872963170730369 32254894346154722378047777)
  ·
    refine ⟨24191170759616041783535833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32254894346154722378047777 24191170759616041783535833)
    ·
      refine ⟨18143378069712031337651875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24191170759616041783535833 18143378069712031337651875)
      ·
        refine ⟨27215067104568047006477813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18143378069712031337651875 27215067104568047006477813)
        ·
          refine ⟨2551412541053254406857295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27215067104568047006477813 2551412541053254406857295)
          ·
            refine ⟨3827118811579881610285943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551412541053254406857295 3827118811579881610285943)
            ·
              refine ⟨5740678217369822415428915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827118811579881610285943 5740678217369822415428915)
              ·
                refine ⟨8611017326054733623143373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740678217369822415428915 8611017326054733623143373)
                ·
                  refine ⟨3229131497270525108678765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8611017326054733623143373 3229131497270525108678765)
                  ·
                    refine ⟨1210924311476446915754537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229131497270525108678765 1210924311476446915754537)
                    ·
                      refine ⟨908193233607335186815903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210924311476446915754537 908193233607335186815903)
                      ·
                        rfl

theorem cell23_1768700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_1768700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768700 prefixEnd_1768700 := by exact prefixLift 1768700
  have htrace : WordTrace (prefixWord ++ tailWord_1768700) baseStart_1768700 baseEnd_1768700 := by
    simpa [prefixWord, tailWord_1768700, baseEnd_1768700] using wordTrace_append hprefix tailTrace_1768700
  have hstable : (prefixWord ++ tailWord_1768700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768700).length < 2 ^ (prefixWord ++ tailWord_1768700).sum := by decide
  have hdescent : baseEnd_1768700 < baseStart_1768700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768713 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 4, 2]
def baseStart_1768713 : Nat := 118140960795 + 1768713 * 2 ^ 59
def prefixEnd_1768713 : Nat := 4983230072969 + 3 ^ 40 * 1768713 * 2
def baseEnd_1768713 : Nat := 908199908855843635953343

theorem tailTrace_1768713 : CollatzResearch.WordTrace tailWord_1768713 prefixEnd_1768713 908199908855843635953343 := by
  unfold tailWord_1768713
  simp only [CollatzResearch.WordTrace]
  refine ⟨64510262841262347976318793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43006841894174898650879195 64510262841262347976318793)
  ·
    refine ⟨48382697130946760982239095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64510262841262347976318793 48382697130946760982239095)
    ·
      refine ⟨72574045696420141473358643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48382697130946760982239095 72574045696420141473358643)
      ·
        refine ⟨108861068544630212210037965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72574045696420141473358643 108861068544630212210037965)
        ·
          refine ⟨40822900704236329578764237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108861068544630212210037965 40822900704236329578764237)
          ·
            refine ⟨15308587764088623592036589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40822900704236329578764237 15308587764088623592036589)
            ·
              refine ⟨5740720411533233847013721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15308587764088623592036589 5740720411533233847013721)
              ·
                refine ⟨4305540308649925385260291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740720411533233847013721 4305540308649925385260291)
                ·
                  refine ⟨6458310462974888077890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305540308649925385260291 6458310462974888077890437)
                  ·
                    refine ⟨1210933211807791514604457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458310462974888077890437 1210933211807791514604457)
                    ·
                      refine ⟨908199908855843635953343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1210933211807791514604457 908199908855843635953343)
                      ·
                        rfl

theorem cell23_1768713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4, 2].length) (baseStart_1768713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768713 prefixEnd_1768713 := by exact prefixLift 1768713
  have htrace : WordTrace (prefixWord ++ tailWord_1768713) baseStart_1768713 baseEnd_1768713 := by
    simpa [prefixWord, tailWord_1768713, baseEnd_1768713] using wordTrace_append hprefix tailTrace_1768713
  have hstable : (prefixWord ++ tailWord_1768713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768713).length < 2 ^ (prefixWord ++ tailWord_1768713).sum := by decide
  have hdescent : baseEnd_1768713 < baseStart_1768713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768716 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1768716 : Nat := 118140960795 + 1768716 * 2 ^ 59
def prefixEnd_1768716 : Nat := 4983230072969 + 3 ^ 40 * 1768716 * 2
def baseEnd_1768716 : Nat := 908201449297807124215829

theorem tailTrace_1768716 : CollatzResearch.WordTrace tailWord_1768716 prefixEnd_1768716 908201449297807124215829 := by
  unfold tailWord_1768716
  simp only [CollatzResearch.WordTrace]
  refine ⟨32255186130125739744339001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43006914840167652992452001 32255186130125739744339001)
  ·
    refine ⟨24191389597594304808254251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32255186130125739744339001 24191389597594304808254251)
    ·
      refine ⟨36287084396391457212381377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24191389597594304808254251 36287084396391457212381377)
      ·
        refine ⟨27215313297293592909286033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36287084396391457212381377 27215313297293592909286033)
        ·
          refine ⟨20411484972970194681964525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27215313297293592909286033 20411484972970194681964525)
          ·
            refine ⟨7654306864863823005736697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20411484972970194681964525 7654306864863823005736697)
            ·
              refine ⟨5740730148647867254302523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7654306864863823005736697 5740730148647867254302523)
              ·
                refine ⟨8611095222971800881453785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740730148647867254302523 8611095222971800881453785)
                ·
                  refine ⟨6458321417228850661090339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8611095222971800881453785 6458321417228850661090339)
                  ·
                    refine ⟨9687482125843275991635509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6458321417228850661090339 9687482125843275991635509)
                    ·
                      refine ⟨908201449297807124215829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9687482125843275991635509 908201449297807124215829)
                      ·
                        rfl

theorem cell23_1768716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1768716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768716 prefixEnd_1768716 := by exact prefixLift 1768716
  have htrace : WordTrace (prefixWord ++ tailWord_1768716) baseStart_1768716 baseEnd_1768716 := by
    simpa [prefixWord, tailWord_1768716, baseEnd_1768716] using wordTrace_append hprefix tailTrace_1768716
  have hstable : (prefixWord ++ tailWord_1768716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768716).length < 2 ^ (prefixWord ++ tailWord_1768716).sum := by decide
  have hdescent : baseEnd_1768716 < baseStart_1768716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768733 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1768733 : Nat := 118140960795 + 1768733 * 2 ^ 59
def prefixEnd_1768733 : Nat := 4983230072969 + 3 ^ 40 * 1768733 * 2
def baseEnd_1768733 : Nat := 908210178468933557703251

theorem tailTrace_1768733 : CollatzResearch.WordTrace tailWord_1768733 prefixEnd_1768733 908210178468933557703251 := by
  unfold tailWord_1768733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64510992301189891392046853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43007328200793260928031235 64510992301189891392046853)
  ·
    refine ⟨12095811056473104636008785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64510992301189891392046853 12095811056473104636008785)
    ·
      refine ⟨9071858292354828477006589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12095811056473104636008785 9071858292354828477006589)
      ·
        refine ⟨3401946859633060678877471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9071858292354828477006589 3401946859633060678877471)
        ·
          refine ⟨5102920289449591018316207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401946859633060678877471 5102920289449591018316207)
          ·
            refine ⟨7654380434174386527474311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102920289449591018316207 7654380434174386527474311)
            ·
              refine ⟨11481570651261579791211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654380434174386527474311 11481570651261579791211467)
              ·
                refine ⟨17222355976892369686817201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11481570651261579791211467 17222355976892369686817201)
                ·
                  refine ⟨12916766982669277265112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17222355976892369686817201 12916766982669277265112901)
                  ·
                    refine ⟨2421893809250489487208669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12916766982669277265112901 2421893809250489487208669)
                    ·
                      refine ⟨908210178468933557703251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2421893809250489487208669 908210178468933557703251)
                      ·
                        rfl

theorem cell23_1768733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1768733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768733 prefixEnd_1768733 := by exact prefixLift 1768733
  have htrace : WordTrace (prefixWord ++ tailWord_1768733) baseStart_1768733 baseEnd_1768733 := by
    simpa [prefixWord, tailWord_1768733, baseEnd_1768733] using wordTrace_append hprefix tailTrace_1768733
  have hstable : (prefixWord ++ tailWord_1768733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768733).length < 2 ^ (prefixWord ++ tailWord_1768733).sum := by decide
  have hdescent : baseEnd_1768733 < baseStart_1768733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768816 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1768816 : Nat := 118140960795 + 1768816 * 2 ^ 59
def prefixEnd_1768816 : Nat := 4983230072969 + 3 ^ 40 * 1768816 * 2
def baseEnd_1768816 : Nat := 908252797363256732965369

theorem tailTrace_1768816 : CollatzResearch.WordTrace tailWord_1768816 prefixEnd_1768816 908252797363256732965369 := by
  unfold tailWord_1768816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32257009779944598283659151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43009346373259464378212201 32257009779944598283659151)
  ·
    refine ⟨48385514669916897425488727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32257009779944598283659151 48385514669916897425488727)
    ·
      refine ⟨72578272004875346138233091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48385514669916897425488727 72578272004875346138233091)
      ·
        refine ⟨108867408007313019207349637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72578272004875346138233091 108867408007313019207349637)
        ·
          refine ⟨20412639001371191101378057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108867408007313019207349637 20412639001371191101378057)
          ·
            refine ⟨15309479251028393326033543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20412639001371191101378057 15309479251028393326033543)
            ·
              refine ⟨22964218876542589989050315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309479251028393326033543 22964218876542589989050315)
              ·
                refine ⟨34446328314813884983575473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22964218876542589989050315 34446328314813884983575473)
                ·
                  refine ⟨25834746236110413737681605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34446328314813884983575473 25834746236110413737681605)
                  ·
                    refine ⟨4844014919270702575815301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25834746236110413737681605 4844014919270702575815301)
                    ·
                      refine ⟨908252797363256732965369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4844014919270702575815301 908252797363256732965369)
                      ·
                        rfl

theorem cell23_1768816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1768816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768816 prefixEnd_1768816 := by exact prefixLift 1768816
  have htrace : WordTrace (prefixWord ++ tailWord_1768816) baseStart_1768816 baseEnd_1768816 := by
    simpa [prefixWord, tailWord_1768816, baseEnd_1768816] using wordTrace_append hprefix tailTrace_1768816
  have hstable : (prefixWord ++ tailWord_1768816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768816).length < 2 ^ (prefixWord ++ tailWord_1768816).sum := by decide
  have hdescent : baseEnd_1768816 < baseStart_1768816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768823 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1768823 : Nat := 118140960795 + 1768823 * 2 ^ 59
def prefixEnd_1768823 : Nat := 4983230072969 + 3 ^ 40 * 1768823 * 2
def baseEnd_1768823 : Nat := 908256391727838205577837

theorem tailTrace_1768823 : CollatzResearch.WordTrace tailWord_1768823 prefixEnd_1768823 908256391727838205577837 := by
  unfold tailWord_1768823
  simp only [CollatzResearch.WordTrace]
  refine ⟨64514274870863836762823123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43009516580575891175215415 64514274870863836762823123)
  ·
    refine ⟨96771412306295755144234685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64514274870863836762823123 96771412306295755144234685)
    ·
      refine ⟨36289279614860908179088007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96771412306295755144234685 36289279614860908179088007)
      ·
        refine ⟨54433919422291362268632011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36289279614860908179088007 54433919422291362268632011)
        ·
          refine ⟨81650879133437043402948017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54433919422291362268632011 81650879133437043402948017)
          ·
            refine ⟨61238159350077782552211013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81650879133437043402948017 61238159350077782552211013)
            ·
              refine ⟨11482154878139584228539565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61238159350077782552211013 11482154878139584228539565)
              ·
                refine ⟨4305808079302344085702337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11482154878139584228539565 4305808079302344085702337)
                ·
                  refine ⟨3229356059476758064276753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305808079302344085702337 3229356059476758064276753)
                  ·
                    refine ⟨2422017044607568548207565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229356059476758064276753 2422017044607568548207565)
                    ·
                      refine ⟨908256391727838205577837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422017044607568548207565 908256391727838205577837)
                      ·
                        rfl

theorem cell23_1768823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1768823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768823 prefixEnd_1768823 := by exact prefixLift 1768823
  have htrace : WordTrace (prefixWord ++ tailWord_1768823) baseStart_1768823 baseEnd_1768823 := by
    simpa [prefixWord, tailWord_1768823, baseEnd_1768823] using wordTrace_append hprefix tailTrace_1768823
  have hstable : (prefixWord ++ tailWord_1768823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768823).length < 2 ^ (prefixWord ++ tailWord_1768823).sum := by decide
  have hdescent : baseEnd_1768823 < baseStart_1768823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768840 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1768840 : Nat := 118140960795 + 1768840 * 2 ^ 59
def prefixEnd_1768840 : Nat := 4983230072969 + 3 ^ 40 * 1768840 * 2
def baseEnd_1768840 : Nat := 908265120898964639065259

theorem tailTrace_1768840 : CollatzResearch.WordTrace tailWord_1768840 prefixEnd_1768840 908265120898964639065259 := by
  unfold tailWord_1768840
  simp only [CollatzResearch.WordTrace]
  refine ⟨32257447455901124333095987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43009929941201499110794649 32257447455901124333095987)
  ·
    refine ⟨48386171183851686499643981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32257447455901124333095987 48386171183851686499643981)
    ·
      refine ⟨18144814193944382437366493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48386171183851686499643981 18144814193944382437366493)
      ·
        refine ⟨6804305322729143414012435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18144814193944382437366493 6804305322729143414012435)
        ·
          refine ⟨10206457984093715121018653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804305322729143414012435 10206457984093715121018653)
          ·
            refine ⟨3827421744035143170381995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10206457984093715121018653 3827421744035143170381995)
            ·
              refine ⟨5741132616052714755572993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827421744035143170381995 5741132616052714755572993)
              ·
                refine ⟨4305849462039536066679745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741132616052714755572993 4305849462039536066679745)
                ·
                  refine ⟨3229387096529652050009809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305849462039536066679745 3229387096529652050009809)
                  ·
                    refine ⟨2422040322397239037507357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3229387096529652050009809 2422040322397239037507357)
                    ·
                      refine ⟨908265120898964639065259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422040322397239037507357 908265120898964639065259)
                      ·
                        rfl

theorem cell23_1768840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1768840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768840 prefixEnd_1768840 := by exact prefixLift 1768840
  have htrace : WordTrace (prefixWord ++ tailWord_1768840) baseStart_1768840 baseEnd_1768840 := by
    simpa [prefixWord, tailWord_1768840, baseEnd_1768840] using wordTrace_append hprefix tailTrace_1768840
  have hstable : (prefixWord ++ tailWord_1768840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768840).length < 2 ^ (prefixWord ++ tailWord_1768840).sum := by decide
  have hdescent : baseEnd_1768840 < baseStart_1768840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768887 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_1768887 : Nat := 118140960795 + 1768887 * 2 ^ 59
def prefixEnd_1768887 : Nat := 4983230072969 + 3 ^ 40 * 1768887 * 2
def baseEnd_1768887 : Nat := 908289254489725955177543

theorem tailTrace_1768887 : CollatzResearch.WordTrace tailWord_1768887 prefixEnd_1768887 908289254489725955177543 := by
  unfold tailWord_1768887
  simp only [CollatzResearch.WordTrace]
  refine ⟨64516609142631975693152915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43011072761754650462101943 64516609142631975693152915)
  ·
    refine ⟨96774913713947963539729373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64516609142631975693152915 96774913713947963539729373)
    ·
      refine ⟨36290592642730486327398515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96774913713947963539729373 36290592642730486327398515)
      ·
        refine ⟨54435888964095729491097773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36290592642730486327398515 54435888964095729491097773)
        ·
          refine ⟨20413458361535898559161665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54435888964095729491097773 20413458361535898559161665)
          ·
            refine ⟨15310093771151923919371249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20413458361535898559161665 15310093771151923919371249)
            ·
              refine ⟨11482570328363942939528437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15310093771151923919371249 11482570328363942939528437)
              ·
                refine ⟨1076490968284119650580791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11482570328363942939528437 1076490968284119650580791)
                ·
                  refine ⟨1614736452426179475871187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076490968284119650580791 1614736452426179475871187)
                  ·
                    refine ⟨2422104678639269213806781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1614736452426179475871187 2422104678639269213806781)
                    ·
                      refine ⟨908289254489725955177543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422104678639269213806781 908289254489725955177543)
                      ·
                        rfl

theorem cell23_1768887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_1768887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768887 prefixEnd_1768887 := by exact prefixLift 1768887
  have htrace : WordTrace (prefixWord ++ tailWord_1768887) baseStart_1768887 baseEnd_1768887 := by
    simpa [prefixWord, tailWord_1768887, baseEnd_1768887] using wordTrace_append hprefix tailTrace_1768887
  have hstable : (prefixWord ++ tailWord_1768887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768887).length < 2 ^ (prefixWord ++ tailWord_1768887).sum := by decide
  have hdescent : baseEnd_1768887 < baseStart_1768887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768920 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1768920 : Nat := 118140960795 + 1768920 * 2 ^ 59
def prefixEnd_1768920 : Nat := 4983230072969 + 3 ^ 40 * 1768920 * 2
def baseEnd_1768920 : Nat := 302768733117108108688297

theorem tailTrace_1768920 : CollatzResearch.WordTrace tailWord_1768920 prefixEnd_1768920 302768733117108108688297 := by
  unfold tailWord_1768920
  simp only [CollatzResearch.WordTrace]
  refine ⟨32258906375756211164552107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43011875167674948219402809 32258906375756211164552107)
  ·
    refine ⟨48388359563634316746828161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32258906375756211164552107 48388359563634316746828161)
    ·
      refine ⟨36291269672725737560121121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48388359563634316746828161 36291269672725737560121121)
      ·
        refine ⟨27218452254544303170090841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36291269672725737560121121 27218452254544303170090841)
        ·
          refine ⟨20413839190908227377568131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27218452254544303170090841 20413839190908227377568131)
          ·
            refine ⟨30620758786362341066352197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20413839190908227377568131 30620758786362341066352197)
            ·
              refine ⟨5741392272442938949941037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30620758786362341066352197 5741392272442938949941037)
              ·
                refine ⟨2153022102166102106227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741392272442938949941037 2153022102166102106227889)
                ·
                  refine ⟨1614766576624576579670917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153022102166102106227889 1614766576624576579670917)
                  ·
                    refine ⟨302768733117108108688297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1614766576624576579670917 302768733117108108688297)
                    ·
                      rfl

theorem cell23_1768920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1768920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768920 prefixEnd_1768920 := by exact prefixLift 1768920
  have htrace : WordTrace (prefixWord ++ tailWord_1768920) baseStart_1768920 baseEnd_1768920 := by
    simpa [prefixWord, tailWord_1768920, baseEnd_1768920] using wordTrace_append hprefix tailTrace_1768920
  have hstable : (prefixWord ++ tailWord_1768920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768920).length < 2 ^ (prefixWord ++ tailWord_1768920).sum := by decide
  have hdescent : baseEnd_1768920 < baseStart_1768920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768927 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 3, 2, 2]
def baseStart_1768927 : Nat := 118140960795 + 1768927 * 2 ^ 59
def prefixEnd_1768927 : Nat := 4983230072969 + 3 ^ 40 * 1768927 * 2
def baseEnd_1768927 : Nat := 908309793715905798677359

theorem tailTrace_1768927 : CollatzResearch.WordTrace tailWord_1768927 prefixEnd_1768927 908309793715905798677359 := by
  unfold tailWord_1768927
  simp only [CollatzResearch.WordTrace]
  refine ⟨64518068062487062524609035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43012045374991375016406023 64518068062487062524609035)
  ·
    refine ⟨96777102093730593786913553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64518068062487062524609035 96777102093730593786913553)
    ·
      refine ⟨72582826570297945340185165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96777102093730593786913553 72582826570297945340185165)
      ·
        refine ⟨27218559963861729502569437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72582826570297945340185165 27218559963861729502569437)
        ·
          refine ⟨10206959986448148563463539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27218559963861729502569437 10206959986448148563463539)
          ·
            refine ⟨15310439979672222845195309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206959986448148563463539 15310439979672222845195309)
            ·
              refine ⟨5741414992377083566948241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15310439979672222845195309 5741414992377083566948241)
              ·
                refine ⟨4306061244282812675211181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741414992377083566948241 4306061244282812675211181)
                ·
                  refine ⟨1614772966606054753204193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4306061244282812675211181 1614772966606054753204193)
                  ·
                    refine ⟨1211079724954541064903145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614772966606054753204193 1211079724954541064903145)
                    ·
                      refine ⟨908309793715905798677359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211079724954541064903145 908309793715905798677359)
                      ·
                        rfl

theorem cell23_1768927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_1768927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768927 prefixEnd_1768927 := by exact prefixLift 1768927
  have htrace : WordTrace (prefixWord ++ tailWord_1768927) baseStart_1768927 baseEnd_1768927 := by
    simpa [prefixWord, tailWord_1768927, baseEnd_1768927] using wordTrace_append hprefix tailTrace_1768927
  have hstable : (prefixWord ++ tailWord_1768927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768927).length < 2 ^ (prefixWord ++ tailWord_1768927).sum := by decide
  have hdescent : baseEnd_1768927 < baseStart_1768927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768941 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1768941 : Nat := 118140960795 + 1768941 * 2 ^ 59
def prefixEnd_1768941 : Nat := 4983230072969 + 3 ^ 40 * 1768941 * 2
def baseEnd_1768941 : Nat := 302772327481689581300765

theorem tailTrace_1768941 : CollatzResearch.WordTrace tailWord_1768941 prefixEnd_1768941 302772327481689581300765 := by
  unfold tailWord_1768941
  simp only [CollatzResearch.WordTrace]
  refine ⟨64518578684436342915618677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43012385789624228610412451 64518578684436342915618677)
  ·
    refine ⟨6048616751665907148339251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64518578684436342915618677 6048616751665907148339251)
    ·
      refine ⟨9072925127498860722508877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6048616751665907148339251 9072925127498860722508877)
      ·
        refine ⟨3402346922812072770940829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9072925127498860722508877 3402346922812072770940829)
        ·
          refine ⟨1275880096054527289102811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3402346922812072770940829 1275880096054527289102811)
          ·
            refine ⟨1913820144081790933654217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275880096054527289102811 1913820144081790933654217)
            ·
              refine ⟨1435365108061343200240663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913820144081790933654217 1435365108061343200240663)
              ·
                refine ⟨2153047662092014800360995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435365108061343200240663 2153047662092014800360995)
                ·
                  refine ⟨3229571493138022200541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153047662092014800360995 3229571493138022200541493)
                  ·
                    refine ⟨302772327481689581300765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3229571493138022200541493 302772327481689581300765)
                    ·
                      rfl

theorem cell23_1768941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1768941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768941 prefixEnd_1768941 := by exact prefixLift 1768941
  have htrace : WordTrace (prefixWord ++ tailWord_1768941) baseStart_1768941 baseEnd_1768941 := by
    simpa [prefixWord, tailWord_1768941, baseEnd_1768941] using wordTrace_append hprefix tailTrace_1768941
  have hstable : (prefixWord ++ tailWord_1768941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768941).length < 2 ^ (prefixWord ++ tailWord_1768941).sum := by decide
  have hdescent : baseEnd_1768941 < baseStart_1768941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768944 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 1, 2, 2]
def baseStart_1768944 : Nat := 118140960795 + 1768944 * 2 ^ 59
def prefixEnd_1768944 : Nat := 4983230072969 + 3 ^ 40 * 1768944 * 2
def baseEnd_1768944 : Nat := 908318522887032232164781

theorem tailTrace_1768944 : CollatzResearch.WordTrace tailWord_1768944 prefixEnd_1768944 908318522887032232164781 := by
  unfold tailWord_1768944
  simp only [CollatzResearch.WordTrace]
  refine ⟨32259344051712737213988943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43012458735616982951985257 32259344051712737213988943)
  ·
    refine ⟨48389016077569105820983415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32259344051712737213988943 48389016077569105820983415)
    ·
      refine ⟨72583524116353658731475123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48389016077569105820983415 72583524116353658731475123)
      ·
        refine ⟨108875286174530488097212685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72583524116353658731475123 108875286174530488097212685)
        ·
          refine ⟨40828232315448933036454757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108875286174530488097212685 40828232315448933036454757)
          ·
            refine ⟨7655293559146674944335267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40828232315448933036454757 7655293559146674944335267)
            ·
              refine ⟨11482940338720012416502901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655293559146674944335267 11482940338720012416502901)
              ·
                refine ⟨1076525656755001164047147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11482940338720012416502901 1076525656755001164047147)
                ·
                  refine ⟨1614788485132501746070721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076525656755001164047147 1614788485132501746070721)
                  ·
                    refine ⟨1211091363849376309553041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614788485132501746070721 1211091363849376309553041)
                    ·
                      refine ⟨908318522887032232164781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211091363849376309553041 908318522887032232164781)
                      ·
                        rfl

theorem cell23_1768944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 2, 2].length) (baseStart_1768944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768944 prefixEnd_1768944 := by exact prefixLift 1768944
  have htrace : WordTrace (prefixWord ++ tailWord_1768944) baseStart_1768944 baseEnd_1768944 := by
    simpa [prefixWord, tailWord_1768944, baseEnd_1768944] using wordTrace_append hprefix tailTrace_1768944
  have hstable : (prefixWord ++ tailWord_1768944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768944).length < 2 ^ (prefixWord ++ tailWord_1768944).sum := by decide
  have hdescent : baseEnd_1768944 < baseStart_1768944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1768974 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1768974 : Nat := 118140960795 + 1768974 * 2 ^ 59
def prefixEnd_1768974 : Nat := 4983230072969 + 3 ^ 40 * 1768974 * 2
def baseEnd_1768974 : Nat := 908333927306667114789643

theorem tailTrace_1768974 : CollatzResearch.WordTrace tailWord_1768974 prefixEnd_1768974 908333927306667114789643 := by
  unfold tailWord_1768974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064972786664598693946247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43013188195544526367713317 8064972786664598693946247)
  ·
    refine ⟨12097459179996898040919371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8064972786664598693946247 12097459179996898040919371)
    ·
      refine ⟨18146188769995347061379057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097459179996898040919371 18146188769995347061379057)
      ·
        refine ⟨13609641577496510296034293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18146188769995347061379057 13609641577496510296034293)
        ·
          refine ⟨1275903897890297840253215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13609641577496510296034293 1275903897890297840253215)
          ·
            refine ⟨1913855846835446760379823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275903897890297840253215 1913855846835446760379823)
            ·
              refine ⟨2870783770253170140569735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913855846835446760379823 2870783770253170140569735)
              ·
                refine ⟨4306175655379755210854603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870783770253170140569735 4306175655379755210854603)
                ·
                  refine ⟨6459263483069632816281905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306175655379755210854603 6459263483069632816281905)
                  ·
                    refine ⟨4844447612302224612211429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6459263483069632816281905 4844447612302224612211429)
                    ·
                      refine ⟨908333927306667114789643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4844447612302224612211429 908333927306667114789643)
                      ·
                        rfl

theorem cell23_1768974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1768974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1768974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1768974 prefixEnd_1768974 := by exact prefixLift 1768974
  have htrace : WordTrace (prefixWord ++ tailWord_1768974) baseStart_1768974 baseEnd_1768974 := by
    simpa [prefixWord, tailWord_1768974, baseEnd_1768974] using wordTrace_append hprefix tailTrace_1768974
  have hstable : (prefixWord ++ tailWord_1768974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1768974).length < 2 ^ (prefixWord ++ tailWord_1768974).sum := by decide
  have hdescent : baseEnd_1768974 < baseStart_1768974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1768974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769003 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3]
def baseStart_1769003 : Nat := 118140960795 + 1769003 * 2 ^ 59
def prefixEnd_1769003 : Nat := 4983230072969 + 3 ^ 40 * 1769003 * 2
def baseEnd_1769003 : Nat := 908348818245647501327009

theorem tailTrace_1769003 : CollatzResearch.WordTrace tailWord_1769003 prefixEnd_1769003 908348818245647501327009 := by
  unfold tailWord_1769003
  simp only [CollatzResearch.WordTrace]
  refine ⟨64520840010211727504375663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43013893340141151669583775 64520840010211727504375663)
  ·
    refine ⟨96781260015317591256563495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64520840010211727504375663 96781260015317591256563495)
    ·
      refine ⟨145171890022976386884845243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96781260015317591256563495 145171890022976386884845243)
      ·
        refine ⟨217757835034464580327267865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145171890022976386884845243 217757835034464580327267865)
        ·
          refine ⟨163318376275848435245450899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217757835034464580327267865 163318376275848435245450899)
          ·
            refine ⟨244977564413772652868176349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163318376275848435245450899 244977564413772652868176349)
            ·
              refine ⟨91866586655164744825566131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244977564413772652868176349 91866586655164744825566131)
              ·
                refine ⟨137799879982747117238349197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91866586655164744825566131 137799879982747117238349197)
                ·
                  refine ⟨51674954993530168964380949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137799879982747117238349197 51674954993530168964380949)
                  ·
                    refine ⟨2422263515321726670205357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51674954993530168964380949 2422263515321726670205357)
                    ·
                      refine ⟨908348818245647501327009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422263515321726670205357 908348818245647501327009)
                      ·
                        rfl

theorem cell23_1769003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].length) (baseStart_1769003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769003 prefixEnd_1769003 := by exact prefixLift 1769003
  have htrace : WordTrace (prefixWord ++ tailWord_1769003) baseStart_1769003 baseEnd_1769003 := by
    simpa [prefixWord, tailWord_1769003, baseEnd_1769003] using wordTrace_append hprefix tailTrace_1769003
  have hstable : (prefixWord ++ tailWord_1769003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769003).length < 2 ^ (prefixWord ++ tailWord_1769003).sum := by decide
  have hdescent : baseEnd_1769003 < baseStart_1769003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769034 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_1769034 : Nat := 118140960795 + 1769034 * 2 ^ 59
def prefixEnd_1769034 : Nat := 4983230072969 + 3 ^ 40 * 1769034 * 2
def baseEnd_1769034 : Nat := 908364736145936880039367

theorem tailTrace_1769034 : CollatzResearch.WordTrace tailWord_1769034 prefixEnd_1769034 908364736145936880039367 := by
  unfold tailWord_1769034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130492668274854949688539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43014647115399613199169437 16130492668274854949688539)
  ·
    refine ⟨24195739002412282424532809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16130492668274854949688539 24195739002412282424532809)
    ·
      refine ⟨18146804251809211818399607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24195739002412282424532809 18146804251809211818399607)
      ·
        refine ⟨27220206377713817727599411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18146804251809211818399607 27220206377713817727599411)
        ·
          refine ⟨40830309566570726591399117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27220206377713817727599411 40830309566570726591399117)
          ·
            refine ⟨15311366087464022471774669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40830309566570726591399117 15311366087464022471774669)
            ·
              refine ⟨5741762282799008426915501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15311366087464022471774669 5741762282799008426915501)
              ·
                refine ⟨2153160856049628160093313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741762282799008426915501 2153160856049628160093313)
                ·
                  refine ⟨1614870642037221120069985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153160856049628160093313 1614870642037221120069985)
                  ·
                    refine ⟨1211152981527915840052489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1614870642037221120069985 1211152981527915840052489)
                    ·
                      refine ⟨908364736145936880039367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211152981527915840052489 908364736145936880039367)
                      ·
                        rfl

theorem cell23_1769034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_1769034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769034 prefixEnd_1769034 := by exact prefixLift 1769034
  have htrace : WordTrace (prefixWord ++ tailWord_1769034) baseStart_1769034 baseEnd_1769034 := by
    simpa [prefixWord, tailWord_1769034, baseEnd_1769034] using wordTrace_append hprefix tailTrace_1769034
  have hstable : (prefixWord ++ tailWord_1769034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769034).length < 2 ^ (prefixWord ++ tailWord_1769034).sum := by decide
  have hdescent : baseEnd_1769034 < baseStart_1769034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769074 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_1769074 : Nat := 118140960795 + 1769074 * 2 ^ 59
def prefixEnd_1769074 : Nat := 4983230072969 + 3 ^ 40 * 1769074 * 2
def baseEnd_1769074 : Nat := 100931697263568524837687

theorem tailTrace_1769074 : CollatzResearch.WordTrace tailWord_1769074 prefixEnd_1769074 100931697263568524837687 := by
  unfold tailWord_1769074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130857398238626657552569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43015619728636337753473517 16130857398238626657552569)
  ·
    refine ⟨12098143048678969993164427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16130857398238626657552569 12098143048678969993164427)
    ·
      refine ⟨18147214573018454989746641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12098143048678969993164427 18147214573018454989746641)
      ·
        refine ⟨13610410929763841242309981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18147214573018454989746641 13610410929763841242309981)
        ·
          refine ⟨5103904098661440465866243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13610410929763841242309981 5103904098661440465866243)
          ·
            refine ⟨7655856147992160698799365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103904098661440465866243 7655856147992160698799365)
            ·
              refine ⟨1435473027748530131024881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7655856147992160698799365 1435473027748530131024881)
              ·
                refine ⟨1076604770811397598268661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435473027748530131024881 1076604770811397598268661)
                ·
                  refine ⟨100931697263568524837687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076604770811397598268661 100931697263568524837687)
                  ·
                    rfl

theorem cell23_1769074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_1769074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769074 prefixEnd_1769074 := by exact prefixLift 1769074
  have htrace : WordTrace (prefixWord ++ tailWord_1769074) baseStart_1769074 baseEnd_1769074 := by
    simpa [prefixWord, tailWord_1769074, baseEnd_1769074] using wordTrace_append hprefix tailTrace_1769074
  have hstable : (prefixWord ++ tailWord_1769074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769074).length < 2 ^ (prefixWord ++ tailWord_1769074).sum := by decide
  have hdescent : baseEnd_1769074 < baseStart_1769074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_1769103 : Nat := 118140960795 + 1769103 * 2 ^ 59
def prefixEnd_1769103 : Nat := 4983230072969 + 3 ^ 40 * 1769103 * 2
def baseEnd_1769103 : Nat := 908400166311097110076549

theorem tailTrace_1769103 : CollatzResearch.WordTrace tailWord_1769103 prefixEnd_1769103 908400166311097110076549 := by
  unfold tailWord_1769103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64524487309849444583015963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43016324873232963055343975 64524487309849444583015963)
  ·
    refine ⟨96786730964774166874523945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64524487309849444583015963 96786730964774166874523945)
    ·
      refine ⟨72590048223580625155892959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96786730964774166874523945 72590048223580625155892959)
      ·
        refine ⟨108885072335370937733839439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72590048223580625155892959 108885072335370937733839439)
        ·
          refine ⟨163327608503056406600759159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108885072335370937733839439 163327608503056406600759159)
          ·
            refine ⟨244991412754584609901138739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163327608503056406600759159 244991412754584609901138739)
            ·
              refine ⟨367487119131876914851708109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244991412754584609901138739 367487119131876914851708109)
              ·
                refine ⟨137807669674453843069390541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367487119131876914851708109 137807669674453843069390541)
                ·
                  refine ⟨51677876127920191151021453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137807669674453843069390541 51677876127920191151021453)
                  ·
                    refine ⟨19379203547970071681633045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51677876127920191151021453 19379203547970071681633045)
                    ·
                      refine ⟨908400166311097110076549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19379203547970071681633045 908400166311097110076549)
                      ·
                        rfl

theorem cell23_1769103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_1769103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769103 prefixEnd_1769103 := by exact prefixLift 1769103
  have htrace : WordTrace (prefixWord ++ tailWord_1769103) baseStart_1769103 baseEnd_1769103 := by
    simpa [prefixWord, tailWord_1769103, baseEnd_1769103] using wordTrace_append hprefix tailTrace_1769103
  have hstable : (prefixWord ++ tailWord_1769103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769103).length < 2 ^ (prefixWord ++ tailWord_1769103).sum := by decide
  have hdescent : baseEnd_1769103 < baseStart_1769103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769120 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1769120 : Nat := 118140960795 + 1769120 * 2 ^ 59
def prefixEnd_1769120 : Nat := 4983230072969 + 3 ^ 40 * 1769120 * 2
def baseEnd_1769120 : Nat := 908408895482223543563971

theorem tailTrace_1769120 : CollatzResearch.WordTrace tailWord_1769120 prefixEnd_1769120 908408895482223543563971 := by
  unfold tailWord_1769120
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262553675393928243192407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43016738233858570990923209 32262553675393928243192407)
  ·
    refine ⟨48393830513090892364788611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32262553675393928243192407 48393830513090892364788611)
    ·
      refine ⟨72590745769636338547182917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48393830513090892364788611 72590745769636338547182917)
      ·
        refine ⟨13610764831806813477596797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72590745769636338547182917 13610764831806813477596797)
        ·
          refine ⟨5104036811927555054098799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13610764831806813477596797 5104036811927555054098799)
          ·
            refine ⟨7656055217891332581148199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104036811927555054098799 7656055217891332581148199)
            ·
              refine ⟨11484082826836998871722299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656055217891332581148199 11484082826836998871722299)
              ·
                refine ⟨17226124240255498307583449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11484082826836998871722299 17226124240255498307583449)
                ·
                  refine ⟨12919593180191623730687587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17226124240255498307583449 12919593180191623730687587)
                  ·
                    refine ⟨19379389770287435596031381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12919593180191623730687587 19379389770287435596031381)
                    ·
                      refine ⟨908408895482223543563971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19379389770287435596031381 908408895482223543563971)
                      ·
                        rfl

theorem cell23_1769120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1769120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769120 prefixEnd_1769120 := by exact prefixLift 1769120
  have htrace : WordTrace (prefixWord ++ tailWord_1769120) baseStart_1769120 baseEnd_1769120 := by
    simpa [prefixWord, tailWord_1769120, baseEnd_1769120] using wordTrace_append hprefix tailTrace_1769120
  have hstable : (prefixWord ++ tailWord_1769120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769120).length < 2 ^ (prefixWord ++ tailWord_1769120).sum := by decide
  have hdescent : baseEnd_1769120 < baseStart_1769120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769167 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 6, 3, 2]
def baseStart_1769167 : Nat := 118140960795 + 1769167 * 2 ^ 59
def prefixEnd_1769167 : Nat := 4983230072969 + 3 ^ 40 * 1769167 * 2
def baseEnd_1769167 : Nat := 908433029072984859676255

theorem tailTrace_1769167 : CollatzResearch.WordTrace tailWord_1769167 prefixEnd_1769167 908433029072984859676255 := by
  unfold tailWord_1769167
  simp only [CollatzResearch.WordTrace]
  refine ⟨64526821581617583513345755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43017881054411722342230503 64526821581617583513345755)
  ·
    refine ⟨96790232372426375270018633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64526821581617583513345755 96790232372426375270018633)
    ·
      refine ⟨72592674279319781452513975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96790232372426375270018633 72592674279319781452513975)
      ·
        refine ⟨108889011418979672178770963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72592674279319781452513975 108889011418979672178770963)
        ·
          refine ⟨163333517128469508268156445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108889011418979672178770963 163333517128469508268156445)
          ·
            refine ⟨61250068923176065600558667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163333517128469508268156445 61250068923176065600558667)
            ·
              refine ⟨91875103384764098400838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61250068923176065600558667 91875103384764098400838001)
              ·
                refine ⟨68906327538573073800628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91875103384764098400838001 68906327538573073800628501)
                ·
                  refine ⟨3229984103370612834404461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68906327538573073800628501 3229984103370612834404461)
                  ·
                    refine ⟨1211244038763979812901673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229984103370612834404461 1211244038763979812901673)
                    ·
                      refine ⟨908433029072984859676255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211244038763979812901673 908433029072984859676255)
                      ·
                        rfl

theorem cell23_1769167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3, 2].length) (baseStart_1769167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769167 prefixEnd_1769167 := by exact prefixLift 1769167
  have htrace : WordTrace (prefixWord ++ tailWord_1769167) baseStart_1769167 baseEnd_1769167 := by
    simpa [prefixWord, tailWord_1769167, baseEnd_1769167] using wordTrace_append hprefix tailTrace_1769167
  have hstable : (prefixWord ++ tailWord_1769167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769167).length < 2 ^ (prefixWord ++ tailWord_1769167).sum := by decide
  have hdescent : baseEnd_1769167 < baseStart_1769167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769177 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_1769177 : Nat := 118140960795 + 1769177 * 2 ^ 59
def prefixEnd_1769177 : Nat := 4983230072969 + 3 ^ 40 * 1769177 * 2
def baseEnd_1769177 : Nat := 302812721293176606850403

theorem tailTrace_1769177 : CollatzResearch.WordTrace tailWord_1769177 prefixEnd_1769177 302812721293176606850403 := by
  unfold tailWord_1769177
  simp only [CollatzResearch.WordTrace]
  refine ⟨64527186311581355221209785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43018124207720903480806523 64527186311581355221209785)
  ·
    refine ⟨48395389733686016415907339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64527186311581355221209785 48395389733686016415907339)
    ·
      refine ⟨72593084600529024623861009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48395389733686016415907339 72593084600529024623861009)
      ·
        refine ⟨54444813450396768467895757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72593084600529024623861009 54444813450396768467895757)
        ·
          refine ⟨20416805043898788175460909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54444813450396768467895757 20416805043898788175460909)
          ·
            refine ⟨7656301891462045565797841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20416805043898788175460909 7656301891462045565797841)
            ·
              refine ⟨5742226418596534174348381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656301891462045565797841 5742226418596534174348381)
              ·
                refine ⟨2153334906973700315380643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5742226418596534174348381 2153334906973700315380643)
                ·
                  refine ⟨3230002360460550473070965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153334906973700315380643 3230002360460550473070965)
                  ·
                    refine ⟨302812721293176606850403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3230002360460550473070965 302812721293176606850403)
                    ·
                      rfl

theorem cell23_1769177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_1769177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769177 prefixEnd_1769177 := by exact prefixLift 1769177
  have htrace : WordTrace (prefixWord ++ tailWord_1769177) baseStart_1769177 baseEnd_1769177 := by
    simpa [prefixWord, tailWord_1769177, baseEnd_1769177] using wordTrace_append hprefix tailTrace_1769177
  have hstable : (prefixWord ++ tailWord_1769177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769177).length < 2 ^ (prefixWord ++ tailWord_1769177).sum := by decide
  have hdescent : baseEnd_1769177 < baseStart_1769177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769200 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1769200 : Nat := 118140960795 + 1769200 * 2 ^ 59
def prefixEnd_1769200 : Nat := 4983230072969 + 3 ^ 40 * 1769200 * 2
def baseEnd_1769200 : Nat := 908449973934583230563603

theorem tailTrace_1769200 : CollatzResearch.WordTrace tailWord_1769200 prefixEnd_1769200 908449973934583230563603 := by
  unfold tailWord_1769200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32264012595249015074648527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43018683460332020099531369 32264012595249015074648527)
  ·
    refine ⟨48396018892873522611972791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32264012595249015074648527 48396018892873522611972791)
    ·
      refine ⟨72594028339310283917959187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48396018892873522611972791 72594028339310283917959187)
      ·
        refine ⟨108891042508965425876938781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72594028339310283917959187 108891042508965425876938781)
        ·
          refine ⟨40834140940862034703852043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108891042508965425876938781 40834140940862034703852043)
          ·
            refine ⟨61251211411293052055778065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40834140940862034703852043 61251211411293052055778065)
            ·
              refine ⟨45938408558469789041833549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61251211411293052055778065 45938408558469789041833549)
              ·
                refine ⟨17226903209426170890687581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45938408558469789041833549 17226903209426170890687581)
                ·
                  refine ⟨6460088703534814084007843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17226903209426170890687581 6460088703534814084007843)
                  ·
                    refine ⟨9690133055302221126011765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6460088703534814084007843 9690133055302221126011765)
                    ·
                      refine ⟨908449973934583230563603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9690133055302221126011765 908449973934583230563603)
                      ·
                        rfl

theorem cell23_1769200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1769200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769200 prefixEnd_1769200 := by exact prefixLift 1769200
  have htrace : WordTrace (prefixWord ++ tailWord_1769200) baseStart_1769200 baseEnd_1769200 := by
    simpa [prefixWord, tailWord_1769200, baseEnd_1769200] using wordTrace_append hprefix tailTrace_1769200
  have hstable : (prefixWord ++ tailWord_1769200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769200).length < 2 ^ (prefixWord ++ tailWord_1769200).sum := by decide
  have hdescent : baseEnd_1769200 < baseStart_1769200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769247 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1769247 : Nat := 118140960795 + 1769247 * 2 ^ 59
def prefixEnd_1769247 : Nat := 4983230072969 + 3 ^ 40 * 1769247 * 2
def baseEnd_1769247 : Nat := 908474107525344546675887

theorem tailTrace_1769247 : CollatzResearch.WordTrace tailWord_1769247 prefixEnd_1769247 908474107525344546675887 := by
  unfold tailWord_1769247
  simp only [CollatzResearch.WordTrace]
  refine ⟨64529739421327757176257995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43019826280885171450838663 64529739421327757176257995)
  ·
    refine ⟨96794609131991635764386993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64529739421327757176257995 96794609131991635764386993)
    ·
      refine ⟨72595956848993726823290245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96794609131991635764386993 72595956848993726823290245)
      ·
        refine ⟨13611741909186323779366921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72595956848993726823290245 13611741909186323779366921)
        ·
          refine ⟨10208806431889742834525191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13611741909186323779366921 10208806431889742834525191)
          ·
            refine ⟨15313209647834614251787787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10208806431889742834525191 15313209647834614251787787)
            ·
              refine ⟨22969814471751921377681681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15313209647834614251787787 22969814471751921377681681)
              ·
                refine ⟨17227360853813941033261261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22969814471751921377681681 17227360853813941033261261)
                ·
                  refine ⟨6460260320180227887472973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17227360853813941033261261 6460260320180227887472973)
                  ·
                    refine ⟨2422597620067585457802365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6460260320180227887472973 2422597620067585457802365)
                    ·
                      refine ⟨908474107525344546675887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422597620067585457802365 908474107525344546675887)
                      ·
                        rfl

theorem cell23_1769247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1769247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769247 prefixEnd_1769247 := by exact prefixLift 1769247
  have htrace : WordTrace (prefixWord ++ tailWord_1769247) baseStart_1769247 baseEnd_1769247 := by
    simpa [prefixWord, tailWord_1769247, baseEnd_1769247] using wordTrace_append hprefix tailTrace_1769247
  have hstable : (prefixWord ++ tailWord_1769247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769247).length < 2 ^ (prefixWord ++ tailWord_1769247).sum := by decide
  have hdescent : baseEnd_1769247 < baseStart_1769247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769248 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1769248 : Nat := 118140960795 + 1769248 * 2 ^ 59
def prefixEnd_1769248 : Nat := 4983230072969 + 3 ^ 40 * 1769248 * 2
def baseEnd_1769248 : Nat := 908474621005999042763383

theorem tailTrace_1769248 : CollatzResearch.WordTrace tailWord_1769248 prefixEnd_1769248 908474621005999042763383 := by
  unfold tailWord_1769248
  simp only [CollatzResearch.WordTrace]
  refine ⟨32264887947162067173522199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43019850596216089564696265 32264887947162067173522199)
  ·
    refine ⟨48397331920743100760283299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32264887947162067173522199 48397331920743100760283299)
    ·
      refine ⟨72595997881114651140424949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48397331920743100760283299 72595997881114651140424949)
      ·
        refine ⟨6805874801354498544414839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72595997881114651140424949 6805874801354498544414839)
        ·
          refine ⟨10208812202031747816622259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805874801354498544414839 10208812202031747816622259)
          ·
            refine ⟨15313218303047621724933389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10208812202031747816622259 15313218303047621724933389)
            ·
              refine ⟨5742456863642858146850021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15313218303047621724933389 5742456863642858146850021)
              ·
                refine ⟨1076710661933035902534379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5742456863642858146850021 1076710661933035902534379)
                ·
                  refine ⟨1615065992899553853801569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076710661933035902534379 1615065992899553853801569)
                  ·
                    refine ⟨1211299494674665390351177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615065992899553853801569 1211299494674665390351177)
                    ·
                      refine ⟨908474621005999042763383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211299494674665390351177 908474621005999042763383)
                      ·
                        rfl

theorem cell23_1769248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1769248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769248 prefixEnd_1769248 := by exact prefixLift 1769248
  have htrace : WordTrace (prefixWord ++ tailWord_1769248) baseStart_1769248 baseEnd_1769248 := by
    simpa [prefixWord, tailWord_1769248, baseEnd_1769248] using wordTrace_append hprefix tailTrace_1769248
  have hstable : (prefixWord ++ tailWord_1769248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769248).length < 2 ^ (prefixWord ++ tailWord_1769248).sum := by decide
  have hdescent : baseEnd_1769248 < baseStart_1769248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769257 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 9, 2]
def baseStart_1769257 : Nat := 118140960795 + 1769257 * 2 ^ 59
def prefixEnd_1769257 : Nat := 4983230072969 + 3 ^ 40 * 1769257 * 2
def baseEnd_1769257 : Nat := 908479242331889507550841

theorem tailTrace_1769257 : CollatzResearch.WordTrace tailWord_1769257 prefixEnd_1769257 908479242331889507550841 := by
  unfold tailWord_1769257
  simp only [CollatzResearch.WordTrace]
  refine ⟨64530104151291528884122025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43020069434194352589414683 64530104151291528884122025)
  ·
    refine ⟨48397578113468646663091519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64530104151291528884122025 48397578113468646663091519)
    ·
      refine ⟨72596367170202969994637279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48397578113468646663091519 72596367170202969994637279)
      ·
        refine ⟨108894550755304454991955919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72596367170202969994637279 108894550755304454991955919)
        ·
          refine ⟨163341826132956682487933879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108894550755304454991955919 163341826132956682487933879)
          ·
            refine ⟨245012739199435023731900819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163341826132956682487933879 245012739199435023731900819)
            ·
              refine ⟨367519108799152535597851229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245012739199435023731900819 367519108799152535597851229)
              ·
                refine ⟨137819665799682200849194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367519108799152535597851229 137819665799682200849194211)
                ·
                  refine ⟨206729498699523301273791317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137819665799682200849194211 206729498699523301273791317)
                  ·
                    refine ⟨1211305656442519343401121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206729498699523301273791317 1211305656442519343401121)
                    ·
                      refine ⟨908479242331889507550841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211305656442519343401121 908479242331889507550841)
                      ·
                        rfl

theorem cell23_1769257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9, 2].length) (baseStart_1769257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769257 prefixEnd_1769257 := by exact prefixLift 1769257
  have htrace : WordTrace (prefixWord ++ tailWord_1769257) baseStart_1769257 baseEnd_1769257 := by
    simpa [prefixWord, tailWord_1769257, baseEnd_1769257] using wordTrace_append hprefix tailTrace_1769257
  have hstable : (prefixWord ++ tailWord_1769257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769257).length < 2 ^ (prefixWord ++ tailWord_1769257).sum := by decide
  have hdescent : baseEnd_1769257 < baseStart_1769257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769297 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1769297 : Nat := 118140960795 + 1769297 * 2 ^ 59
def prefixEnd_1769297 : Nat := 4983230072969 + 3 ^ 40 * 1769297 * 2
def baseEnd_1769297 : Nat := 302833260519356450350219

theorem tailTrace_1769297 : CollatzResearch.WordTrace tailWord_1769297 prefixEnd_1769297 302833260519356450350219 := by
  unfold tailWord_1769297
  simp only [CollatzResearch.WordTrace]
  refine ⟨64531563071146615715578145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43021042047431077143718763 64531563071146615715578145)
  ·
    refine ⟨48398672303359961786683609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64531563071146615715578145 48398672303359961786683609)
    ·
      refine ⟨36299004227519971340012707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48398672303359961786683609 36299004227519971340012707)
      ·
        refine ⟨54448506341279957010019061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36299004227519971340012707 54448506341279957010019061)
        ·
          refine ⟨5104547469494995969689287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54448506341279957010019061 5104547469494995969689287)
          ·
            refine ⟨7656821204242493954533931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104547469494995969689287 7656821204242493954533931)
            ·
              refine ⟨11485231806363740931800897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7656821204242493954533931 11485231806363740931800897)
              ·
                refine ⟨8613923854772805698850673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11485231806363740931800897 8613923854772805698850673)
                ·
                  refine ⟨6460442891079604274138005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8613923854772805698850673 6460442891079604274138005)
                  ·
                    refine ⟨302833260519356450350219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6460442891079604274138005 302833260519356450350219)
                    ·
                      rfl

theorem cell23_1769297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1769297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769297 prefixEnd_1769297 := by exact prefixLift 1769297
  have htrace : WordTrace (prefixWord ++ tailWord_1769297) baseStart_1769297 baseEnd_1769297 := by
    simpa [prefixWord, tailWord_1769297, baseEnd_1769297] using wordTrace_append hprefix tailTrace_1769297
  have hstable : (prefixWord ++ tailWord_1769297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769297).length < 2 ^ (prefixWord ++ tailWord_1769297).sum := by decide
  have hdescent : baseEnd_1769297 < baseStart_1769297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769298 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1769298 : Nat := 118140960795 + 1769298 * 2 ^ 59
def prefixEnd_1769298 : Nat := 4983230072969 + 3 ^ 40 * 1769298 * 2
def baseEnd_1769298 : Nat := 908500295038723847138153

theorem tailTrace_1769298 : CollatzResearch.WordTrace tailWord_1769298 prefixEnd_1769298 908500295038723847138153 := by
  unfold tailWord_1769298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132899886035748221591137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43021066362761995257576365 16132899886035748221591137)
  ·
    refine ⟨12099674914526811166193353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16132899886035748221591137 12099674914526811166193353)
    ·
      refine ⟨9074756185895108374645015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12099674914526811166193353 9074756185895108374645015)
      ·
        refine ⟨13612134278842662561967523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074756185895108374645015 13612134278842662561967523)
        ·
          refine ⟨20418201418263993842951285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612134278842662561967523 20418201418263993842951285)
          ·
            refine ⟨1914206382962249422776683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20418201418263993842951285 1914206382962249422776683)
            ·
              refine ⟨2871309574443374134165025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914206382962249422776683 2871309574443374134165025)
              ·
                refine ⟨2153482180832530600623769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871309574443374134165025 2153482180832530600623769)
                ·
                  refine ⟨1615111635624397950467827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153482180832530600623769 1615111635624397950467827)
                  ·
                    refine ⟨2422667453436596925701741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1615111635624397950467827 2422667453436596925701741)
                    ·
                      refine ⟨908500295038723847138153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422667453436596925701741 908500295038723847138153)
                      ·
                        rfl

theorem cell23_1769298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1769298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769298 prefixEnd_1769298 := by exact prefixLift 1769298
  have htrace : WordTrace (prefixWord ++ tailWord_1769298) baseStart_1769298 baseEnd_1769298 := by
    simpa [prefixWord, tailWord_1769298, baseEnd_1769298] using wordTrace_append hprefix tailTrace_1769298
  have hstable : (prefixWord ++ tailWord_1769298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769298).length < 2 ^ (prefixWord ++ tailWord_1769298).sum := by decide
  have hdescent : baseEnd_1769298 < baseStart_1769298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769314 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1769314 : Nat := 118140960795 + 1769314 * 2 ^ 59
def prefixEnd_1769314 : Nat := 4983230072969 + 3 ^ 40 * 1769314 * 2
def baseEnd_1769314 : Nat := 302836170243065261512693

theorem tailTrace_1769314 : CollatzResearch.WordTrace tailWord_1769314 prefixEnd_1769314 302836170243065261512693 := by
  unfold tailWord_1769314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133045778021256904736749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43021455408056685079297997 16133045778021256904736749)
  ·
    refine ⟨6049892166757971339276281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16133045778021256904736749 6049892166757971339276281)
    ·
      refine ⟨4537419125068478504457211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049892166757971339276281 4537419125068478504457211)
      ·
        refine ⟨6806128687602717756685817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537419125068478504457211 6806128687602717756685817)
        ·
          refine ⟨5104596515702038317514363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6806128687602717756685817 5104596515702038317514363)
          ·
            refine ⟨7656894773553057476271545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104596515702038317514363 7656894773553057476271545)
            ·
              refine ⟨5742671080164793107203659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7656894773553057476271545 5742671080164793107203659)
              ·
                refine ⟨8614006620247189660805489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742671080164793107203659 8614006620247189660805489)
                ·
                  refine ⟨6460504965185392245604117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8614006620247189660805489 6460504965185392245604117)
                  ·
                    refine ⟨302836170243065261512693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6460504965185392245604117 302836170243065261512693)
                    ·
                      rfl

theorem cell23_1769314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1769314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769314 prefixEnd_1769314 := by exact prefixLift 1769314
  have htrace : WordTrace (prefixWord ++ tailWord_1769314) baseStart_1769314 baseEnd_1769314 := by
    simpa [prefixWord, tailWord_1769314, baseEnd_1769314] using wordTrace_append hprefix tailTrace_1769314
  have hstable : (prefixWord ++ tailWord_1769314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769314).length < 2 ^ (prefixWord ++ tailWord_1769314).sum := by decide
  have hdescent : baseEnd_1769314 < baseStart_1769314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769321 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 2, 2, 2]
def baseStart_1769321 : Nat := 118140960795 + 1769321 * 2 ^ 59
def prefixEnd_1769321 : Nat := 4983230072969 + 3 ^ 40 * 1769321 * 2
def baseEnd_1769321 : Nat := 908512105093777257150547

theorem tailTrace_1769321 : CollatzResearch.WordTrace tailWord_1769321 prefixEnd_1769321 908512105093777257150547 := by
  unfold tailWord_1769321
  simp only [CollatzResearch.WordTrace]
  refine ⟨64532438423059667814451817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43021625615373111876301211 64532438423059667814451817)
  ·
    refine ⟨48399328817294750860838863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64532438423059667814451817 48399328817294750860838863)
    ·
      refine ⟨72598993225942126291258295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48399328817294750860838863 72598993225942126291258295)
      ·
        refine ⟨108898489838913189436887443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72598993225942126291258295 108898489838913189436887443)
        ·
          refine ⟨163347734758369784155331165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108898489838913189436887443 163347734758369784155331165)
          ·
            refine ⟨61255400534388669058249187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163347734758369784155331165 61255400534388669058249187)
            ·
              refine ⟨91883100801583003587373781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61255400534388669058249187 91883100801583003587373781)
              ·
                refine ⟨2153510175037101646579073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91883100801583003587373781 2153510175037101646579073)
                ·
                  refine ⟨1615132631277826234934305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153510175037101646579073 1615132631277826234934305)
                  ·
                    refine ⟨1211349473458369676200729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615132631277826234934305 1211349473458369676200729)
                    ·
                      refine ⟨908512105093777257150547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211349473458369676200729 908512105093777257150547)
                      ·
                        rfl

theorem cell23_1769321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2, 2].length) (baseStart_1769321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769321 prefixEnd_1769321 := by exact prefixLift 1769321
  have htrace : WordTrace (prefixWord ++ tailWord_1769321) baseStart_1769321 baseEnd_1769321 := by
    simpa [prefixWord, tailWord_1769321, baseEnd_1769321] using wordTrace_append hprefix tailTrace_1769321
  have hstable : (prefixWord ++ tailWord_1769321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769321).length < 2 ^ (prefixWord ++ tailWord_1769321).sum := by decide
  have hdescent : baseEnd_1769321 < baseStart_1769321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769366 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1769366 : Nat := 118140960795 + 1769366 * 2 ^ 59
def prefixEnd_1769366 : Nat := 4983230072969 + 3 ^ 40 * 1769366 * 2
def baseEnd_1769366 : Nat := 908535211723229581087841

theorem tailTrace_1769366 : CollatzResearch.WordTrace tailWord_1769366 prefixEnd_1769366 908535211723229581087841 := by
  unfold tailWord_1769366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033379981743540031239997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43022719805264426999893301 4033379981743540031239997)
  ·
    refine ⟨1512517493153827511714999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4033379981743540031239997 1512517493153827511714999)
    ·
      refine ⟨2268776239730741267572499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512517493153827511714999 2268776239730741267572499)
      ·
        refine ⟨3403164359596111901358749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268776239730741267572499 3403164359596111901358749)
        ·
          refine ⟨1276186634848541963009531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3403164359596111901358749 1276186634848541963009531)
          ·
            refine ⟨1914279952272812944514297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276186634848541963009531 1914279952272812944514297)
            ·
              refine ⟨1435709964204609708385723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914279952272812944514297 1435709964204609708385723)
              ·
                refine ⟨2153564946306914562578585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435709964204609708385723 2153564946306914562578585)
                ·
                  refine ⟨1615173709730185921933939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153564946306914562578585 1615173709730185921933939)
                  ·
                    refine ⟨2422760564595278882900909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1615173709730185921933939 2422760564595278882900909)
                    ·
                      refine ⟨908535211723229581087841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2422760564595278882900909 908535211723229581087841)
                      ·
                        rfl

theorem cell23_1769366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1769366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769366 prefixEnd_1769366 := by exact prefixLift 1769366
  have htrace : WordTrace (prefixWord ++ tailWord_1769366) baseStart_1769366 baseEnd_1769366 := by
    simpa [prefixWord, tailWord_1769366, baseEnd_1769366] using wordTrace_append hprefix tailTrace_1769366
  have hstable : (prefixWord ++ tailWord_1769366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769366).length < 2 ^ (prefixWord ++ tailWord_1769366).sum := by decide
  have hdescent : baseEnd_1769366 < baseStart_1769366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769367 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1769367 : Nat := 118140960795 + 1769367 * 2 ^ 59
def prefixEnd_1769367 : Nat := 4983230072969 + 3 ^ 40 * 1769367 * 2
def baseEnd_1769367 : Nat := 908535725203884077175335

theorem tailTrace_1769367 : CollatzResearch.WordTrace tailWord_1769367 prefixEnd_1769367 908535725203884077175335 := by
  unfold tailWord_1769367
  simp only [CollatzResearch.WordTrace]
  refine ⟨64534116180893017670626355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43022744120595345113750903 64534116180893017670626355)
  ·
    refine ⟨96801174271339526505939533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64534116180893017670626355 96801174271339526505939533)
    ·
      refine ⟨36300440351752322439727325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96801174271339526505939533 36300440351752322439727325)
      ·
        refine ⟨13612665131907120914897747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36300440351752322439727325 13612665131907120914897747)
        ·
          refine ⟨20418997697860681372346621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612665131907120914897747 20418997697860681372346621)
          ·
            refine ⟨7657124136697755514629983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20418997697860681372346621 7657124136697755514629983)
            ·
              refine ⟨11485686205046633271944975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7657124136697755514629983 11485686205046633271944975)
              ·
                refine ⟨17228529307569949907917463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485686205046633271944975 17228529307569949907917463)
                ·
                  refine ⟨25842793961354924861876195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17228529307569949907917463 25842793961354924861876195)
                  ·
                    refine ⟨38764190942032387292814293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25842793961354924861876195 38764190942032387292814293)
                    ·
                      refine ⟨908535725203884077175335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38764190942032387292814293 908535725203884077175335)
                      ·
                        rfl

theorem cell23_1769367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1769367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769367 prefixEnd_1769367 := by exact prefixLift 1769367
  have htrace : WordTrace (prefixWord ++ tailWord_1769367) baseStart_1769367 baseEnd_1769367 := by
    simpa [prefixWord, tailWord_1769367, baseEnd_1769367] using wordTrace_append hprefix tailTrace_1769367
  have hstable : (prefixWord ++ tailWord_1769367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769367).length < 2 ^ (prefixWord ++ tailWord_1769367).sum := by decide
  have hdescent : baseEnd_1769367 < baseStart_1769367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769372 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1769372 : Nat := 118140960795 + 1769372 * 2 ^ 59
def prefixEnd_1769372 : Nat := 4983230072969 + 3 ^ 40 * 1769372 * 2
def baseEnd_1769372 : Nat := 908538292607156557612813

theorem tailTrace_1769372 : CollatzResearch.WordTrace tailWord_1769372 prefixEnd_1769372 908538292607156557612813 := by
  unfold tailWord_1769372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267149272937451762279185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43022865697249935683038913 32267149272937451762279185)
  ·
    refine ⟨24200361954703088821709389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32267149272937451762279185 24200361954703088821709389)
    ·
      refine ⟨9075135733013658308141021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24200361954703088821709389 9075135733013658308141021)
      ·
        refine ⟨3403175899880121865552883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9075135733013658308141021 3403175899880121865552883)
        ·
          refine ⟨5104763849820182798329325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403175899880121865552883 5104763849820182798329325)
          ·
            refine ⟨1914286443682568549373497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5104763849820182798329325 1914286443682568549373497)
            ·
              refine ⟨1435714832761926412030123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914286443682568549373497 1435714832761926412030123)
              ·
                refine ⟨2153572249142889618045185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435714832761926412030123 2153572249142889618045185)
                ·
                  refine ⟨1615179186857167213533889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2153572249142889618045185 1615179186857167213533889)
                  ·
                    refine ⟨1211384390142875410150417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615179186857167213533889 1211384390142875410150417)
                    ·
                      refine ⟨908538292607156557612813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211384390142875410150417 908538292607156557612813)
                      ·
                        rfl

theorem cell23_1769372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1769372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769372 prefixEnd_1769372 := by exact prefixLift 1769372
  have htrace : WordTrace (prefixWord ++ tailWord_1769372) baseStart_1769372 baseEnd_1769372 := by
    simpa [prefixWord, tailWord_1769372, baseEnd_1769372] using wordTrace_append hprefix tailTrace_1769372
  have hstable : (prefixWord ++ tailWord_1769372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769372).length < 2 ^ (prefixWord ++ tailWord_1769372).sum := by decide
  have hdescent : baseEnd_1769372 < baseStart_1769372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769407 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1769407 : Nat := 118140960795 + 1769407 * 2 ^ 59
def prefixEnd_1769407 : Nat := 4983230072969 + 3 ^ 40 * 1769407 * 2
def baseEnd_1769407 : Nat := 908556264430063920675151

theorem tailTrace_1769407 : CollatzResearch.WordTrace tailWord_1769407 prefixEnd_1769407 908556264430063920675151 := by
  unfold tailWord_1769407
  simp only [CollatzResearch.WordTrace]
  refine ⟨64535575100748104502082475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43023716733832069668054983 64535575100748104502082475)
  ·
    refine ⟨96803362651122156753123713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64535575100748104502082475 96803362651122156753123713)
    ·
      refine ⟨72602521988341617564842785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96803362651122156753123713 72602521988341617564842785)
      ·
        refine ⟨54451891491256213173632089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72602521988341617564842785 54451891491256213173632089)
        ·
          refine ⟨40838918618442159880224067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54451891491256213173632089 40838918618442159880224067)
          ·
            refine ⟨61258377927663239820336101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40838918618442159880224067 61258377927663239820336101)
            ·
              refine ⟨11485945861436857466313019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61258377927663239820336101 11485945861436857466313019)
              ·
                refine ⟨17228918792155286199469529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485945861436857466313019 17228918792155286199469529)
                ·
                  refine ⟨12921689094116464649602147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17228918792155286199469529 12921689094116464649602147)
                  ·
                    refine ⟨19382533641174696974403221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12921689094116464649602147 19382533641174696974403221)
                    ·
                      refine ⟨908556264430063920675151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19382533641174696974403221 908556264430063920675151)
                      ·
                        rfl

theorem cell23_1769407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1769407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769407 prefixEnd_1769407 := by exact prefixLift 1769407
  have htrace : WordTrace (prefixWord ++ tailWord_1769407) baseStart_1769407 baseEnd_1769407 := by
    simpa [prefixWord, tailWord_1769407, baseEnd_1769407] using wordTrace_append hprefix tailTrace_1769407
  have hstable : (prefixWord ++ tailWord_1769407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769407).length < 2 ^ (prefixWord ++ tailWord_1769407).sum := by decide
  have hdescent : baseEnd_1769407 < baseStart_1769407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769471 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 2, 3, 2]
def baseStart_1769471 : Nat := 118140960795 + 1769471 * 2 ^ 59
def prefixEnd_1769471 : Nat := 4983230072969 + 3 ^ 40 * 1769471 * 2
def baseEnd_1769471 : Nat := 908589127191951670274857

theorem tailTrace_1769471 : CollatzResearch.WordTrace tailWord_1769471 prefixEnd_1769471 908589127191951670274857 := by
  unfold tailWord_1769471
  simp only [CollatzResearch.WordTrace]
  refine ⟨64537909372516243432412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43025272915010828954941511 64537909372516243432412267)
  ·
    refine ⟨96806864058774365148618401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64537909372516243432412267 96806864058774365148618401)
    ·
      refine ⟨72605148044080773861463801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96806864058774365148618401 72605148044080773861463801)
      ·
        refine ⟨54453861033060580396097851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72605148044080773861463801 54453861033060580396097851)
        ·
          refine ⟨81680791549590870594146777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54453861033060580396097851 81680791549590870594146777)
          ·
            refine ⟨61260593662193152945610083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81680791549590870594146777 61260593662193152945610083)
            ·
              refine ⟨91890890493289729418415125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61260593662193152945610083 91890890493289729418415125)
              ·
                refine ⟨4307385491872956066488209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91890890493289729418415125 4307385491872956066488209)
                ·
                  refine ⟨3230539118904717049866157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307385491872956066488209 3230539118904717049866157)
                  ·
                    refine ⟨1211452169589268893699809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230539118904717049866157 1211452169589268893699809)
                    ·
                      refine ⟨908589127191951670274857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211452169589268893699809 908589127191951670274857)
                      ·
                        rfl

theorem cell23_1769471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_1769471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769471 prefixEnd_1769471 := by exact prefixLift 1769471
  have htrace : WordTrace (prefixWord ++ tailWord_1769471) baseStart_1769471 baseEnd_1769471 := by
    simpa [prefixWord, tailWord_1769471, baseEnd_1769471] using wordTrace_append hprefix tailTrace_1769471
  have hstable : (prefixWord ++ tailWord_1769471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769471).length < 2 ^ (prefixWord ++ tailWord_1769471).sum := by decide
  have hdescent : baseEnd_1769471 < baseStart_1769471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769518 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1769518 : Nat := 118140960795 + 1769518 * 2 ^ 59
def prefixEnd_1769518 : Nat := 4983230072969 + 3 ^ 40 * 1769518 * 2
def baseEnd_1769518 : Nat := 908613260782712986387141

theorem tailTrace_1769518 : CollatzResearch.WordTrace tailWord_1769518 prefixEnd_1769518 908613260782712986387141 := by
  unfold tailWord_1769518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067452950418246307421651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43026415735563980306248805 8067452950418246307421651)
  ·
    refine ⟨12101179425627369461132477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067452950418246307421651 12101179425627369461132477)
    ·
      refine ⟨4537942284610263547924679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12101179425627369461132477 4537942284610263547924679)
      ·
        refine ⟨6806913426915395321887019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537942284610263547924679 6806913426915395321887019)
        ·
          refine ⟨10210370140373092982830529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806913426915395321887019 10210370140373092982830529)
          ·
            refine ⟨7657777605279819737122897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10210370140373092982830529 7657777605279819737122897)
            ·
              refine ⟨5743333203959864802842173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657777605279819737122897 5743333203959864802842173)
              ·
                refine ⟨2153749951484949301065815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5743333203959864802842173 2153749951484949301065815)
                ·
                  refine ⟨3230624927227423951598723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153749951484949301065815 3230624927227423951598723)
                  ·
                    refine ⟨4845937390841135927398085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3230624927227423951598723 4845937390841135927398085)
                    ·
                      refine ⟨908613260782712986387141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4845937390841135927398085 908613260782712986387141)
                      ·
                        rfl

theorem cell23_1769518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1769518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769518 prefixEnd_1769518 := by exact prefixLift 1769518
  have htrace : WordTrace (prefixWord ++ tailWord_1769518) baseStart_1769518 baseEnd_1769518 := by
    simpa [prefixWord, tailWord_1769518, baseEnd_1769518] using wordTrace_append hprefix tailTrace_1769518
  have hstable : (prefixWord ++ tailWord_1769518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769518).length < 2 ^ (prefixWord ++ tailWord_1769518).sum := by decide
  have hdescent : baseEnd_1769518 < baseStart_1769518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769521 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1769521 : Nat := 118140960795 + 1769521 * 2 ^ 59
def prefixEnd_1769521 : Nat := 4983230072969 + 3 ^ 40 * 1769521 * 2
def baseEnd_1769521 : Nat := 908614801224676474649627

theorem tailTrace_1769521 : CollatzResearch.WordTrace tailWord_1769521 prefixEnd_1769521 908614801224676474649627 := by
  unfold tailWord_1769521
  simp only [CollatzResearch.WordTrace]
  refine ⟨64539733022335101971732417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43026488681556734647821611 64539733022335101971732417)
  ·
    refine ⟨48404799766751326478799313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64539733022335101971732417 48404799766751326478799313)
    ·
      refine ⟨36303599825063494859099485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48404799766751326478799313 36303599825063494859099485)
      ·
        refine ⟨13613849934398810572162307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36303599825063494859099485 13613849934398810572162307)
        ·
          refine ⟨20420774901598215858243461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13613849934398810572162307 20420774901598215858243461)
          ·
            refine ⟨3828895294049665473420649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20420774901598215858243461 3828895294049665473420649)
            ·
              refine ⟨2871671470537249105065487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828895294049665473420649 2871671470537249105065487)
              ·
                refine ⟨4307507205805873657598231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871671470537249105065487 4307507205805873657598231)
                ·
                  refine ⟨6461260808708810486397347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307507205805873657598231 6461260808708810486397347)
                  ·
                    refine ⟨9691891213063215729596021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6461260808708810486397347 9691891213063215729596021)
                    ·
                      refine ⟨908614801224676474649627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9691891213063215729596021 908614801224676474649627)
                      ·
                        rfl

theorem cell23_1769521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1769521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769521 prefixEnd_1769521 := by exact prefixLift 1769521
  have htrace : WordTrace (prefixWord ++ tailWord_1769521) baseStart_1769521 baseEnd_1769521 := by
    simpa [prefixWord, tailWord_1769521, baseEnd_1769521] using wordTrace_append hprefix tailTrace_1769521
  have hstable : (prefixWord ++ tailWord_1769521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769521).length < 2 ^ (prefixWord ++ tailWord_1769521).sum := by decide
  have hdescent : baseEnd_1769521 < baseStart_1769521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769535 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 1, 2, 2]
def baseStart_1769535 : Nat := 118140960795 + 1769535 * 2 ^ 59
def prefixEnd_1769535 : Nat := 4983230072969 + 3 ^ 40 * 1769535 * 2
def baseEnd_1769535 : Nat := 908621989953839419874563

theorem tailTrace_1769535 : CollatzResearch.WordTrace tailWord_1769535 prefixEnd_1769535 908621989953839419874563 := by
  unfold tailWord_1769535
  simp only [CollatzResearch.WordTrace]
  refine ⟨64540243644284382362742059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43026829096189588241828039 64540243644284382362742059)
  ·
    refine ⟨96810365466426573544113089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64540243644284382362742059 96810365466426573544113089)
    ·
      refine ⟨72607774099819930158084817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96810365466426573544113089 72607774099819930158084817)
      ·
        refine ⟨54455830574864947618563613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72607774099819930158084817 54455830574864947618563613)
        ·
          refine ⟨20420936465574355356961355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54455830574864947618563613 20420936465574355356961355)
          ·
            refine ⟨30631404698361533035442033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20420936465574355356961355 30631404698361533035442033)
            ·
              refine ⟨22973553523771149776581525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30631404698361533035442033 22973553523771149776581525)
              ·
                refine ⟨1076885321426772645777259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22973553523771149776581525 1076885321426772645777259)
                ·
                  refine ⟨1615327982140158968665889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076885321426772645777259 1615327982140158968665889)
                  ·
                    refine ⟨1211495986605119226499417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615327982140158968665889 1211495986605119226499417)
                    ·
                      refine ⟨908621989953839419874563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211495986605119226499417 908621989953839419874563)
                      ·
                        rfl

theorem cell23_1769535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_1769535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769535 prefixEnd_1769535 := by exact prefixLift 1769535
  have htrace : WordTrace (prefixWord ++ tailWord_1769535) baseStart_1769535 baseEnd_1769535 := by
    simpa [prefixWord, tailWord_1769535, baseEnd_1769535] using wordTrace_append hprefix tailTrace_1769535
  have hstable : (prefixWord ++ tailWord_1769535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769535).length < 2 ^ (prefixWord ++ tailWord_1769535).sum := by decide
  have hdescent : baseEnd_1769535 < baseStart_1769535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769558 : List Nat := [5, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1769558 : Nat := 118140960795 + 1769558 * 2 ^ 59
def prefixEnd_1769558 : Nat := 4983230072969 + 3 ^ 40 * 1769558 * 2
def baseEnd_1769558 : Nat := 33653103704033067773591

theorem tailTrace_1769558 : CollatzResearch.WordTrace tailWord_1769558 prefixEnd_1769558 33653103704033067773591 := by
  unfold tailWord_1769558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033817657700066080676833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43027388348800704860552885 4033817657700066080676833)
  ·
    refine ⟨3025363243275049560507625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4033817657700066080676833 3025363243275049560507625)
    ·
      refine ⟨2269022432456287170380719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025363243275049560507625 2269022432456287170380719)
      ·
        refine ⟨3403533648684430755571079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269022432456287170380719 3403533648684430755571079)
        ·
          refine ⟨5105300473026646133356619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403533648684430755571079 5105300473026646133356619)
          ·
            refine ⟨7657950709539969200034929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105300473026646133356619 7657950709539969200034929)
            ·
              refine ⟨5743463032154976900026197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657950709539969200034929 5743463032154976900026197)
              ·
                refine ⟨33653103704033067773591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5743463032154976900026197 33653103704033067773591)
                ·
                  rfl

theorem cell23_1769558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1769558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769558 prefixEnd_1769558 := by exact prefixLift 1769558
  have htrace : WordTrace (prefixWord ++ tailWord_1769558) baseStart_1769558 baseEnd_1769558 := by
    simpa [prefixWord, tailWord_1769558, baseEnd_1769558] using wordTrace_append hprefix tailTrace_1769558
  have hstable : (prefixWord ++ tailWord_1769558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769558).length < 2 ^ (prefixWord ++ tailWord_1769558).sum := by decide
  have hdescent : baseEnd_1769558 < baseStart_1769558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769681 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1769681 : Nat := 118140960795 + 1769681 * 2 ^ 59
def prefixEnd_1769681 : Nat := 4983230072969 + 3 ^ 40 * 1769681 * 2
def baseEnd_1769681 : Nat := 908696958129395848648891

theorem tailTrace_1769681 : CollatzResearch.WordTrace tailWord_1769681 prefixEnd_1769681 908696958129395848648891 := by
  unfold tailWord_1769681
  simp only [CollatzResearch.WordTrace]
  refine ⟨64545568701755449297556897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43030379134503632865037931 64545568701755449297556897)
  ·
    refine ⟨48409176526316586973167673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64545568701755449297556897 48409176526316586973167673)
    ·
      refine ⟨36306882394737440229875755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48409176526316586973167673 36306882394737440229875755)
      ·
        refine ⟨54460323592106160344813633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36306882394737440229875755 54460323592106160344813633)
        ·
          refine ⟨40845242694079620258610225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54460323592106160344813633 40845242694079620258610225)
          ·
            refine ⟨30633932020559715193957669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40845242694079620258610225 30633932020559715193957669)
            ·
              refine ⟨5743862253854946598867063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30633932020559715193957669 5743862253854946598867063)
              ·
                refine ⟨8615793380782419898300595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743862253854946598867063 8615793380782419898300595)
                ·
                  refine ⟨12923690071173629847450893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8615793380782419898300595 12923690071173629847450893)
                  ·
                    refine ⟨4846383776690111192794085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12923690071173629847450893 4846383776690111192794085)
                    ·
                      refine ⟨908696958129395848648891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4846383776690111192794085 908696958129395848648891)
                      ·
                        rfl

theorem cell23_1769681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1769681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769681 prefixEnd_1769681 := by exact prefixLift 1769681
  have htrace : WordTrace (prefixWord ++ tailWord_1769681) baseStart_1769681 baseEnd_1769681 := by
    simpa [prefixWord, tailWord_1769681, baseEnd_1769681] using wordTrace_append hprefix tailTrace_1769681
  have hstable : (prefixWord ++ tailWord_1769681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769681).length < 2 ^ (prefixWord ++ tailWord_1769681).sum := by decide
  have hdescent : baseEnd_1769681 < baseStart_1769681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769691 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 7, 4]
def baseStart_1769691 : Nat := 118140960795 + 1769691 * 2 ^ 59
def prefixEnd_1769691 : Nat := 4983230072969 + 3 ^ 40 * 1769691 * 2
def baseEnd_1769691 : Nat := 302900697645313603174615

theorem tailTrace_1769691 : CollatzResearch.WordTrace tailWord_1769691 prefixEnd_1769691 302900697645313603174615 := by
  unfold tailWord_1769691
  simp only [CollatzResearch.WordTrace]
  refine ⟨64545933431719221005420927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43030622287812814003613951 64545933431719221005420927)
  ·
    refine ⟨96818900147578831508131391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64545933431719221005420927 96818900147578831508131391)
    ·
      refine ⟨145228350221368247262197087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96818900147578831508131391 145228350221368247262197087)
      ·
        refine ⟨217842525332052370893295631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145228350221368247262197087 217842525332052370893295631)
        ·
          refine ⟨326763787998078556339943447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217842525332052370893295631 326763787998078556339943447)
          ·
            refine ⟨490145681997117834509915171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326763787998078556339943447 490145681997117834509915171)
            ·
              refine ⟨735218522995676751764872757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490145681997117834509915171 735218522995676751764872757)
              ·
                refine ⟨68926736530844695477956821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 735218522995676751764872757 68926736530844695477956821)
                ·
                  refine ⟨1615470387441672550264613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 68926736530844695477956821 1615470387441672550264613)
                  ·
                    refine ⟨302900697645313603174615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615470387441672550264613 302900697645313603174615)
                    ·
                      rfl

theorem cell23_1769691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 4].length) (baseStart_1769691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769691 prefixEnd_1769691 := by exact prefixLift 1769691
  have htrace : WordTrace (prefixWord ++ tailWord_1769691) baseStart_1769691 baseEnd_1769691 := by
    simpa [prefixWord, tailWord_1769691, baseEnd_1769691] using wordTrace_append hprefix tailTrace_1769691
  have hstable : (prefixWord ++ tailWord_1769691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769691).length < 2 ^ (prefixWord ++ tailWord_1769691).sum := by decide
  have hdescent : baseEnd_1769691 < baseStart_1769691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769718 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1769718 : Nat := 118140960795 + 1769718 * 2 ^ 59
def prefixEnd_1769718 : Nat := 4983230072969 + 3 ^ 40 * 1769718 * 2
def baseEnd_1769718 : Nat := 908715956913612203886221

theorem tailTrace_1769718 : CollatzResearch.WordTrace tailWord_1769718 prefixEnd_1769718 908715956913612203886221 := by
  unfold tailWord_1769718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034182387663837788540863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43031278801747603077769205 4034182387663837788540863)
  ·
    refine ⟨6051273581495756682811295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4034182387663837788540863 6051273581495756682811295)
    ·
      refine ⟨9076910372243635024216943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051273581495756682811295 9076910372243635024216943)
      ·
        refine ⟨13615365558365452536325415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076910372243635024216943 13615365558365452536325415)
        ·
          refine ⟨20423048337548178804488123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615365558365452536325415 20423048337548178804488123)
          ·
            refine ⟨30634572506322268206732185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423048337548178804488123 30634572506322268206732185)
            ·
              refine ⟨22975929379741701155049139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30634572506322268206732185 22975929379741701155049139)
              ·
                refine ⟨34463894069612551732573709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22975929379741701155049139 34463894069612551732573709)
                ·
                  refine ⟨12923960276104706899715141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34463894069612551732573709 12923960276104706899715141)
                  ·
                    refine ⟨2423242551769632543696589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12923960276104706899715141 2423242551769632543696589)
                    ·
                      refine ⟨908715956913612203886221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423242551769632543696589 908715956913612203886221)
                      ·
                        rfl

theorem cell23_1769718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1769718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769718 prefixEnd_1769718 := by exact prefixLift 1769718
  have htrace : WordTrace (prefixWord ++ tailWord_1769718) baseStart_1769718 baseEnd_1769718 := by
    simpa [prefixWord, tailWord_1769718, baseEnd_1769718] using wordTrace_append hprefix tailTrace_1769718
  have hstable : (prefixWord ++ tailWord_1769718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769718).length < 2 ^ (prefixWord ++ tailWord_1769718).sum := by decide
  have hdescent : baseEnd_1769718 < baseStart_1769718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769759 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 1, 4]
def baseStart_1769759 : Nat := 118140960795 + 1769759 * 2 ^ 59
def prefixEnd_1769759 : Nat := 4983230072969 + 3 ^ 40 * 1769759 * 2
def baseEnd_1769759 : Nat := 302912336540148847824511

theorem tailTrace_1769759 : CollatzResearch.WordTrace tailWord_1769759 prefixEnd_1769759 302912336540148847824511 := by
  unfold tailWord_1769759
  simp only [CollatzResearch.WordTrace]
  refine ⟨64548413595472868618896331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43032275730315245745930887 64548413595472868618896331)
  ·
    refine ⟨96822620393209302928344497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64548413595472868618896331 96822620393209302928344497)
    ·
      refine ⟨72616965294906977196258373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96822620393209302928344497 72616965294906977196258373)
      ·
        refine ⟨13615680992795058224298445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72616965294906977196258373 13615680992795058224298445)
        ·
          refine ⟨5105880372298146834111917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13615680992795058224298445 5105880372298146834111917)
          ·
            refine ⟨1914705139611805062791969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5105880372298146834111917 1914705139611805062791969)
            ·
              refine ⟨1436028854708853797093977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914705139611805062791969 1436028854708853797093977)
              ·
                refine ⟨1077021641031640347820483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436028854708853797093977 1077021641031640347820483)
                ·
                  refine ⟨1615532461547460521730725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077021641031640347820483 1615532461547460521730725)
                  ·
                    refine ⟨302912336540148847824511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615532461547460521730725 302912336540148847824511)
                    ·
                      rfl

theorem cell23_1769759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_1769759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769759 prefixEnd_1769759 := by exact prefixLift 1769759
  have htrace : WordTrace (prefixWord ++ tailWord_1769759) baseStart_1769759 baseEnd_1769759 := by
    simpa [prefixWord, tailWord_1769759, baseEnd_1769759] using wordTrace_append hprefix tailTrace_1769759
  have hstable : (prefixWord ++ tailWord_1769759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769759).length < 2 ^ (prefixWord ++ tailWord_1769759).sum := by decide
  have hdescent : baseEnd_1769759 < baseStart_1769759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769788 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1769788 : Nat := 118140960795 + 1769788 * 2 ^ 59
def prefixEnd_1769788 : Nat := 4983230072969 + 3 ^ 40 * 1769788 * 2
def baseEnd_1769788 : Nat := 908751900559426930010899

theorem tailTrace_1769788 : CollatzResearch.WordTrace tailWord_1769788 prefixEnd_1769788 908751900559426930010899 := by
  unfold tailWord_1769788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274735656183903285851009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43032980874911871047801345 32274735656183903285851009)
  ·
    refine ⟨24206051742137927464388257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32274735656183903285851009 24206051742137927464388257)
    ·
      refine ⟨18154538806603445598291193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24206051742137927464388257 18154538806603445598291193)
      ·
        refine ⟨13615904104952584198718395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18154538806603445598291193 13615904104952584198718395)
        ·
          refine ⟨20423856157428876298077593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13615904104952584198718395 20423856157428876298077593)
          ·
            refine ⟨15317892118071657223558195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20423856157428876298077593 15317892118071657223558195)
            ·
              refine ⟨22976838177107485835337293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15317892118071657223558195 22976838177107485835337293)
              ·
                refine ⟨8616314316415307188251485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22976838177107485835337293 8616314316415307188251485)
                ·
                  refine ⟨3231117868655740195594307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8616314316415307188251485 3231117868655740195594307)
                  ·
                    refine ⟨4846676802983610293391461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231117868655740195594307 4846676802983610293391461)
                    ·
                      refine ⟨908751900559426930010899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4846676802983610293391461 908751900559426930010899)
                      ·
                        rfl

theorem cell23_1769788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1769788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769788 prefixEnd_1769788 := by exact prefixLift 1769788
  have htrace : WordTrace (prefixWord ++ tailWord_1769788) baseStart_1769788 baseEnd_1769788 := by
    simpa [prefixWord, tailWord_1769788, baseEnd_1769788] using wordTrace_append hprefix tailTrace_1769788
  have hstable : (prefixWord ++ tailWord_1769788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769788).length < 2 ^ (prefixWord ++ tailWord_1769788).sum := by decide
  have hdescent : baseEnd_1769788 < baseStart_1769788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769801 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1769801 : Nat := 118140960795 + 1769801 * 2 ^ 59
def prefixEnd_1769801 : Nat := 4983230072969 + 3 ^ 40 * 1769801 * 2
def baseEnd_1769801 : Nat := 908758575807935379148339

theorem tailTrace_1769801 : CollatzResearch.WordTrace tailWord_1769801 prefixEnd_1769801 908758575807935379148339 := by
  unfold tailWord_1769801
  simp only [CollatzResearch.WordTrace]
  refine ⟨64549945461320709791925257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43033296974213806527950171 64549945461320709791925257)
  ·
    refine ⟨48412459095990532343943943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64549945461320709791925257 48412459095990532343943943)
    ·
      refine ⟨72618688643985798515915915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48412459095990532343943943 72618688643985798515915915)
      ·
        refine ⟨108928032965978697773873873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72618688643985798515915915 108928032965978697773873873)
        ·
          refine ⟨81696024724484023330405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108928032965978697773873873 81696024724484023330405405)
          ·
            refine ⟨30636009271681508748902027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81696024724484023330405405 30636009271681508748902027)
            ·
              refine ⟨45954013907522263123353041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30636009271681508748902027 45954013907522263123353041)
              ·
                refine ⟨34465510430641697342514781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45954013907522263123353041 34465510430641697342514781)
                ·
                  refine ⟨12924566411490636503443043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34465510430641697342514781 12924566411490636503443043)
                  ·
                    refine ⟨19386849617235954755164565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12924566411490636503443043 19386849617235954755164565)
                    ·
                      refine ⟨908758575807935379148339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19386849617235954755164565 908758575807935379148339)
                      ·
                        rfl

theorem cell23_1769801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1769801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769801 prefixEnd_1769801 := by exact prefixLift 1769801
  have htrace : WordTrace (prefixWord ++ tailWord_1769801) baseStart_1769801 baseEnd_1769801 := by
    simpa [prefixWord, tailWord_1769801, baseEnd_1769801] using wordTrace_append hprefix tailTrace_1769801
  have hstable : (prefixWord ++ tailWord_1769801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769801).length < 2 ^ (prefixWord ++ tailWord_1769801).sum := by decide
  have hdescent : baseEnd_1769801 < baseStart_1769801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769842 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1769842 : Nat := 118140960795 + 1769842 * 2 ^ 59
def prefixEnd_1769842 : Nat := 4983230072969 + 3 ^ 40 * 1769842 * 2
def baseEnd_1769842 : Nat := 908779628514769718735651

theorem tailTrace_1769842 : CollatzResearch.WordTrace tailWord_1769842 prefixEnd_1769842 908779628514769718735651 := by
  unfold tailWord_1769842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137860213543043448541945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43034293902781449196111853 16137860213543043448541945)
  ·
    refine ⟨12103395160157282586406459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16137860213543043448541945 12103395160157282586406459)
    ·
      refine ⟨18155092740235923879609689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103395160157282586406459 18155092740235923879609689)
      ·
        refine ⟨13616319555176942909707267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18155092740235923879609689 13616319555176942909707267)
        ·
          refine ⟨20424479332765414364560901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616319555176942909707267 20424479332765414364560901)
          ·
            refine ⟨3829589874893515193355169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20424479332765414364560901 3829589874893515193355169)
            ·
              refine ⟨2872192406170136395016377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829589874893515193355169 2872192406170136395016377)
              ·
                refine ⟨2154144304627602296262283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872192406170136395016377 2154144304627602296262283)
                ·
                  refine ⟨3231216456941403444393425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154144304627602296262283 3231216456941403444393425)
                  ·
                    refine ⟨2423412342706052583295069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231216456941403444393425 2423412342706052583295069)
                    ·
                      refine ⟨908779628514769718735651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423412342706052583295069 908779628514769718735651)
                      ·
                        rfl

theorem cell23_1769842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1769842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769842 prefixEnd_1769842 := by exact prefixLift 1769842
  have htrace : WordTrace (prefixWord ++ tailWord_1769842) baseStart_1769842 baseEnd_1769842 := by
    simpa [prefixWord, tailWord_1769842, baseEnd_1769842] using wordTrace_append hprefix tailTrace_1769842
  have hstable : (prefixWord ++ tailWord_1769842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769842).length < 2 ^ (prefixWord ++ tailWord_1769842).sum := by decide
  have hdescent : baseEnd_1769842 < baseStart_1769842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769845 : List Nat := [1, 3, 4, 1, 2, 1, 4, 7]
def baseStart_1769845 : Nat := 118140960795 + 1769845 * 2 ^ 59
def prefixEnd_1769845 : Nat := 4983230072969 + 3 ^ 40 * 1769845 * 2
def baseEnd_1769845 : Nat := 33658561813212340999931

theorem tailTrace_1769845 : CollatzResearch.WordTrace tailWord_1769845 prefixEnd_1769845 33658561813212340999931 := by
  unfold tailWord_1769845
  simp only [CollatzResearch.WordTrace]
  refine ⟨64551550273161305306526989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43034366848774203537684659 64551550273161305306526989)
  ·
    refine ⟨24206831352435489489947621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64551550273161305306526989 24206831352435489489947621)
    ·
      refine ⟨4538780878581654279365179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24206831352435489489947621 4538780878581654279365179)
      ·
        refine ⟨6808171317872481419047769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538780878581654279365179 6808171317872481419047769)
        ·
          refine ⟨5106128488404361064285827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6808171317872481419047769 5106128488404361064285827)
          ·
            refine ⟨7659192732606541596428741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106128488404361064285827 7659192732606541596428741)
            ·
              refine ⟨1436098637363726549330389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7659192732606541596428741 1436098637363726549330389)
              ·
                refine ⟨33658561813212340999931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1436098637363726549330389 33658561813212340999931)
                ·
                  rfl

theorem cell23_1769845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 7].length) (baseStart_1769845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769845 prefixEnd_1769845 := by exact prefixLift 1769845
  have htrace : WordTrace (prefixWord ++ tailWord_1769845) baseStart_1769845 baseEnd_1769845 := by
    simpa [prefixWord, tailWord_1769845, baseEnd_1769845] using wordTrace_append hprefix tailTrace_1769845
  have hstable : (prefixWord ++ tailWord_1769845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769845).length < 2 ^ (prefixWord ++ tailWord_1769845).sum := by decide
  have hdescent : baseEnd_1769845 < baseStart_1769845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769916 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1769916 : Nat := 118140960795 + 1769916 * 2 ^ 59
def prefixEnd_1769916 : Nat := 4983230072969 + 3 ^ 40 * 1769916 * 2
def baseEnd_1769916 : Nat := 908817626083202429210311

theorem tailTrace_1769916 : CollatzResearch.WordTrace tailWord_1769916 prefixEnd_1769916 908817626083202429210311 := by
  unfold tailWord_1769916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277069927952042216180801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43036093237269389621574401 32277069927952042216180801)
  ·
    refine ⟨24207802445964031662135601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32277069927952042216180801 24207802445964031662135601)
    ·
      refine ⟨18155851834473023746601701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24207802445964031662135601 18155851834473023746601701)
      ·
        refine ⟨3404222218963691952487819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18155851834473023746601701 3404222218963691952487819)
        ·
          refine ⟨5106333328445537928731729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404222218963691952487819 5106333328445537928731729)
          ·
            refine ⟨3829749996334153446548797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106333328445537928731729 3829749996334153446548797)
            ·
              refine ⟨1436156248625307542455799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3829749996334153446548797 1436156248625307542455799)
              ·
                refine ⟨2154234372937961313683699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436156248625307542455799 2154234372937961313683699)
                ·
                  refine ⟨3231351559406941970525549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154234372937961313683699 3231351559406941970525549)
                  ·
                    refine ⟨1211756834777603238947081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231351559406941970525549 1211756834777603238947081)
                    ·
                      refine ⟨908817626083202429210311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211756834777603238947081 908817626083202429210311)
                      ·
                        rfl

theorem cell23_1769916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1769916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769916 prefixEnd_1769916 := by exact prefixLift 1769916
  have htrace : WordTrace (prefixWord ++ tailWord_1769916) baseStart_1769916 baseEnd_1769916 := by
    simpa [prefixWord, tailWord_1769916, baseEnd_1769916] using wordTrace_append hprefix tailTrace_1769916
  have hstable : (prefixWord ++ tailWord_1769916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769916).length < 2 ^ (prefixWord ++ tailWord_1769916).sum := by decide
  have hdescent : baseEnd_1769916 < baseStart_1769916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769942 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1769942 : Nat := 118140960795 + 1769942 * 2 ^ 59
def prefixEnd_1769942 : Nat := 4983230072969 + 3 ^ 40 * 1769942 * 2
def baseEnd_1769942 : Nat := 908830976580219327485191

theorem tailTrace_1769942 : CollatzResearch.WordTrace tailWord_1769942 prefixEnd_1769942 908830976580219327485191 := by
  unfold tailWord_1769942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034693009613118179550505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43036725435873260581872053 4034693009613118179550505)
  ·
    refine ⟨3026019757209838634662879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4034693009613118179550505 3026019757209838634662879)
    ·
      refine ⟨4539029635814757951994319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026019757209838634662879 4539029635814757951994319)
      ·
        refine ⟨6808544453722136927991479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539029635814757951994319 6808544453722136927991479)
        ·
          refine ⟨10212816680583205391987219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808544453722136927991479 10212816680583205391987219)
          ·
            refine ⟨15319225020874808087980829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212816680583205391987219 15319225020874808087980829)
            ·
              refine ⟨5744709382828053032992811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15319225020874808087980829 5744709382828053032992811)
              ·
                refine ⟨8617064074242079549489217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744709382828053032992811 8617064074242079549489217)
                ·
                  refine ⟨6462798055681559662116913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8617064074242079549489217 6462798055681559662116913)
                  ·
                    refine ⟨4847098541761169746587685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6462798055681559662116913 4847098541761169746587685)
                    ·
                      refine ⟨908830976580219327485191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4847098541761169746587685 908830976580219327485191)
                      ·
                        rfl

theorem cell23_1769942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1769942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769942 prefixEnd_1769942 := by exact prefixLift 1769942
  have htrace : WordTrace (prefixWord ++ tailWord_1769942) baseStart_1769942 baseEnd_1769942 := by
    simpa [prefixWord, tailWord_1769942, baseEnd_1769942] using wordTrace_append hprefix tailTrace_1769942
  have hstable : (prefixWord ++ tailWord_1769942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769942).length < 2 ^ (prefixWord ++ tailWord_1769942).sum := by decide
  have hdescent : baseEnd_1769942 < baseStart_1769942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1769945 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1769945 : Nat := 118140960795 + 1769945 * 2 ^ 59
def prefixEnd_1769945 : Nat := 4983230072969 + 3 ^ 40 * 1769945 * 2
def baseEnd_1769945 : Nat := 908832517022182815747677

theorem tailTrace_1769945 : CollatzResearch.WordTrace tailWord_1769945 prefixEnd_1769945 908832517022182815747677 := by
  unfold tailWord_1769945
  simp only [CollatzResearch.WordTrace]
  refine ⟨64555197572799022385167289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43036798381866014923444859 64555197572799022385167289)
  ·
    refine ⟨48416398179599266788875467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64555197572799022385167289 48416398179599266788875467)
    ·
      refine ⟨72624597269398900183313201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48416398179599266788875467 72624597269398900183313201)
      ·
        refine ⟨54468447952049175137484901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72624597269398900183313201 54468447952049175137484901)
        ·
          refine ⟨10212833991009220338278419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54468447952049175137484901 10212833991009220338278419)
          ·
            refine ⟨15319250986513830507417629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212833991009220338278419 15319250986513830507417629)
            ·
              refine ⟨5744719119942686440281611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15319250986513830507417629 5744719119942686440281611)
              ·
                refine ⟨8617078679914029660422417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744719119942686440281611 8617078679914029660422417)
                ·
                  refine ⟨6462809009935522245316813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8617078679914029660422417 6462809009935522245316813)
                  ·
                    refine ⟨2423553378725820841993805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6462809009935522245316813 2423553378725820841993805)
                    ·
                      refine ⟨908832517022182815747677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423553378725820841993805 908832517022182815747677)
                      ·
                        rfl

theorem cell23_1769945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1769945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1769945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1769945 prefixEnd_1769945 := by exact prefixLift 1769945
  have htrace : WordTrace (prefixWord ++ tailWord_1769945) baseStart_1769945 baseEnd_1769945 := by
    simpa [prefixWord, tailWord_1769945, baseEnd_1769945] using wordTrace_append hprefix tailTrace_1769945
  have hstable : (prefixWord ++ tailWord_1769945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1769945).length < 2 ^ (prefixWord ++ tailWord_1769945).sum := by decide
  have hdescent : baseEnd_1769945 < baseStart_1769945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1769945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770005 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1770005 : Nat := 118140960795 + 1770005 * 2 ^ 59
def prefixEnd_1770005 : Nat := 4983230072969 + 3 ^ 40 * 1770005 * 2
def baseEnd_1770005 : Nat := 908863325861452580997401

theorem tailTrace_1770005 : CollatzResearch.WordTrace tailWord_1770005 prefixEnd_1770005 908863325861452580997401 := by
  unfold tailWord_1770005
  simp only [CollatzResearch.WordTrace]
  refine ⟨64557385952581652632351469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43038257301721101754900979 64557385952581652632351469)
  ·
    refine ⟨24209019732218119737131801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64557385952581652632351469 24209019732218119737131801)
    ·
      refine ⟨18156764799163589802848851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24209019732218119737131801 18156764799163589802848851)
      ·
        refine ⟨27235147198745384704273277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18156764799163589802848851 27235147198745384704273277)
        ·
          refine ⟨10213180199529519264102479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27235147198745384704273277 10213180199529519264102479)
          ·
            refine ⟨15319770299294278896153719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213180199529519264102479 15319770299294278896153719)
            ·
              refine ⟨22979655448941418344230579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15319770299294278896153719 22979655448941418344230579)
              ·
                refine ⟨34469483173412127516345869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22979655448941418344230579 34469483173412127516345869)
                ·
                  refine ⟨12926056190029547818629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34469483173412127516345869 12926056190029547818629701)
                  ·
                    refine ⟨2423635535630540215993069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12926056190029547818629701 2423635535630540215993069)
                    ·
                      refine ⟨908863325861452580997401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423635535630540215993069 908863325861452580997401)
                      ·
                        rfl

theorem cell23_1770005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1770005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770005 prefixEnd_1770005 := by exact prefixLift 1770005
  have htrace : WordTrace (prefixWord ++ tailWord_1770005) baseStart_1770005 baseEnd_1770005 := by
    simpa [prefixWord, tailWord_1770005, baseEnd_1770005] using wordTrace_append hprefix tailTrace_1770005
  have hstable : (prefixWord ++ tailWord_1770005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770005).length < 2 ^ (prefixWord ++ tailWord_1770005).sum := by decide
  have hdescent : baseEnd_1770005 < baseStart_1770005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770012 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1770012 : Nat := 118140960795 + 1770012 * 2 ^ 59
def prefixEnd_1770012 : Nat := 4983230072969 + 3 ^ 40 * 1770012 * 2
def baseEnd_1770012 : Nat := 302955640075344684536623

theorem tailTrace_1770012 : CollatzResearch.WordTrace tailWord_1770012 prefixEnd_1770012 302955640075344684536623 := by
  unfold tailWord_1770012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278820631778146413928145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43038427509037528551904193 32278820631778146413928145)
  ·
    refine ⟨24209115473833609810446109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32278820631778146413928145 24209115473833609810446109)
    ·
      refine ⟨9078418302687603678917291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24209115473833609810446109 9078418302687603678917291)
      ·
        refine ⟨13617627454031405518375937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078418302687603678917291 13617627454031405518375937)
        ·
          refine ⟨10213220590523554138781953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617627454031405518375937 10213220590523554138781953)
          ·
            refine ⟨7659915442892665604086465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213220590523554138781953 7659915442892665604086465)
            ·
              refine ⟨5744936582169499203064849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659915442892665604086465 5744936582169499203064849)
              ·
                refine ⟨4308702436627124402298637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5744936582169499203064849 4308702436627124402298637)
                ·
                  refine ⟨1615763413735171650861989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4308702436627124402298637 1615763413735171650861989)
                  ·
                    refine ⟨302955640075344684536623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615763413735171650861989 302955640075344684536623)
                    ·
                      rfl

theorem cell23_1770012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1770012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770012 prefixEnd_1770012 := by exact prefixLift 1770012
  have htrace : WordTrace (prefixWord ++ tailWord_1770012) baseStart_1770012 baseEnd_1770012 := by
    simpa [prefixWord, tailWord_1770012, baseEnd_1770012] using wordTrace_append hprefix tailTrace_1770012
  have hstable : (prefixWord ++ tailWord_1770012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770012).length < 2 ^ (prefixWord ++ tailWord_1770012).sum := by decide
  have hdescent : baseEnd_1770012 < baseStart_1770012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770036 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1770036 : Nat := 118140960795 + 1770036 * 2 ^ 59
def prefixEnd_1770036 : Nat := 4983230072969 + 3 ^ 40 * 1770036 * 2
def baseEnd_1770036 : Nat := 908879243761741959709759

theorem tailTrace_1770036 : CollatzResearch.WordTrace tailWord_1770036 prefixEnd_1770036 908879243761741959709759 := by
  unfold tailWord_1770036
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279258307734672463364981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43039011076979563284486641 32279258307734672463364981)
  ·
    refine ⟨3026180466350125543440467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32279258307734672463364981 3026180466350125543440467)
    ·
      refine ⟨4539270699525188315160701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026180466350125543440467 4539270699525188315160701)
      ·
        refine ⟨1702226512321945618185263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4539270699525188315160701 1702226512321945618185263)
        ·
          refine ⟨2553339768482918427277895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702226512321945618185263 2553339768482918427277895)
          ·
            refine ⟨3830009652724377640916843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553339768482918427277895 3830009652724377640916843)
            ·
              refine ⟨5745014479086566461375265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830009652724377640916843 5745014479086566461375265)
              ·
                refine ⟨4308760859314924846031449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745014479086566461375265 4308760859314924846031449)
                ·
                  refine ⟨3231570644486193634523587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308760859314924846031449 3231570644486193634523587)
                  ·
                    refine ⟨4847355966729290451785381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231570644486193634523587 4847355966729290451785381)
                    ·
                      refine ⟨908879243761741959709759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4847355966729290451785381 908879243761741959709759)
                      ·
                        rfl

theorem cell23_1770036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1770036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770036 prefixEnd_1770036 := by exact prefixLift 1770036
  have htrace : WordTrace (prefixWord ++ tailWord_1770036) baseStart_1770036 baseEnd_1770036 := by
    simpa [prefixWord, tailWord_1770036, baseEnd_1770036] using wordTrace_append hprefix tailTrace_1770036
  have hstable : (prefixWord ++ tailWord_1770036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770036).length < 2 ^ (prefixWord ++ tailWord_1770036).sum := by decide
  have hdescent : baseEnd_1770036 < baseStart_1770036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770062 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_1770062 : Nat := 118140960795 + 1770062 * 2 ^ 59
def prefixEnd_1770062 : Nat := 4983230072969 + 3 ^ 40 * 1770062 * 2
def baseEnd_1770062 : Nat := 908892594258758857984639

theorem tailTrace_1770062 : CollatzResearch.WordTrace tailWord_1770062 prefixEnd_1770062 908892594258758857984639 := by
  unfold tailWord_1770062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069933114171893920897055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43039643275583434244784293 8069933114171893920897055)
  ·
    refine ⟨12104899671257840881345583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8069933114171893920897055 12104899671257840881345583)
    ·
      refine ⟨18157349506886761322018375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104899671257840881345583 18157349506886761322018375)
      ·
        refine ⟨27236024260330141983027563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18157349506886761322018375 27236024260330141983027563)
        ·
          refine ⟨40854036390495212974541345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27236024260330141983027563 40854036390495212974541345)
          ·
            refine ⟨30640527292871409730906009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40854036390495212974541345 30640527292871409730906009)
            ·
              refine ⟨22980395469653557298179507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30640527292871409730906009 22980395469653557298179507)
              ·
                refine ⟨34470593204480335947269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22980395469653557298179507 34470593204480335947269261)
                ·
                  refine ⟨12926472451680125980225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34470593204480335947269261 12926472451680125980225973)
                  ·
                    refine ⟨1211856792345011810646185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12926472451680125980225973 1211856792345011810646185)
                    ·
                      refine ⟨908892594258758857984639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211856792345011810646185 908892594258758857984639)
                      ·
                        rfl

theorem cell23_1770062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_1770062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770062 prefixEnd_1770062 := by exact prefixLift 1770062
  have htrace : WordTrace (prefixWord ++ tailWord_1770062) baseStart_1770062 baseEnd_1770062 := by
    simpa [prefixWord, tailWord_1770062, baseEnd_1770062] using wordTrace_append hprefix tailTrace_1770062
  have hstable : (prefixWord ++ tailWord_1770062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770062).length < 2 ^ (prefixWord ++ tailWord_1770062).sum := by decide
  have hdescent : baseEnd_1770062 < baseStart_1770062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770072 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_1770072 : Nat := 118140960795 + 1770072 * 2 ^ 59
def prefixEnd_1770072 : Nat := 4983230072969 + 3 ^ 40 * 1770072 * 2
def baseEnd_1770072 : Nat := 302965909688434606286531

theorem tailTrace_1770072 : CollatzResearch.WordTrace tailWord_1770072 prefixEnd_1770072 302965909688434606286531 := by
  unfold tailWord_1770072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279914821669461537520235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43039886428892615383360313 32279914821669461537520235)
  ·
    refine ⟨48419872232504192306280353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32279914821669461537520235 48419872232504192306280353)
    ·
      refine ⟨36314904174378144229710265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48419872232504192306280353 36314904174378144229710265)
      ·
        refine ⟨27236178130783608172282699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36314904174378144229710265 27236178130783608172282699)
        ·
          refine ⟨40854267196175412258424049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27236178130783608172282699 40854267196175412258424049)
          ·
            refine ⟨30640700397131559193818037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40854267196175412258424049 30640700397131559193818037)
            ·
              refine ⟨2872565662231083674420441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30640700397131559193818037 2872565662231083674420441)
              ·
                refine ⟨2154424246673312755815331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872565662231083674420441 2154424246673312755815331)
                ·
                  refine ⟨3231636370009969133722997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154424246673312755815331 3231636370009969133722997)
                  ·
                    refine ⟨302965909688434606286531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3231636370009969133722997 302965909688434606286531)
                    ·
                      rfl

theorem cell23_1770072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_1770072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770072 prefixEnd_1770072 := by exact prefixLift 1770072
  have htrace : WordTrace (prefixWord ++ tailWord_1770072) baseStart_1770072 baseEnd_1770072 := by
    simpa [prefixWord, tailWord_1770072, baseEnd_1770072] using wordTrace_append hprefix tailTrace_1770072
  have hstable : (prefixWord ++ tailWord_1770072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770072).length < 2 ^ (prefixWord ++ tailWord_1770072).sum := by decide
  have hdescent : baseEnd_1770072 < baseStart_1770072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770092 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1770092 : Nat := 118140960795 + 1770092 * 2 ^ 59
def prefixEnd_1770092 : Nat := 4983230072969 + 3 ^ 40 * 1770092 * 2
def baseEnd_1770092 : Nat := 908907998678393740609501

theorem tailTrace_1770092 : CollatzResearch.WordTrace tailWord_1770092 prefixEnd_1770092 908907998678393740609501 := by
  unfold tailWord_1770092
  simp only [CollatzResearch.WordTrace]
  refine ⟨32280279551633233245384265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43040372735510977660512353 32280279551633233245384265)
  ·
    refine ⟨24210209663724924934038199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32280279551633233245384265 24210209663724924934038199)
    ·
      refine ⟨36315314495587387401057299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24210209663724924934038199 36315314495587387401057299)
      ·
        refine ⟨54472971743381081101585949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36315314495587387401057299 54472971743381081101585949)
        ·
          refine ⟨20427364403767905413094731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54472971743381081101585949 20427364403767905413094731)
          ·
            refine ⟨30641046605651858119642097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427364403767905413094731 30641046605651858119642097)
            ·
              refine ⟨22980784954238893589731573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30641046605651858119642097 22980784954238893589731573)
              ·
                refine ⟨2154448589459896274037335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22980784954238893589731573 2154448589459896274037335)
                ·
                  refine ⟨3231672884189844411056003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154448589459896274037335 3231672884189844411056003)
                  ·
                    refine ⟨4847509326284766616584005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3231672884189844411056003 4847509326284766616584005)
                    ·
                      refine ⟨908907998678393740609501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4847509326284766616584005 908907998678393740609501)
                      ·
                        rfl

theorem cell23_1770092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1770092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770092 prefixEnd_1770092 := by exact prefixLift 1770092
  have htrace : WordTrace (prefixWord ++ tailWord_1770092) baseStart_1770092 baseEnd_1770092 := by
    simpa [prefixWord, tailWord_1770092, baseEnd_1770092] using wordTrace_append hprefix tailTrace_1770092
  have hstable : (prefixWord ++ tailWord_1770092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770092).length < 2 ^ (prefixWord ++ tailWord_1770092).sum := by decide
  have hdescent : baseEnd_1770092 < baseStart_1770092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770112 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1770112 : Nat := 118140960795 + 1770112 * 2 ^ 59
def prefixEnd_1770112 : Nat := 4983230072969 + 3 ^ 40 * 1770112 * 2
def baseEnd_1770112 : Nat := 908918268291483662359409

theorem tailTrace_1770112 : CollatzResearch.WordTrace tailWord_1770112 prefixEnd_1770112 908918268291483662359409 := by
  unfold tailWord_1770112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32280644281597004953248295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43040859042129339937664393 32280644281597004953248295)
  ·
    refine ⟨48420966422395507429872443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32280644281597004953248295 48420966422395507429872443)
    ·
      refine ⟨72631449633593261144808665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48420966422395507429872443 72631449633593261144808665)
      ·
        refine ⟨54473587225194945858606499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72631449633593261144808665 54473587225194945858606499)
        ·
          refine ⟨81710380837792418787909749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54473587225194945858606499 81710380837792418787909749)
          ·
            refine ⟨7660348203543039261366539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81710380837792418787909749 7660348203543039261366539)
            ·
              refine ⟨11490522305314558892049809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660348203543039261366539 11490522305314558892049809)
              ·
                refine ⟨8617891728985919169037357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11490522305314558892049809 8617891728985919169037357)
                ·
                  refine ⟨3231709398369719688389009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8617891728985919169037357 3231709398369719688389009)
                  ·
                    refine ⟨2423782048777289766291757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3231709398369719688389009 2423782048777289766291757)
                    ·
                      refine ⟨908918268291483662359409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423782048777289766291757 908918268291483662359409)
                      ·
                        rfl

theorem cell23_1770112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1770112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770112 prefixEnd_1770112 := by exact prefixLift 1770112
  have htrace : WordTrace (prefixWord ++ tailWord_1770112) baseStart_1770112 baseEnd_1770112 := by
    simpa [prefixWord, tailWord_1770112, baseEnd_1770112] using wordTrace_append hprefix tailTrace_1770112
  have hstable : (prefixWord ++ tailWord_1770112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770112).length < 2 ^ (prefixWord ++ tailWord_1770112).sum := by decide
  have hdescent : baseEnd_1770112 < baseStart_1770112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770115 : List Nat := [1, 1, 1, 3, 3, 1, 5, 8]
def baseStart_1770115 : Nat := 118140960795 + 1770115 * 2 ^ 59
def prefixEnd_1770115 : Nat := 4983230072969 + 3 ^ 40 * 1770115 * 2
def baseEnd_1770115 : Nat := 33663696619757301874885

theorem tailTrace_1770115 : CollatzResearch.WordTrace tailWord_1770115 prefixEnd_1770115 33663696619757301874885 := by
  unfold tailWord_1770115
  simp only [CollatzResearch.WordTrace]
  refine ⟨64561397982183141418855799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43040931988122094279237199 64561397982183141418855799)
  ·
    refine ⟨96842096973274712128283699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64561397982183141418855799 96842096973274712128283699)
    ·
      refine ⟨145263145459912068192425549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96842096973274712128283699 145263145459912068192425549)
      ·
        refine ⟨54473679547467025572159581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145263145459912068192425549 54473679547467025572159581)
        ·
          refine ⟨20427629830300134589559843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54473679547467025572159581 20427629830300134589559843)
          ·
            refine ⟨30641444745450201884339765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427629830300134589559843 30641444745450201884339765)
            ·
              refine ⟨2872635444885956426656853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30641444745450201884339765 2872635444885956426656853)
              ·
                refine ⟨33663696619757301874885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2872635444885956426656853 33663696619757301874885)
                ·
                  rfl

theorem cell23_1770115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 8].length) (baseStart_1770115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770115 prefixEnd_1770115 := by exact prefixLift 1770115
  have htrace : WordTrace (prefixWord ++ tailWord_1770115) baseStart_1770115 baseEnd_1770115 := by
    simpa [prefixWord, tailWord_1770115, baseEnd_1770115] using wordTrace_append hprefix tailTrace_1770115
  have hstable : (prefixWord ++ tailWord_1770115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770115).length < 2 ^ (prefixWord ++ tailWord_1770115).sum := by decide
  have hdescent : baseEnd_1770115 < baseStart_1770115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770126 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1770126 : Nat := 118140960795 + 1770126 * 2 ^ 59
def prefixEnd_1770126 : Nat := 4983230072969 + 3 ^ 40 * 1770126 * 2
def baseEnd_1770126 : Nat := 908925457020646607584345

theorem tailTrace_1770126 : CollatzResearch.WordTrace tailWord_1770126 prefixEnd_1770126 908925457020646607584345 := by
  unfold tailWord_1770126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070224898142911287188279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43041199456762193531670821 8070224898142911287188279)
  ·
    refine ⟨12105337347214366930782419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8070224898142911287188279 12105337347214366930782419)
    ·
      refine ⟨18158006020821550396173629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12105337347214366930782419 18158006020821550396173629)
      ·
        refine ⟨6809252257808081398565111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18158006020821550396173629 6809252257808081398565111)
        ·
          refine ⟨10213878386712122097847667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809252257808081398565111 10213878386712122097847667)
          ·
            refine ⟨15320817580068183146771501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213878386712122097847667 15320817580068183146771501)
            ·
              refine ⟨5745306592525568680039313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15320817580068183146771501 5745306592525568680039313)
              ·
                refine ⟨4308979944394176510029485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745306592525568680039313 4308979944394176510029485)
                ·
                  refine ⟨1615867479147816191261057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4308979944394176510029485 1615867479147816191261057)
                  ·
                    refine ⟨1211900609360862143445793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1615867479147816191261057 1211900609360862143445793)
                    ·
                      refine ⟨908925457020646607584345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211900609360862143445793 908925457020646607584345)
                      ·
                        rfl

theorem cell23_1770126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1770126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770126 prefixEnd_1770126 := by exact prefixLift 1770126
  have htrace : WordTrace (prefixWord ++ tailWord_1770126) baseStart_1770126 baseEnd_1770126 := by
    simpa [prefixWord, tailWord_1770126, baseEnd_1770126] using wordTrace_append hprefix tailTrace_1770126
  have hstable : (prefixWord ++ tailWord_1770126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770126).length < 2 ^ (prefixWord ++ tailWord_1770126).sum := by decide
  have hdescent : baseEnd_1770126 < baseStart_1770126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770159 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_1770159 : Nat := 118140960795 + 1770159 * 2 ^ 59
def prefixEnd_1770159 : Nat := 4983230072969 + 3 ^ 40 * 1770159 * 2
def baseEnd_1770159 : Nat := 908942401882244978471693

theorem tailTrace_1770159 : CollatzResearch.WordTrace tailWord_1770159 prefixEnd_1770159 908942401882244978471693 := by
  unfold tailWord_1770159
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563002794023736933457531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43042001862682491288971687 64563002794023736933457531)
  ·
    refine ⟨96844504191035605400186297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64563002794023736933457531 96844504191035605400186297)
    ·
      refine ⟨72633378143276704050139723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96844504191035605400186297 72633378143276704050139723)
      ·
        refine ⟨108950067214915056075209585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72633378143276704050139723 108950067214915056075209585)
        ·
          refine ⟨81712550411186292056407189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108950067214915056075209585 81712550411186292056407189)
          ·
            refine ⟨3830275800524357440144087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81712550411186292056407189 3830275800524357440144087)
            ·
              refine ⟨5745413700786536160216131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830275800524357440144087 5745413700786536160216131)
              ·
                refine ⟨8618120551179804240324197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745413700786536160216131 8618120551179804240324197)
                ·
                  refine ⟨1615897603346213295060787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8618120551179804240324197 1615897603346213295060787)
                  ·
                    refine ⟨2423846405019319942591181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1615897603346213295060787 2423846405019319942591181)
                    ·
                      refine ⟨908942401882244978471693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423846405019319942591181 908942401882244978471693)
                      ·
                        rfl

theorem cell23_1770159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_1770159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770159 prefixEnd_1770159 := by exact prefixLift 1770159
  have htrace : WordTrace (prefixWord ++ tailWord_1770159) baseStart_1770159 baseEnd_1770159 := by
    simpa [prefixWord, tailWord_1770159, baseEnd_1770159] using wordTrace_append hprefix tailTrace_1770159
  have hstable : (prefixWord ++ tailWord_1770159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770159).length < 2 ^ (prefixWord ++ tailWord_1770159).sum := by decide
  have hdescent : baseEnd_1770159 < baseStart_1770159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770185 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1770185 : Nat := 118140960795 + 1770185 * 2 ^ 59
def prefixEnd_1770185 : Nat := 4983230072969 + 3 ^ 40 * 1770185 * 2
def baseEnd_1770185 : Nat := 908955752379261876746573

theorem tailTrace_1770185 : CollatzResearch.WordTrace tailWord_1770185 prefixEnd_1770185 908955752379261876746573 := by
  unfold tailWord_1770185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563951091929543373904009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43042634061286362249269339 64563951091929543373904009)
  ·
    refine ⟨48422963318947157530428007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64563951091929543373904009 48422963318947157530428007)
    ·
      refine ⟨72634444978420736295642011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48422963318947157530428007 72634444978420736295642011)
      ·
        refine ⟨108951667467631104443463017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72634444978420736295642011 108951667467631104443463017)
        ·
          refine ⟨81713750600723328332597263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108951667467631104443463017 81713750600723328332597263)
          ·
            refine ⟨122570625901084992498895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81713750600723328332597263 122570625901084992498895895)
            ·
              refine ⟨183855938851627488748343843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122570625901084992498895895 183855938851627488748343843)
              ·
                refine ⟨275783908277441233122515765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183855938851627488748343843 275783908277441233122515765)
                ·
                  refine ⟨25854741401010115605235853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275783908277441233122515765 25854741401010115605235853)
                  ·
                    refine ⟨9695528025378793351963445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25854741401010115605235853 9695528025378793351963445)
                    ·
                      refine ⟨908955752379261876746573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9695528025378793351963445 908955752379261876746573)
                      ·
                        rfl

theorem cell23_1770185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1770185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770185 prefixEnd_1770185 := by exact prefixLift 1770185
  have htrace : WordTrace (prefixWord ++ tailWord_1770185) baseStart_1770185 baseEnd_1770185 := by
    simpa [prefixWord, tailWord_1770185, baseEnd_1770185] using wordTrace_append hprefix tailTrace_1770185
  have hstable : (prefixWord ++ tailWord_1770185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770185).length < 2 ^ (prefixWord ++ tailWord_1770185).sum := by decide
  have hdescent : baseEnd_1770185 < baseStart_1770185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770186 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_1770186 : Nat := 118140960795 + 1770186 * 2 ^ 59
def prefixEnd_1770186 : Nat := 4983230072969 + 3 ^ 40 * 1770186 * 2
def baseEnd_1770186 : Nat := 908956265859916372834069

theorem tailTrace_1770186 : CollatzResearch.WordTrace tailWord_1770186 prefixEnd_1770186 908956265859916372834069 := by
  unfold tailWord_1770186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140996891231480136172603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43042658376617280363126941 16140996891231480136172603)
  ·
    refine ⟨24211495336847220204258905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16140996891231480136172603 24211495336847220204258905)
    ·
      refine ⟨18158621502635415153194179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24211495336847220204258905 18158621502635415153194179)
      ·
        refine ⟨27237932253953122729791269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18158621502635415153194179 27237932253953122729791269)
        ·
          refine ⟨5107112297616210511835863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27237932253953122729791269 5107112297616210511835863)
          ·
            refine ⟨7660668446424315767753795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107112297616210511835863 7660668446424315767753795)
            ·
              refine ⟨11491002669636473651630693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660668446424315767753795 11491002669636473651630693)
              ·
                refine ⟨2154563000556838809680755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11491002669636473651630693 2154563000556838809680755)
                ·
                  refine ⟨3231844500835258214521133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154563000556838809680755 3231844500835258214521133)
                  ·
                    refine ⟨1211941687813221830445425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231844500835258214521133 1211941687813221830445425)
                    ·
                      refine ⟨908956265859916372834069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1211941687813221830445425 908956265859916372834069)
                      ·
                        rfl

theorem cell23_1770186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_1770186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770186 prefixEnd_1770186 := by exact prefixLift 1770186
  have htrace : WordTrace (prefixWord ++ tailWord_1770186) baseStart_1770186 baseEnd_1770186 := by
    simpa [prefixWord, tailWord_1770186, baseEnd_1770186] using wordTrace_append hprefix tailTrace_1770186
  have hstable : (prefixWord ++ tailWord_1770186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770186).length < 2 ^ (prefixWord ++ tailWord_1770186).sum := by decide
  have hdescent : baseEnd_1770186 < baseStart_1770186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770202 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1770202 : Nat := 118140960795 + 1770202 * 2 ^ 59
def prefixEnd_1770202 : Nat := 4983230072969 + 3 ^ 40 * 1770202 * 2
def baseEnd_1770202 : Nat := 908964481550388310233995

theorem tailTrace_1770202 : CollatzResearch.WordTrace tailWord_1770202 prefixEnd_1770202 908964481550388310233995 := by
  unfold tailWord_1770202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141142783216988819318215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43043047421911970184848573 16141142783216988819318215)
  ·
    refine ⟨24211714174825483228977323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141142783216988819318215 24211714174825483228977323)
    ·
      refine ⟨36317571262238224843465985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24211714174825483228977323 36317571262238224843465985)
      ·
        refine ⟨27238178446678668632599489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36317571262238224843465985 27238178446678668632599489)
        ·
          refine ⟨20428633835009001474449617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27238178446678668632599489 20428633835009001474449617)
          ·
            refine ⟨15321475376256751105837213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20428633835009001474449617 15321475376256751105837213)
            ·
              refine ⟨5745553266096281664688955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321475376256751105837213 5745553266096281664688955)
              ·
                refine ⟨8618329899144422497033433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745553266096281664688955 8618329899144422497033433)
                ·
                  refine ⟨6463747424358316872775075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8618329899144422497033433 6463747424358316872775075)
                  ·
                    refine ⟨9695621136537475309162613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6463747424358316872775075 9695621136537475309162613)
                    ·
                      refine ⟨908964481550388310233995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9695621136537475309162613 908964481550388310233995)
                      ·
                        rfl

theorem cell23_1770202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1770202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770202 prefixEnd_1770202 := by exact prefixLift 1770202
  have htrace : WordTrace (prefixWord ++ tailWord_1770202) baseStart_1770202 baseEnd_1770202 := by
    simpa [prefixWord, tailWord_1770202, baseEnd_1770202] using wordTrace_append hprefix tailTrace_1770202
  have hstable : (prefixWord ++ tailWord_1770202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770202).length < 2 ^ (prefixWord ++ tailWord_1770202).sum := by decide
  have hdescent : baseEnd_1770202 < baseStart_1770202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770232 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1770232 : Nat := 118140960795 + 1770232 * 2 ^ 59
def prefixEnd_1770232 : Nat := 4983230072969 + 3 ^ 40 * 1770232 * 2
def baseEnd_1770232 : Nat := 908979885970023192858857

theorem tailTrace_1770232 : CollatzResearch.WordTrace tailWord_1770232 prefixEnd_1770232 908979885970023192858857 := by
  unfold tailWord_1770232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32282832661379635200432475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43043776881839513600576633 32282832661379635200432475)
  ·
    refine ⟨48424248992069452800648713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32282832661379635200432475 48424248992069452800648713)
    ·
      refine ⟨36318186744052089600486535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48424248992069452800648713 36318186744052089600486535)
      ·
        refine ⟨54477280116078134400729803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36318186744052089600486535 54477280116078134400729803)
        ·
          refine ⟨81715920174117201601094705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54477280116078134400729803 81715920174117201601094705)
          ·
            refine ⟨61286940130587901200821029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81715920174117201601094705 61286940130587901200821029)
            ·
              refine ⟨11491301274485231475153943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61286940130587901200821029 11491301274485231475153943)
              ·
                refine ⟨17236951911727847212730915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491301274485231475153943 17236951911727847212730915)
                ·
                  refine ⟨25855427867591770819096373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17236951911727847212730915 25855427867591770819096373)
                  ·
                    refine ⟨2423946362586728514290285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25855427867591770819096373 2423946362586728514290285)
                    ·
                      refine ⟨908979885970023192858857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2423946362586728514290285 908979885970023192858857)
                      ·
                        rfl

theorem cell23_1770232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1770232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770232 prefixEnd_1770232 := by exact prefixLift 1770232
  have htrace : WordTrace (prefixWord ++ tailWord_1770232) baseStart_1770232 baseEnd_1770232 := by
    simpa [prefixWord, tailWord_1770232, baseEnd_1770232] using wordTrace_append hprefix tailTrace_1770232
  have hstable : (prefixWord ++ tailWord_1770232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770232).length < 2 ^ (prefixWord ++ tailWord_1770232).sum := by decide
  have hdescent : baseEnd_1770232 < baseStart_1770232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770309 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1770309 : Nat := 118140960795 + 1770309 * 2 ^ 59
def prefixEnd_1770309 : Nat := 4983230072969 + 3 ^ 40 * 1770309 * 2
def baseEnd_1770309 : Nat := 909019423980419391596003

theorem tailTrace_1770309 : CollatzResearch.WordTrace tailWord_1770309 prefixEnd_1770309 909019423980419391596003 := by
  unfold tailWord_1770309
  simp only [CollatzResearch.WordTrace]
  refine ⟨64568473743480312551417981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43045649162320208367611987 64568473743480312551417981)
  ·
    refine ⟨24213177653805117206781743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64568473743480312551417981 24213177653805117206781743)
    ·
      refine ⟨36319766480707675810172615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24213177653805117206781743 36319766480707675810172615)
      ·
        refine ⟨54479649721061513715258923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36319766480707675810172615 54479649721061513715258923)
        ·
          refine ⟨81719474581592270572888385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54479649721061513715258923 81719474581592270572888385)
          ·
            refine ⟨61289605936194202929666289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81719474581592270572888385 61289605936194202929666289)
            ·
              refine ⟨45967204452145652197249717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61289605936194202929666289 45967204452145652197249717)
              ·
                refine ⟨4309425417388654893492161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45967204452145652197249717 4309425417388654893492161)
                ·
                  refine ⟨3232069063041491170119121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309425417388654893492161 3232069063041491170119121)
                  ·
                    refine ⟨2424051797281118377589341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3232069063041491170119121 2424051797281118377589341)
                    ·
                      refine ⟨909019423980419391596003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424051797281118377589341 909019423980419391596003)
                      ·
                        rfl

theorem cell23_1770309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1770309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770309 prefixEnd_1770309 := by exact prefixLift 1770309
  have htrace : WordTrace (prefixWord ++ tailWord_1770309) baseStart_1770309 baseEnd_1770309 := by
    simpa [prefixWord, tailWord_1770309, baseEnd_1770309] using wordTrace_append hprefix tailTrace_1770309
  have hstable : (prefixWord ++ tailWord_1770309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770309).length < 2 ^ (prefixWord ++ tailWord_1770309).sum := by decide
  have hdescent : baseEnd_1770309 < baseStart_1770309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770312 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 8]
def baseStart_1770312 : Nat := 118140960795 + 1770312 * 2 ^ 59
def prefixEnd_1770312 : Nat := 4983230072969 + 3 ^ 40 * 1770312 * 2
def baseEnd_1770312 : Nat := 101002329380264764428721

theorem tailTrace_1770312 : CollatzResearch.WordTrace tailWord_1770312 prefixEnd_1770312 101002329380264764428721 := by
  unfold tailWord_1770312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32284291581234722031888595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43045722108312962709184793 32284291581234722031888595)
  ·
    refine ⟨48426437371852083047832893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32284291581234722031888595 48426437371852083047832893)
    ·
      refine ⟨18159914014444531142937335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48426437371852083047832893 18159914014444531142937335)
      ·
        refine ⟨27239871021666796714406003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18159914014444531142937335 27239871021666796714406003)
        ·
          refine ⟨40859806532500195071609005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27239871021666796714406003 40859806532500195071609005)
          ·
            refine ⟨15322427449687573151853377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40859806532500195071609005 15322427449687573151853377)
            ·
              refine ⟨11491820587265679863890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15322427449687573151853377 11491820587265679863890033)
              ·
                refine ⟨8618865440449259897917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11491820587265679863890033 8618865440449259897917525)
                ·
                  refine ⟨101002329380264764428721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8618865440449259897917525 101002329380264764428721)
                  ·
                    rfl

theorem cell23_1770312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_1770312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770312 prefixEnd_1770312 := by exact prefixLift 1770312
  have htrace : WordTrace (prefixWord ++ tailWord_1770312) baseStart_1770312 baseEnd_1770312 := by
    simpa [prefixWord, tailWord_1770312, baseEnd_1770312] using wordTrace_append hprefix tailTrace_1770312
  have hstable : (prefixWord ++ tailWord_1770312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770312).length < 2 ^ (prefixWord ++ tailWord_1770312).sum := by decide
  have hdescent : baseEnd_1770312 < baseStart_1770312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770329 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 6]
def baseStart_1770329 : Nat := 118140960795 + 1770329 * 2 ^ 59
def prefixEnd_1770329 : Nat := 4983230072969 + 3 ^ 40 * 1770329 * 2
def baseEnd_1770329 : Nat := 101003299288167701482879

theorem tailTrace_1770329 : CollatzResearch.WordTrace tailWord_1770329 prefixEnd_1770329 101003299288167701482879 := by
  unfold tailWord_1770329
  simp only [CollatzResearch.WordTrace]
  refine ⟨64569203203407855967146041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43046135468938570644764027 64569203203407855967146041)
  ·
    refine ⟨48426902402555891975359531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64569203203407855967146041 48426902402555891975359531)
    ·
      refine ⟨72640353603833837963039297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48426902402555891975359531 72640353603833837963039297)
      ·
        refine ⟨54480265202875378472279473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72640353603833837963039297 54480265202875378472279473)
        ·
          refine ⟨40860198902156533854209605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54480265202875378472279473 40860198902156533854209605)
          ·
            refine ⟨7661287294154350097664301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40860198902156533854209605 7661287294154350097664301)
            ·
              refine ⟨2872982735307881286624113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7661287294154350097664301 2872982735307881286624113)
              ·
                refine ⟨2154737051480910964968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872982735307881286624113 2154737051480910964968085)
                ·
                  refine ⟨101003299288167701482879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2154737051480910964968085 101003299288167701482879)
                  ·
                    rfl

theorem cell23_1770329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_1770329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770329 prefixEnd_1770329 := by exact prefixLift 1770329
  have htrace : WordTrace (prefixWord ++ tailWord_1770329) baseStart_1770329 baseEnd_1770329 := by
    simpa [prefixWord, tailWord_1770329, baseEnd_1770329] using wordTrace_append hprefix tailTrace_1770329
  have hstable : (prefixWord ++ tailWord_1770329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770329).length < 2 ^ (prefixWord ++ tailWord_1770329).sum := by decide
  have hdescent : baseEnd_1770329 < baseStart_1770329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770352 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1770352 : Nat := 118140960795 + 1770352 * 2 ^ 59
def prefixEnd_1770352 : Nat := 4983230072969 + 3 ^ 40 * 1770352 * 2
def baseEnd_1770352 : Nat := 909041503648562723358305

theorem tailTrace_1770352 : CollatzResearch.WordTrace tailWord_1770352 prefixEnd_1770352 909041503648562723358305 := by
  unfold tailWord_1770352
  simp only [CollatzResearch.WordTrace]
  refine ⟨32285021041162265447616655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43046694721549687263488873 32285021041162265447616655)
  ·
    refine ⟨48427531561743398171424983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32285021041162265447616655 48427531561743398171424983)
    ·
      refine ⟨72641297342615097257137475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48427531561743398171424983 72641297342615097257137475)
      ·
        refine ⟨108961946013922645885706213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72641297342615097257137475 108961946013922645885706213)
        ·
          refine ⟨20430364877610496103569915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108961946013922645885706213 20430364877610496103569915)
          ·
            refine ⟨30645547316415744155354873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20430364877610496103569915 30645547316415744155354873)
            ·
              refine ⟨22984160487311808116516155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30645547316415744155354873 22984160487311808116516155)
              ·
                refine ⟨34476240730967712174774233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22984160487311808116516155 34476240730967712174774233)
                ·
                  refine ⟨25857180548225784131080675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34476240730967712174774233 25857180548225784131080675)
                  ·
                    refine ⟨38785770822338676196621013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25857180548225784131080675 38785770822338676196621013)
                    ·
                      refine ⟨909041503648562723358305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38785770822338676196621013 909041503648562723358305)
                      ·
                        rfl

theorem cell23_1770352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1770352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770352 prefixEnd_1770352 := by exact prefixLift 1770352
  have htrace : WordTrace (prefixWord ++ tailWord_1770352) baseStart_1770352 baseEnd_1770352 := by
    simpa [prefixWord, tailWord_1770352, baseEnd_1770352] using wordTrace_append hprefix tailTrace_1770352
  have hstable : (prefixWord ++ tailWord_1770352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770352).length < 2 ^ (prefixWord ++ tailWord_1770352).sum := by decide
  have hdescent : baseEnd_1770352 < baseStart_1770352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770376 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1770376 : Nat := 118140960795 + 1770376 * 2 ^ 59
def prefixEnd_1770376 : Nat := 4983230072969 + 3 ^ 40 * 1770376 * 2
def baseEnd_1770376 : Nat := 303017942394756876486065

theorem tailTrace_1770376 : CollatzResearch.WordTrace tailWord_1770376 prefixEnd_1770376 303017942394756876486065 := by
  unfold tailWord_1770376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32285458717118791497053491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43047278289491721996071321 32285458717118791497053491)
  ·
    refine ⟨48428188075678187245580237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32285458717118791497053491 48428188075678187245580237)
    ·
      refine ⟨18160570528379320217092589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48428188075678187245580237 18160570528379320217092589)
      ·
        refine ⟨6810213948142245081409721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18160570528379320217092589 6810213948142245081409721)
        ·
          refine ⟨5107660461106683811057291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6810213948142245081409721 5107660461106683811057291)
          ·
            refine ⟨7661490691660025716585937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107660461106683811057291 7661490691660025716585937)
            ·
              refine ⟨5746118018745019287439453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7661490691660025716585937 5746118018745019287439453)
              ·
                refine ⟨2154794257029382232789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5746118018745019287439453 2154794257029382232789795)
                ·
                  refine ⟨3232191385544073349184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154794257029382232789795 3232191385544073349184693)
                  ·
                    refine ⟨303017942394756876486065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3232191385544073349184693 303017942394756876486065)
                    ·
                      rfl

theorem cell23_1770376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1770376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770376 prefixEnd_1770376 := by exact prefixLift 1770376
  have htrace : WordTrace (prefixWord ++ tailWord_1770376) baseStart_1770376 baseEnd_1770376 := by
    simpa [prefixWord, tailWord_1770376, baseEnd_1770376] using wordTrace_append hprefix tailTrace_1770376
  have hstable : (prefixWord ++ tailWord_1770376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770376).length < 2 ^ (prefixWord ++ tailWord_1770376).sum := by decide
  have hdescent : baseEnd_1770376 < baseStart_1770376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770409 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_1770409 : Nat := 118140960795 + 1770409 * 2 ^ 59
def prefixEnd_1770409 : Nat := 4983230072969 + 3 ^ 40 * 1770409 * 2
def baseEnd_1770409 : Nat := 909070772045869000345543

theorem tailTrace_1770409 : CollatzResearch.WordTrace tailWord_1770409 prefixEnd_1770409 909070772045869000345543 := by
  unfold tailWord_1770409
  simp only [CollatzResearch.WordTrace]
  refine ⟨64572121043118029630058281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43048080695412019753372187 64572121043118029630058281)
  ·
    refine ⟨48429090782338522222543711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64572121043118029630058281 48429090782338522222543711)
    ·
      refine ⟨72643636173507783333815567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48429090782338522222543711 72643636173507783333815567)
      ·
        refine ⟨108965454260261675000723351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72643636173507783333815567 108965454260261675000723351)
        ·
          refine ⟨163448181390392512501085027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108965454260261675000723351 163448181390392512501085027)
          ·
            refine ⟨245172272085588768751627541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163448181390392512501085027 245172272085588768751627541)
            ·
              refine ⟨11492450254011973535232541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245172272085588768751627541 11492450254011973535232541)
              ·
                refine ⟨4309668845254490075712203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11492450254011973535232541 4309668845254490075712203)
                ·
                  refine ⟨6464503267881735113568305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309668845254490075712203 6464503267881735113568305)
                  ·
                    refine ⟨4848377450911301335176229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6464503267881735113568305 4848377450911301335176229)
                    ·
                      refine ⟨909070772045869000345543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4848377450911301335176229 909070772045869000345543)
                      ·
                        rfl

theorem cell23_1770409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_1770409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770409 prefixEnd_1770409 := by exact prefixLift 1770409
  have htrace : WordTrace (prefixWord ++ tailWord_1770409) baseStart_1770409 baseEnd_1770409 := by
    simpa [prefixWord, tailWord_1770409, baseEnd_1770409] using wordTrace_append hprefix tailTrace_1770409
  have hstable : (prefixWord ++ tailWord_1770409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770409).length < 2 ^ (prefixWord ++ tailWord_1770409).sum := by decide
  have hdescent : baseEnd_1770409 < baseStart_1770409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770436 : List Nat := [2, 3, 3, 3, 1, 11]
def baseStart_1770436 : Nat := 118140960795 + 1770436 * 2 ^ 59
def prefixEnd_1770436 : Nat := 4983230072969 + 3 ^ 40 * 1770436 * 2
def baseEnd_1770436 : Nat := 3741089037133911089333

theorem tailTrace_1770436 : CollatzResearch.WordTrace tailWord_1770436 prefixEnd_1770436 3741089037133911089333 := by
  unfold tailWord_1770436
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286552907010106620645581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43048737209346808827527441 32286552907010106620645581)
  ·
    refine ⟨12107457340128789982742093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32286552907010106620645581 12107457340128789982742093)
    ·
      refine ⟨4540296502548296243528285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12107457340128789982742093 4540296502548296243528285)
      ·
        refine ⟨1702611188455611091323107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4540296502548296243528285 1702611188455611091323107)
        ·
          refine ⟨2553916782683416636984661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702611188455611091323107 2553916782683416636984661)
          ·
            refine ⟨3741089037133911089333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2553916782683416636984661 3741089037133911089333)
            ·
              rfl

theorem cell23_1770436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 11].length) (baseStart_1770436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770436 prefixEnd_1770436 := by exact prefixLift 1770436
  have htrace : WordTrace (prefixWord ++ tailWord_1770436) baseStart_1770436 baseEnd_1770436 := by
    simpa [prefixWord, tailWord_1770436, baseEnd_1770436] using wordTrace_append hprefix tailTrace_1770436
  have hstable : (prefixWord ++ tailWord_1770436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770436).length < 2 ^ (prefixWord ++ tailWord_1770436).sum := by decide
  have hdescent : baseEnd_1770436 < baseStart_1770436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770447 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 1, 2, 2]
def baseStart_1770447 : Nat := 118140960795 + 1770447 * 2 ^ 59
def prefixEnd_1770447 : Nat := 4983230072969 + 3 ^ 40 * 1770447 * 2
def baseEnd_1770447 : Nat := 909090284310739851670369

theorem tailTrace_1770447 : CollatzResearch.WordTrace tailWord_1770447 prefixEnd_1770447 909090284310739851670369 := by
  unfold tailWord_1770447
  simp only [CollatzResearch.WordTrace]
  refine ⟨64573507016980362119941595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43049004677986908079961063 64573507016980362119941595)
  ·
    refine ⟨96860260525470543179912393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64573507016980362119941595 96860260525470543179912393)
    ·
      refine ⟨72645195394102907384934295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96860260525470543179912393 72645195394102907384934295)
      ·
        refine ⟨108967793091154361077401443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72645195394102907384934295 108967793091154361077401443)
        ·
          refine ⟨163451689636731541616102165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108967793091154361077401443 163451689636731541616102165)
          ·
            refine ⟨7661797951721791013254789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163451689636731541616102165 7661797951721791013254789)
            ·
              refine ⟨1436587115947835814985273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7661797951721791013254789 1436587115947835814985273)
              ·
                refine ⟨1077440336960876861238955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436587115947835814985273 1077440336960876861238955)
                ·
                  refine ⟨1616160505441315291858433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077440336960876861238955 1616160505441315291858433)
                  ·
                    refine ⟨1212120379080986468893825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616160505441315291858433 1212120379080986468893825)
                    ·
                      refine ⟨909090284310739851670369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212120379080986468893825 909090284310739851670369)
                      ·
                        rfl

theorem cell23_1770447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 2, 2].length) (baseStart_1770447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770447 prefixEnd_1770447 := by exact prefixLift 1770447
  have htrace : WordTrace (prefixWord ++ tailWord_1770447) baseStart_1770447 baseEnd_1770447 := by
    simpa [prefixWord, tailWord_1770447, baseEnd_1770447] using wordTrace_append hprefix tailTrace_1770447
  have hstable : (prefixWord ++ tailWord_1770447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770447).length < 2 ^ (prefixWord ++ tailWord_1770447).sum := by decide
  have hdescent : baseEnd_1770447 < baseStart_1770447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770453 : List Nat := [1, 3, 2, 3, 4, 1, 1, 8]
def baseStart_1770453 : Nat := 118140960795 + 1770453 * 2 ^ 59
def prefixEnd_1770453 : Nat := 4983230072969 + 3 ^ 40 * 1770453 * 2
def baseEnd_1770453 : Nat := 33670124636839512155383

theorem tailTrace_1770453 : CollatzResearch.WordTrace tailWord_1770453 prefixEnd_1770453 33670124636839512155383 := by
  unfold tailWord_1770453
  simp only [CollatzResearch.WordTrace]
  refine ⟨64573725854958625144660013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43049150569972416763106675 64573725854958625144660013)
  ·
    refine ⟨24215147195609484429247505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64573725854958625144660013 24215147195609484429247505)
    ·
      refine ⟨18161360396707113321935629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24215147195609484429247505 18161360396707113321935629)
      ·
        refine ⟨6810510148765167495725861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18161360396707113321935629 6810510148765167495725861)
        ·
          refine ⟨1276970652893468905448599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6810510148765167495725861 1276970652893468905448599)
          ·
            refine ⟨1915455979340203358172899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276970652893468905448599 1915455979340203358172899)
            ·
              refine ⟨2873183969010305037259349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915455979340203358172899 2873183969010305037259349)
              ·
                refine ⟨33670124636839512155383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2873183969010305037259349 33670124636839512155383)
                ·
                  rfl

theorem cell23_1770453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 8].length) (baseStart_1770453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770453 prefixEnd_1770453 := by exact prefixLift 1770453
  have htrace : WordTrace (prefixWord ++ tailWord_1770453) baseStart_1770453 baseEnd_1770453 := by
    simpa [prefixWord, tailWord_1770453, baseEnd_1770453] using wordTrace_append hprefix tailTrace_1770453
  have hstable : (prefixWord ++ tailWord_1770453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770453).length < 2 ^ (prefixWord ++ tailWord_1770453).sum := by decide
  have hdescent : baseEnd_1770453 < baseStart_1770453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770463 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1770463 : Nat := 118140960795 + 1770463 * 2 ^ 59
def prefixEnd_1770463 : Nat := 4983230072969 + 3 ^ 40 * 1770463 * 2
def baseEnd_1770463 : Nat := 909098500001211789070295

theorem tailTrace_1770463 : CollatzResearch.WordTrace tailWord_1770463 prefixEnd_1770463 909098500001211789070295 := by
  unfold tailWord_1770463
  simp only [CollatzResearch.WordTrace]
  refine ⟨64574090584922396852524043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43049393723281597901682695 64574090584922396852524043)
  ·
    refine ⟨96861135877383595278786065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64574090584922396852524043 96861135877383595278786065)
    ·
      refine ⟨72645851908037696459089549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96861135877383595278786065 72645851908037696459089549)
      ·
        refine ⟨27242194465514136172158581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72645851908037696459089549 27242194465514136172158581)
        ·
          refine ⟨2553955731141950266139867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27242194465514136172158581 2553955731141950266139867)
          ·
            refine ⟨3830933596712925399209801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553955731141950266139867 3830933596712925399209801)
            ·
              refine ⟨2873200197534694049407351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3830933596712925399209801 2873200197534694049407351)
              ·
                refine ⟨4309800296302041074111027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873200197534694049407351 4309800296302041074111027)
                ·
                  refine ⟨6464700444453061611166541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309800296302041074111027 6464700444453061611166541)
                  ·
                    refine ⟨2424262666669898104187453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6464700444453061611166541 2424262666669898104187453)
                    ·
                      refine ⟨909098500001211789070295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424262666669898104187453 909098500001211789070295)
                      ·
                        rfl

theorem cell23_1770463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1770463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770463 prefixEnd_1770463 := by exact prefixLift 1770463
  have htrace : WordTrace (prefixWord ++ tailWord_1770463) baseStart_1770463 baseEnd_1770463 := by
    simpa [prefixWord, tailWord_1770463, baseEnd_1770463] using wordTrace_append hprefix tailTrace_1770463
  have hstable : (prefixWord ++ tailWord_1770463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770463).length < 2 ^ (prefixWord ++ tailWord_1770463).sum := by decide
  have hdescent : baseEnd_1770463 < baseStart_1770463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770489 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1770489 : Nat := 118140960795 + 1770489 * 2 ^ 59
def prefixEnd_1770489 : Nat := 4983230072969 + 3 ^ 40 * 1770489 * 2
def baseEnd_1770489 : Nat := 909111850498228687345175

theorem tailTrace_1770489 : CollatzResearch.WordTrace tailWord_1770489 prefixEnd_1770489 909111850498228687345175 := by
  unfold tailWord_1770489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64575038882828203292970521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43050025921885468861980347 64575038882828203292970521)
  ·
    refine ⟨48431279162121152469727891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64575038882828203292970521 48431279162121152469727891)
    ·
      refine ⟨72646918743181728704591837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48431279162121152469727891 72646918743181728704591837)
      ·
        refine ⟨27242594528693148264221939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72646918743181728704591837 27242594528693148264221939)
        ·
          refine ⟨40863891793039722396332909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27242594528693148264221939 40863891793039722396332909)
          ·
            refine ⟨15323959422389895898624841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40863891793039722396332909 15323959422389895898624841)
            ·
              refine ⟨11492969566792421923968631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15323959422389895898624841 11492969566792421923968631)
              ·
                refine ⟨17239454350188632885952947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492969566792421923968631 17239454350188632885952947)
                ·
                  refine ⟨25859181525282949328929421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17239454350188632885952947 25859181525282949328929421)
                  ·
                    refine ⟨9697193071981105998348533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25859181525282949328929421 9697193071981105998348533)
                    ·
                      refine ⟨909111850498228687345175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9697193071981105998348533 909111850498228687345175)
                      ·
                        rfl

theorem cell23_1770489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1770489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770489 prefixEnd_1770489 := by exact prefixLift 1770489
  have htrace : WordTrace (prefixWord ++ tailWord_1770489) baseStart_1770489 baseEnd_1770489 := by
    simpa [prefixWord, tailWord_1770489, baseEnd_1770489] using wordTrace_append hprefix tailTrace_1770489
  have hstable : (prefixWord ++ tailWord_1770489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770489).length < 2 ^ (prefixWord ++ tailWord_1770489).sum := by decide
  have hdescent : baseEnd_1770489 < baseStart_1770489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770514 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1770514 : Nat := 118140960795 + 1770514 * 2 ^ 59
def prefixEnd_1770514 : Nat := 4983230072969 + 3 ^ 40 * 1770514 * 2
def baseEnd_1770514 : Nat := 909124687514591089532561

theorem tailTrace_1770514 : CollatzResearch.WordTrace tailWord_1770514 prefixEnd_1770514 909124687514591089532561 := by
  unfold tailWord_1770514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143987676934408140657649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43050633805158421708420397 16143987676934408140657649)
  ·
    refine ⟨12107990757700806105493237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16143987676934408140657649 12107990757700806105493237)
    ·
      refine ⟨1135124133534450572389991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12107990757700806105493237 1135124133534450572389991)
      ·
        refine ⟨1702686200301675858584987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135124133534450572389991 1702686200301675858584987)
        ·
          refine ⟨2554029300452513787877481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702686200301675858584987 2554029300452513787877481)
          ·
            refine ⟨1915521975339385340908111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2554029300452513787877481 1915521975339385340908111)
            ·
              refine ⟨2873282963009078011362167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915521975339385340908111 2873282963009078011362167)
              ·
                refine ⟨4309924444513617017043251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873282963009078011362167 4309924444513617017043251)
                ·
                  refine ⟨6464886666770425525564877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309924444513617017043251 6464886666770425525564877)
                  ·
                    refine ⟨2424332500038909572086829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6464886666770425525564877 2424332500038909572086829)
                    ·
                      refine ⟨909124687514591089532561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424332500038909572086829 909124687514591089532561)
                      ·
                        rfl

theorem cell23_1770514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1770514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770514 prefixEnd_1770514 := by exact prefixLift 1770514
  have htrace : WordTrace (prefixWord ++ tailWord_1770514) baseStart_1770514 baseEnd_1770514 := by
    simpa [prefixWord, tailWord_1770514, baseEnd_1770514] using wordTrace_append hprefix tailTrace_1770514
  have hstable : (prefixWord ++ tailWord_1770514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770514).length < 2 ^ (prefixWord ++ tailWord_1770514).sum := by decide
  have hdescent : baseEnd_1770514 < baseStart_1770514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770520 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1770520 : Nat := 118140960795 + 1770520 * 2 ^ 59
def prefixEnd_1770520 : Nat := 4983230072969 + 3 ^ 40 * 1770520 * 2
def baseEnd_1770520 : Nat := 909127768398518066057533

theorem tailTrace_1770520 : CollatzResearch.WordTrace tailWord_1770520 prefixEnd_1770520 909127768398518066057533 := by
  unfold tailWord_1770520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288084772857947793674507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43050779697143930391566009 32288084772857947793674507)
  ·
    refine ⟨48432127159286921690511761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32288084772857947793674507 48432127159286921690511761)
    ·
      refine ⟨36324095369465191267883821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48432127159286921690511761 36324095369465191267883821)
      ·
        refine ⟨13621535763549446725456433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36324095369465191267883821 13621535763549446725456433)
        ·
          refine ⟨10216151822662085044092325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621535763549446725456433 10216151822662085044092325)
          ·
            refine ⟨1915528466749140945767311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10216151822662085044092325 1915528466749140945767311)
            ·
              refine ⟨2873292700123711418650967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915528466749140945767311 2873292700123711418650967)
              ·
                refine ⟨4309939050185567127976451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873292700123711418650967 4309939050185567127976451)
                ·
                  refine ⟨6464908575278350691964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309939050185567127976451 6464908575278350691964677)
                  ·
                    refine ⟨1212170357864690754743377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6464908575278350691964677 1212170357864690754743377)
                    ·
                      refine ⟨909127768398518066057533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212170357864690754743377 909127768398518066057533)
                      ·
                        rfl

theorem cell23_1770520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1770520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770520 prefixEnd_1770520 := by exact prefixLift 1770520
  have htrace : WordTrace (prefixWord ++ tailWord_1770520) baseStart_1770520 baseEnd_1770520 := by
    simpa [prefixWord, tailWord_1770520, baseEnd_1770520] using wordTrace_append hprefix tailTrace_1770520
  have hstable : (prefixWord ++ tailWord_1770520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770520).length < 2 ^ (prefixWord ++ tailWord_1770520).sum := by decide
  have hdescent : baseEnd_1770520 < baseStart_1770520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770539 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 7]
def baseStart_1770539 : Nat := 118140960795 + 1770539 * 2 ^ 59
def prefixEnd_1770539 : Nat := 4983230072969 + 3 ^ 40 * 1770539 * 2
def baseEnd_1770539 : Nat := 303045841510317830573315

theorem tailTrace_1770539 : CollatzResearch.WordTrace tailWord_1770539 prefixEnd_1770539 303045841510317830573315 := by
  unfold tailWord_1770539
  simp only [CollatzResearch.WordTrace]
  refine ⟨64576862532647061832290671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43051241688431374554860447 64576862532647061832290671)
  ·
    refine ⟨96865293798970592748436007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64576862532647061832290671 96865293798970592748436007)
    ·
      refine ⟨145297940698455889122654011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96865293798970592748436007 145297940698455889122654011)
      ·
        refine ⟨217946911047683833683981017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145297940698455889122654011 217946911047683833683981017)
        ·
          refine ⟨163460183285762875262985763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217946911047683833683981017 163460183285762875262985763)
          ·
            refine ⟨245190274928644312894478645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163460183285762875262985763 245190274928644312894478645)
            ·
              refine ⟨22986588274560404333857373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245190274928644312894478645 22986588274560404333857373)
              ·
                refine ⟨8619970602960151625196515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22986588274560404333857373 8619970602960151625196515)
                ·
                  refine ⟨12929955904440227437794773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619970602960151625196515 12929955904440227437794773)
                  ·
                    refine ⟨303045841510317830573315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12929955904440227437794773 303045841510317830573315)
                    ·
                      rfl

theorem cell23_1770539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_1770539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770539 prefixEnd_1770539 := by exact prefixLift 1770539
  have htrace : WordTrace (prefixWord ++ tailWord_1770539) baseStart_1770539 baseEnd_1770539 := by
    simpa [prefixWord, tailWord_1770539, baseEnd_1770539] using wordTrace_append hprefix tailTrace_1770539
  have hstable : (prefixWord ++ tailWord_1770539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770539).length < 2 ^ (prefixWord ++ tailWord_1770539).sum := by decide
  have hdescent : baseEnd_1770539 < baseStart_1770539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770556 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1770556 : Nat := 118140960795 + 1770556 * 2 ^ 59
def prefixEnd_1770556 : Nat := 4983230072969 + 3 ^ 40 * 1770556 * 2
def baseEnd_1770556 : Nat := 303048751234026641735789

theorem tailTrace_1770556 : CollatzResearch.WordTrace tailWord_1770556 prefixEnd_1770556 303048751234026641735789 := by
  unfold tailWord_1770556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288741286792736867829761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43051655049056982490439681 32288741286792736867829761)
  ·
    refine ⟨24216555965094552650872321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32288741286792736867829761 24216555965094552650872321)
    ·
      refine ⟨18162416973820914488154241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24216555965094552650872321 18162416973820914488154241)
      ·
        refine ⟨13621812730365685866115681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18162416973820914488154241 13621812730365685866115681)
        ·
          refine ⟨10216359547774264399586761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621812730365685866115681 10216359547774264399586761)
          ·
            refine ⟨7662269660830698299690071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10216359547774264399586761 7662269660830698299690071)
            ·
              refine ⟨11493404491246047449535107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7662269660830698299690071 11493404491246047449535107)
              ·
                refine ⟨17240106736869071174302661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493404491246047449535107 17240106736869071174302661)
                ·
                  refine ⟨3232520013162950845181749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17240106736869071174302661 3232520013162950845181749)
                  ·
                    refine ⟨303048751234026641735789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3232520013162950845181749 303048751234026641735789)
                    ·
                      rfl

theorem cell23_1770556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1770556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770556 prefixEnd_1770556 := by exact prefixLift 1770556
  have htrace : WordTrace (prefixWord ++ tailWord_1770556) baseStart_1770556 baseEnd_1770556 := by
    simpa [prefixWord, tailWord_1770556, baseEnd_1770556] using wordTrace_append hprefix tailTrace_1770556
  have hstable : (prefixWord ++ tailWord_1770556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770556).length < 2 ^ (prefixWord ++ tailWord_1770556).sum := by decide
  have hdescent : baseEnd_1770556 < baseStart_1770556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770569 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_1770569 : Nat := 118140960795 + 1770569 * 2 ^ 59
def prefixEnd_1770569 : Nat := 4983230072969 + 3 ^ 40 * 1770569 * 2
def baseEnd_1770569 : Nat := 303050976316862791448269

theorem tailTrace_1770569 : CollatzResearch.WordTrace tailWord_1770569 prefixEnd_1770569 303050976316862791448269 := by
  unfold tailWord_1770569
  simp only [CollatzResearch.WordTrace]
  refine ⟨64577956722538376955882761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43051971148358917970588507 64577956722538376955882761)
  ·
    refine ⟨48433467541903782716912071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64577956722538376955882761 48433467541903782716912071)
    ·
      refine ⟨72650201312855674075368107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48433467541903782716912071 72650201312855674075368107)
      ·
        refine ⟨108975301969283511113052161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72650201312855674075368107 108975301969283511113052161)
        ·
          refine ⟨81731476476962633334789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108975301969283511113052161 81731476476962633334789121)
          ·
            refine ⟨61298607357721975001091841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81731476476962633334789121 61298607357721975001091841)
            ·
              refine ⟨45973955518291481250818881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61298607357721975001091841 45973955518291481250818881)
              ·
                refine ⟨34480466638718610938114161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45973955518291481250818881 34480466638718610938114161)
                ·
                  refine ⟨25860349979038958203585621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34480466638718610938114161 25860349979038958203585621)
                  ·
                    refine ⟨303050976316862791448269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25860349979038958203585621 303050976316862791448269)
                    ·
                      rfl

theorem cell23_1770569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_1770569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770569 prefixEnd_1770569 := by exact prefixLift 1770569
  have htrace : WordTrace (prefixWord ++ tailWord_1770569) baseStart_1770569 baseEnd_1770569 := by
    simpa [prefixWord, tailWord_1770569, baseEnd_1770569] using wordTrace_append hprefix tailTrace_1770569
  have hstable : (prefixWord ++ tailWord_1770569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770569).length < 2 ^ (prefixWord ++ tailWord_1770569).sum := by decide
  have hdescent : baseEnd_1770569 < baseStart_1770569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770616 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 6]
def baseStart_1770616 : Nat := 118140960795 + 1770616 * 2 ^ 59
def prefixEnd_1770616 : Nat := 4983230072969 + 3 ^ 40 * 1770616 * 2
def baseEnd_1770616 : Nat := 101019673615705521161899

theorem tailTrace_1770616 : CollatzResearch.WordTrace tailWord_1770616 prefixEnd_1770616 101019673615705521161899 := by
  unfold tailWord_1770616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289835476684051991421851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43053113968912069321895801 32289835476684051991421851)
  ·
    refine ⟨48434753215026077987132777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32289835476684051991421851 48434753215026077987132777)
    ·
      refine ⟨36326064911269558490349583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48434753215026077987132777 36326064911269558490349583)
      ·
        refine ⟨54489097366904337735524375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36326064911269558490349583 54489097366904337735524375)
        ·
          refine ⟨81733646050356506603286563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54489097366904337735524375 81733646050356506603286563)
          ·
            refine ⟨122600469075534759904929845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81733646050356506603286563 122600469075534759904929845)
            ·
              refine ⟨11493793975831383741087173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122600469075534759904929845 11493793975831383741087173)
              ·
                refine ⟨2155086370468384451453845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11493793975831383741087173 2155086370468384451453845)
                ·
                  refine ⟨101019673615705521161899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2155086370468384451453845 101019673615705521161899)
                  ·
                    rfl

theorem cell23_1770616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_1770616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770616 prefixEnd_1770616 := by exact prefixLift 1770616
  have htrace : WordTrace (prefixWord ++ tailWord_1770616) baseStart_1770616 baseEnd_1770616 := by
    simpa [prefixWord, tailWord_1770616, baseEnd_1770616] using wordTrace_append hprefix tailTrace_1770616
  have hstable : (prefixWord ++ tailWord_1770616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770616).length < 2 ^ (prefixWord ++ tailWord_1770616).sum := by decide
  have hdescent : baseEnd_1770616 < baseStart_1770616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770620 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1770620 : Nat := 118140960795 + 1770620 * 2 ^ 59
def prefixEnd_1770620 : Nat := 4983230072969 + 3 ^ 40 * 1770620 * 2
def baseEnd_1770620 : Nat := 303059705487989224935691

theorem tailTrace_1770620 : CollatzResearch.WordTrace tailWord_1770620 prefixEnd_1770620 303059705487989224935691 := by
  unfold tailWord_1770620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289908422676806332994657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43053211230235741777326209 32289908422676806332994657)
  ·
    refine ⟨24217431317007604749745993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32289908422676806332994657 24217431317007604749745993)
    ·
      refine ⟨18163073487755703562309495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24217431317007604749745993 18163073487755703562309495)
      ·
        refine ⟨27244610231633555343464243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18163073487755703562309495 27244610231633555343464243)
        ·
          refine ⟨40866915347450333015196365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27244610231633555343464243 40866915347450333015196365)
          ·
            refine ⟨15325093255293874880698637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40866915347450333015196365 15325093255293874880698637)
            ·
              refine ⟨5746909970735203080261989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15325093255293874880698637 5746909970735203080261989)
              ·
                refine ⟨1077545619512850577549123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5746909970735203080261989 1077545619512850577549123)
                ·
                  refine ⟨1616318429269275866323685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077545619512850577549123 1616318429269275866323685)
                  ·
                    refine ⟨303059705487989224935691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616318429269275866323685 303059705487989224935691)
                    ·
                      rfl

theorem cell23_1770620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1770620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770620 prefixEnd_1770620 := by exact prefixLift 1770620
  have htrace : WordTrace (prefixWord ++ tailWord_1770620) baseStart_1770620 baseEnd_1770620 := by
    simpa [prefixWord, tailWord_1770620, baseEnd_1770620] using wordTrace_append hprefix tailTrace_1770620
  have hstable : (prefixWord ++ tailWord_1770620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770620).length < 2 ^ (prefixWord ++ tailWord_1770620).sum := by decide
  have hdescent : baseEnd_1770620 < baseStart_1770620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770643 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 3]
def baseStart_1770643 : Nat := 118140960795 + 1770643 * 2 ^ 59
def prefixEnd_1770643 : Nat := 4983230072969 + 3 ^ 40 * 1770643 * 2
def baseEnd_1770643 : Nat := 909190926519021084819467

theorem tailTrace_1770643 : CollatzResearch.WordTrace tailWord_1770643 prefixEnd_1770643 909190926519021084819467 := by
  unfold tailWord_1770643
  simp only [CollatzResearch.WordTrace]
  refine ⟨64580655724270287594076583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43053770482846858396051055 64580655724270287594076583)
  ·
    refine ⟨96870983586405431391114875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64580655724270287594076583 96870983586405431391114875)
    ·
      refine ⟨145306475379608147086672313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96870983586405431391114875 145306475379608147086672313)
      ·
        refine ⟨108979856534706110315004235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145306475379608147086672313 108979856534706110315004235)
        ·
          refine ⟨163469784802059165472506353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108979856534706110315004235 163469784802059165472506353)
          ·
            refine ⟨122602338601544374104379765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163469784802059165472506353 122602338601544374104379765)
            ·
              refine ⟨11493969243894785072285603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122602338601544374104379765 11493969243894785072285603)
              ·
                refine ⟨17240953865842177608428405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11493969243894785072285603 17240953865842177608428405)
                ·
                  refine ⟨1616339424922704150790163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17240953865842177608428405 1616339424922704150790163)
                  ·
                    refine ⟨2424509137384056226185245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616339424922704150790163 2424509137384056226185245)
                    ·
                      refine ⟨909190926519021084819467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424509137384056226185245 909190926519021084819467)
                      ·
                        rfl

theorem cell23_1770643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_1770643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770643 prefixEnd_1770643 := by exact prefixLift 1770643
  have htrace : WordTrace (prefixWord ++ tailWord_1770643) baseStart_1770643 baseEnd_1770643 := by
    simpa [prefixWord, tailWord_1770643, baseEnd_1770643] using wordTrace_append hprefix tailTrace_1770643
  have hstable : (prefixWord ++ tailWord_1770643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770643).length < 2 ^ (prefixWord ++ tailWord_1770643).sum := by decide
  have hdescent : baseEnd_1770643 < baseStart_1770643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770654 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1770654 : Nat := 118140960795 + 1770654 * 2 ^ 59
def prefixEnd_1770654 : Nat := 4983230072969 + 3 ^ 40 * 1770654 * 2
def baseEnd_1770654 : Nat := 303065524935406847260639

theorem tailTrace_1770654 : CollatzResearch.WordTrace tailWord_1770654 prefixEnd_1770654 303065524935406847260639 := by
  unfold tailWord_1770654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072632115903804559090877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43054037951486957648484677 8072632115903804559090877)
  ·
    refine ⟨3027237043463926709659079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8072632115903804559090877 3027237043463926709659079)
    ·
      refine ⟨4540855565195890064488619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027237043463926709659079 4540855565195890064488619)
      ·
        refine ⟨6811283347793835096732929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540855565195890064488619 6811283347793835096732929)
        ·
          refine ⟨5108462510845376322549697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6811283347793835096732929 5108462510845376322549697)
          ·
            refine ⟨3831346883134032241912273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5108462510845376322549697 3831346883134032241912273)
            ·
              refine ⟨2873510162350524181434205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831346883134032241912273 2873510162350524181434205)
              ·
                refine ⟨1077566310881446568037827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873510162350524181434205 1077566310881446568037827)
                ·
                  refine ⟨1616349466322169852056741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077566310881446568037827 1616349466322169852056741)
                  ·
                    refine ⟨303065524935406847260639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616349466322169852056741 303065524935406847260639)
                    ·
                      rfl

theorem cell23_1770654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1770654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770654 prefixEnd_1770654 := by exact prefixLift 1770654
  have htrace : WordTrace (prefixWord ++ tailWord_1770654) baseStart_1770654 baseEnd_1770654 := by
    simpa [prefixWord, tailWord_1770654, baseEnd_1770654] using wordTrace_append hprefix tailTrace_1770654
  have hstable : (prefixWord ++ tailWord_1770654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770654).length < 2 ^ (prefixWord ++ tailWord_1770654).sum := by decide
  have hdescent : baseEnd_1770654 < baseStart_1770654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770720 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_1770720 : Nat := 118140960795 + 1770720 * 2 ^ 59
def prefixEnd_1770720 : Nat := 4983230072969 + 3 ^ 40 * 1770720 * 2
def baseEnd_1770720 : Nat := 909230464529417283556613

theorem tailTrace_1770720 : CollatzResearch.WordTrace tailWord_1770720 prefixEnd_1770720 909230464529417283556613 := by
  unfold tailWord_1770720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32291732072495664872314807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43055642763327553163086409 32291732072495664872314807)
  ·
    refine ⟨48437598108743497308472211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32291732072495664872314807 48437598108743497308472211)
    ·
      refine ⟨72656397163115245962708317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48437598108743497308472211 72656397163115245962708317)
      ·
        refine ⟨27246148936168217236015619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72656397163115245962708317 27246148936168217236015619)
        ·
          refine ⟨40869223404252325854023429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27246148936168217236015619 40869223404252325854023429)
          ·
            refine ⟨7662979388297311097629393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40869223404252325854023429 7662979388297311097629393)
            ·
              refine ⟨5747234541222983323222045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7662979388297311097629393 5747234541222983323222045)
              ·
                refine ⟨2155212952958618746208267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5747234541222983323222045 2155212952958618746208267)
                ·
                  refine ⟨3232819429437928119312401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155212952958618746208267 3232819429437928119312401)
                  ·
                    refine ⟨2424614572078446089484301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3232819429437928119312401 2424614572078446089484301)
                    ·
                      refine ⟨909230464529417283556613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424614572078446089484301 909230464529417283556613)
                      ·
                        rfl

theorem cell23_1770720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_1770720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770720 prefixEnd_1770720 := by exact prefixLift 1770720
  have htrace : WordTrace (prefixWord ++ tailWord_1770720) baseStart_1770720 baseEnd_1770720 := by
    simpa [prefixWord, tailWord_1770720, baseEnd_1770720] using wordTrace_append hprefix tailTrace_1770720
  have hstable : (prefixWord ++ tailWord_1770720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770720).length < 2 ^ (prefixWord ++ tailWord_1770720).sum := by decide
  have hdescent : baseEnd_1770720 < baseStart_1770720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770734 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_1770734 : Nat := 118140960795 + 1770734 * 2 ^ 59
def prefixEnd_1770734 : Nat := 4983230072969 + 3 ^ 40 * 1770734 * 2
def baseEnd_1770734 : Nat := 909237653258580228781549

theorem tailTrace_1770734 : CollatzResearch.WordTrace tailWord_1770734 prefixEnd_1770734 909237653258580228781549 := by
  unfold tailWord_1770734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072996845867576266954907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43055983177960406757092837 8072996845867576266954907)
  ·
    refine ⟨12109495268801364400432361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8072996845867576266954907 12109495268801364400432361)
    ·
      refine ⟨9082121451601023300324271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12109495268801364400432361 9082121451601023300324271)
      ·
        refine ⟨13623182177401534950486407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9082121451601023300324271 13623182177401534950486407)
        ·
          refine ⟨20434773266102302425729611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13623182177401534950486407 20434773266102302425729611)
          ·
            refine ⟨30652159899153453638594417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20434773266102302425729611 30652159899153453638594417)
            ·
              refine ⟨22989119924365090228945813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30652159899153453638594417 22989119924365090228945813)
              ·
                refine ⟨1077614996454613604481835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22989119924365090228945813 1077614996454613604481835)
                ·
                  refine ⟨1616422494681920406722753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077614996454613604481835 1616422494681920406722753)
                  ·
                    refine ⟨1212316871011440305042065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616422494681920406722753 1212316871011440305042065)
                    ·
                      refine ⟨909237653258580228781549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212316871011440305042065 909237653258580228781549)
                      ·
                        rfl

theorem cell23_1770734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_1770734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770734 prefixEnd_1770734 := by exact prefixLift 1770734
  have htrace : WordTrace (prefixWord ++ tailWord_1770734) baseStart_1770734 baseEnd_1770734 := by
    simpa [prefixWord, tailWord_1770734, baseEnd_1770734] using wordTrace_append hprefix tailTrace_1770734
  have hstable : (prefixWord ++ tailWord_1770734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770734).length < 2 ^ (prefixWord ++ tailWord_1770734).sum := by decide
  have hdescent : baseEnd_1770734 < baseStart_1770734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770784 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1770784 : Nat := 118140960795 + 1770784 * 2 ^ 59
def prefixEnd_1770784 : Nat := 4983230072969 + 3 ^ 40 * 1770784 * 2
def baseEnd_1770784 : Nat := 909263327291305033156319

theorem tailTrace_1770784 : CollatzResearch.WordTrace tailWord_1770784 prefixEnd_1770784 909263327291305033156319 := by
  unfold tailWord_1770784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292899208379734337479703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43057198944506312449972937 32292899208379734337479703)
  ·
    refine ⟨48439348812569601506219555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32292899208379734337479703 48439348812569601506219555)
    ·
      refine ⟨72659023218854402259329333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48439348812569601506219555 72659023218854402259329333)
      ·
        refine ⟨6811783426767600211812125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72659023218854402259329333 6811783426767600211812125)
        ·
          refine ⟨2554418785037850079429547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6811783426767600211812125 2554418785037850079429547)
          ·
            refine ⟨3831628177556775119144321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554418785037850079429547 3831628177556775119144321)
            ·
              refine ⟨2873721133167581339358241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831628177556775119144321 2873721133167581339358241)
              ·
                refine ⟨2155290849875686004518681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873721133167581339358241 2155290849875686004518681)
                ·
                  refine ⟨1616468137406764503389011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155290849875686004518681 1616468137406764503389011)
                  ·
                    refine ⟨2424702206110146755083517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616468137406764503389011 2424702206110146755083517)
                    ·
                      refine ⟨909263327291305033156319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424702206110146755083517 909263327291305033156319)
                      ·
                        rfl

theorem cell23_1770784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1770784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770784 prefixEnd_1770784 := by exact prefixLift 1770784
  have htrace : WordTrace (prefixWord ++ tailWord_1770784) baseStart_1770784 baseEnd_1770784 := by
    simpa [prefixWord, tailWord_1770784, baseEnd_1770784] using wordTrace_append hprefix tailTrace_1770784
  have hstable : (prefixWord ++ tailWord_1770784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770784).length < 2 ^ (prefixWord ++ tailWord_1770784).sum := by decide
  have hdescent : baseEnd_1770784 < baseStart_1770784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770803 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_1770803 : Nat := 118140960795 + 1770803 * 2 ^ 59
def prefixEnd_1770803 : Nat := 4983230072969 + 3 ^ 40 * 1770803 * 2
def baseEnd_1770803 : Nat := 909273083423740458818731

theorem tailTrace_1770803 : CollatzResearch.WordTrace tailWord_1770803 prefixEnd_1770803 909273083423740458818731 := by
  unfold tailWord_1770803
  simp only [CollatzResearch.WordTrace]
  refine ⟨64586491403690634919901063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43057660935793756613267375 64586491403690634919901063)
  ·
    refine ⟨96879737105535952379851595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64586491403690634919901063 96879737105535952379851595)
    ·
      refine ⟨145319605658303928569777393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96879737105535952379851595 145319605658303928569777393)
      ·
        refine ⟨108989704243727946427333045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145319605658303928569777393 108989704243727946427333045)
        ·
          refine ⟨10217784772849494977562473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108989704243727946427333045 10217784772849494977562473)
          ·
            refine ⟨7663338579637121233171855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217784772849494977562473 7663338579637121233171855)
            ·
              refine ⟨11495007869455681849757783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663338579637121233171855 11495007869455681849757783)
              ·
                refine ⟨17242511804183522774636675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495007869455681849757783 17242511804183522774636675)
                ·
                  refine ⟨25863767706275284161955013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17242511804183522774636675 25863767706275284161955013)
                  ·
                    refine ⟨4849456444926615780366565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25863767706275284161955013 4849456444926615780366565)
                    ·
                      refine ⟨909273083423740458818731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4849456444926615780366565 909273083423740458818731)
                      ·
                        rfl

theorem cell23_1770803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_1770803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770803 prefixEnd_1770803 := by exact prefixLift 1770803
  have htrace : WordTrace (prefixWord ++ tailWord_1770803) baseStart_1770803 baseEnd_1770803 := by
    simpa [prefixWord, tailWord_1770803, baseEnd_1770803] using wordTrace_append hprefix tailTrace_1770803
  have hstable : (prefixWord ++ tailWord_1770803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770803).length < 2 ^ (prefixWord ++ tailWord_1770803).sum := by decide
  have hdescent : baseEnd_1770803 < baseStart_1770803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770853 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1770853 : Nat := 118140960795 + 1770853 * 2 ^ 59
def prefixEnd_1770853 : Nat := 4983230072969 + 3 ^ 40 * 1770853 * 2
def baseEnd_1770853 : Nat := 909298757456465263193501

theorem tailTrace_1770853 : CollatzResearch.WordTrace tailWord_1770853 prefixEnd_1770853 909298757456465263193501 := by
  unfold tailWord_1770853
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588315053509493459221213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43058876702339662306147475 64588315053509493459221213)
  ·
    refine ⟨24220618145066060047207955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64588315053509493459221213 24220618145066060047207955)
    ·
      refine ⟨36330927217599090070811933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24220618145066060047207955 36330927217599090070811933)
      ·
        refine ⟨13624097706599658776554475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36330927217599090070811933 13624097706599658776554475)
        ·
          refine ⟨20436146559899488164831713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13624097706599658776554475 20436146559899488164831713)
          ·
            refine ⟨15327109919924616123623785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20436146559899488164831713 15327109919924616123623785)
            ·
              refine ⟨11495332439943462092717839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15327109919924616123623785 11495332439943462092717839)
              ·
                refine ⟨17242998659915193139076759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11495332439943462092717839 17242998659915193139076759)
                ·
                  refine ⟨25864497989872789708615139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17242998659915193139076759 25864497989872789708615139)
                  ·
                    refine ⟨38796746984809184562922709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25864497989872789708615139 38796746984809184562922709)
                    ·
                      refine ⟨909298757456465263193501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38796746984809184562922709 909298757456465263193501)
                      ·
                        rfl

theorem cell23_1770853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1770853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770853 prefixEnd_1770853 := by exact prefixLift 1770853
  have htrace : WordTrace (prefixWord ++ tailWord_1770853) baseStart_1770853 baseEnd_1770853 := by
    simpa [prefixWord, tailWord_1770853, baseEnd_1770853] using wordTrace_append hprefix tailTrace_1770853
  have hstable : (prefixWord ++ tailWord_1770853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770853).length < 2 ^ (prefixWord ++ tailWord_1770853).sum := by decide
  have hdescent : baseEnd_1770853 < baseStart_1770853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770858 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1770858 : Nat := 118140960795 + 1770858 * 2 ^ 59
def prefixEnd_1770858 : Nat := 4983230072969 + 3 ^ 40 * 1770858 * 2
def baseEnd_1770858 : Nat := 909301324859737743630979

theorem tailTrace_1770858 : CollatzResearch.WordTrace tailWord_1770858 prefixEnd_1770858 909301324859737743630979 := by
  unfold tailWord_1770858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147124354622844828288307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43058998278994252875435485 16147124354622844828288307)
  ·
    refine ⟨24220686531934267242432461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16147124354622844828288307 24220686531934267242432461)
    ·
      refine ⟨9082757449475350215912173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24220686531934267242432461 9082757449475350215912173)
      ·
        refine ⟨3406034043553256330967065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9082757449475350215912173 3406034043553256330967065)
        ·
          refine ⟨2554525532664942248225299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406034043553256330967065 2554525532664942248225299)
          ·
            refine ⟨3831788298997413372337949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554525532664942248225299 3831788298997413372337949)
            ·
              refine ⟨1436920612124030014626731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3831788298997413372337949 1436920612124030014626731)
              ·
                refine ⟨2155380918186045021940097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436920612124030014626731 2155380918186045021940097)
                ·
                  refine ⟨1616535688639533766455073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155380918186045021940097 1616535688639533766455073)
                  ·
                    refine ⟨1212401766479650324841305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616535688639533766455073 1212401766479650324841305)
                    ·
                      refine ⟨909301324859737743630979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212401766479650324841305 909301324859737743630979)
                      ·
                        rfl

theorem cell23_1770858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1770858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770858 prefixEnd_1770858 := by exact prefixLift 1770858
  have htrace : WordTrace (prefixWord ++ tailWord_1770858) baseStart_1770858 baseEnd_1770858 := by
    simpa [prefixWord, tailWord_1770858, baseEnd_1770858] using wordTrace_append hprefix tailTrace_1770858
  have hstable : (prefixWord ++ tailWord_1770858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770858).length < 2 ^ (prefixWord ++ tailWord_1770858).sum := by decide
  have hdescent : baseEnd_1770858 < baseStart_1770858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770863 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_1770863 : Nat := 118140960795 + 1770863 * 2 ^ 59
def prefixEnd_1770863 : Nat := 4983230072969 + 3 ^ 40 * 1770863 * 2
def baseEnd_1770863 : Nat := 909303892263010224068455

theorem tailTrace_1770863 : CollatzResearch.WordTrace tailWord_1770863 prefixEnd_1770863 909303892263010224068455 := by
  unfold tailWord_1770863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64588679783473265167085243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43059119855648843444723495 64588679783473265167085243)
  ·
    refine ⟨96883019675209897750627865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64588679783473265167085243 96883019675209897750627865)
    ·
      refine ⟨72662264756407423312970899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96883019675209897750627865 72662264756407423312970899)
      ·
        refine ⟨108993397134611134969456349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72662264756407423312970899 108993397134611134969456349)
        ·
          refine ⟨40872523925479175613546131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108993397134611134969456349 40872523925479175613546131)
          ·
            refine ⟨61308785888218763420319197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40872523925479175613546131 61308785888218763420319197)
            ·
              refine ⟨22990794708082036282619699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61308785888218763420319197 22990794708082036282619699)
              ·
                refine ⟨34486192062123054423929549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22990794708082036282619699 34486192062123054423929549)
                ·
                  refine ⟨12932322023296145408973581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34486192062123054423929549 12932322023296145408973581)
                  ·
                    refine ⟨4849620758736054528365093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12932322023296145408973581 4849620758736054528365093)
                    ·
                      refine ⟨909303892263010224068455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4849620758736054528365093 909303892263010224068455)
                      ·
                        rfl

theorem cell23_1770863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_1770863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770863 prefixEnd_1770863 := by exact prefixLift 1770863
  have htrace : WordTrace (prefixWord ++ tailWord_1770863) baseStart_1770863 baseEnd_1770863 := by
    simpa [prefixWord, tailWord_1770863, baseEnd_1770863] using wordTrace_append hprefix tailTrace_1770863
  have hstable : (prefixWord ++ tailWord_1770863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770863).length < 2 ^ (prefixWord ++ tailWord_1770863).sum := by decide
  have hdescent : baseEnd_1770863 < baseStart_1770863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770880 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2]
def baseStart_1770880 : Nat := 118140960795 + 1770880 * 2 ^ 59
def prefixEnd_1770880 : Nat := 4983230072969 + 3 ^ 40 * 1770880 * 2
def baseEnd_1770880 : Nat := 909312621434136657555877

theorem tailTrace_1770880 : CollatzResearch.WordTrace tailWord_1770880 prefixEnd_1770880 909312621434136657555877 := by
  unfold tailWord_1770880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32294649912205838535227047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43059533216274451380302729 32294649912205838535227047)
  ·
    refine ⟨48441974868308757802840571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32294649912205838535227047 48441974868308757802840571)
    ·
      refine ⟨72662962302463136704260857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48441974868308757802840571 72662962302463136704260857)
      ·
        refine ⟨54497221726847352528195643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72662962302463136704260857 54497221726847352528195643)
        ·
          refine ⟨81745832590271028792293465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54497221726847352528195643 81745832590271028792293465)
          ·
            refine ⟨61309374442703271594220099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81745832590271028792293465 61309374442703271594220099)
            ·
              refine ⟨91964061664054907391330149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61309374442703271594220099 91964061664054907391330149)
              ·
                refine ⟨17243261562010295135874403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91964061664054907391330149 17243261562010295135874403)
                ·
                  refine ⟨25864892343015442703811605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17243261562010295135874403 25864892343015442703811605)
                  ·
                    refine ⟨1212416828578848876741169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25864892343015442703811605 1212416828578848876741169)
                    ·
                      refine ⟨909312621434136657555877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212416828578848876741169 909312621434136657555877)
                      ·
                        rfl

theorem cell23_1770880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_1770880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770880 prefixEnd_1770880 := by exact prefixLift 1770880
  have htrace : WordTrace (prefixWord ++ tailWord_1770880) baseStart_1770880 baseEnd_1770880 := by
    simpa [prefixWord, tailWord_1770880, baseEnd_1770880] using wordTrace_append hprefix tailTrace_1770880
  have hstable : (prefixWord ++ tailWord_1770880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770880).length < 2 ^ (prefixWord ++ tailWord_1770880).sum := by decide
  have hdescent : baseEnd_1770880 < baseStart_1770880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770881 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 5]
def baseStart_1770881 : Nat := 118140960795 + 1770881 * 2 ^ 59
def prefixEnd_1770881 : Nat := 4983230072969 + 3 ^ 40 * 1770881 * 2
def baseEnd_1770881 : Nat := 101034792768310128182597

theorem tailTrace_1770881 : CollatzResearch.WordTrace tailWord_1770881 prefixEnd_1770881 101034792768310128182597 := by
  unfold tailWord_1770881
  simp only [CollatzResearch.WordTrace]
  refine ⟨64589336297408054241240497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43059557531605369494160331 64589336297408054241240497)
  ·
    refine ⟨48442002223056040680930373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64589336297408054241240497 48442002223056040680930373)
    ·
      refine ⟨9082875416823007627674445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48442002223056040680930373 9082875416823007627674445)
      ·
        refine ⟨3406078281308627860377917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9082875416823007627674445 3406078281308627860377917)
        ·
          refine ⟨1277279355490735447641719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3406078281308627860377917 1277279355490735447641719)
          ·
            refine ⟨1915919033236103171462579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277279355490735447641719 1915919033236103171462579)
            ·
              refine ⟨2873878549854154757193869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915919033236103171462579 2873878549854154757193869)
              ·
                refine ⟨1077704456195308033947701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873878549854154757193869 1077704456195308033947701)
                ·
                  refine ⟨101034792768310128182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1077704456195308033947701 101034792768310128182597)
                  ·
                    rfl

theorem cell23_1770881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 5].length) (baseStart_1770881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770881 prefixEnd_1770881 := by exact prefixLift 1770881
  have htrace : WordTrace (prefixWord ++ tailWord_1770881) baseStart_1770881 baseEnd_1770881 := by
    simpa [prefixWord, tailWord_1770881, baseEnd_1770881] using wordTrace_append hprefix tailTrace_1770881
  have hstable : (prefixWord ++ tailWord_1770881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770881).length < 2 ^ (prefixWord ++ tailWord_1770881).sum := by decide
  have hdescent : baseEnd_1770881 < baseStart_1770881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770943 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1770943 : Nat := 118140960795 + 1770943 * 2 ^ 59
def prefixEnd_1770943 : Nat := 4983230072969 + 3 ^ 40 * 1770943 * 2
def baseEnd_1770943 : Nat := 909344970715369911068087

theorem tailTrace_1770943 : CollatzResearch.WordTrace tailWord_1770943 prefixEnd_1770943 909344970715369911068087 := by
  unfold tailWord_1770943
  simp only [CollatzResearch.WordTrace]
  refine ⟨64591597623183438829997483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43061065082122292553331655 64591597623183438829997483)
  ·
    refine ⟨96887396434775158244996225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64591597623183438829997483 96887396434775158244996225)
    ·
      refine ⟨72665547326081368683747169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96887396434775158244996225 72665547326081368683747169)
      ·
        refine ⟨54499160494561026512810377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72665547326081368683747169 54499160494561026512810377)
        ·
          refine ⟨40874370370920769884607783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54499160494561026512810377 40874370370920769884607783)
          ·
            refine ⟨61311555556381154826911675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40874370370920769884607783 61311555556381154826911675)
            ·
              refine ⟨91967333334571732240367513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61311555556381154826911675 91967333334571732240367513)
              ·
                refine ⟨68975500000928799180275635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91967333334571732240367513 68975500000928799180275635)
                ·
                  refine ⟨103463250001393198770413453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68975500000928799180275635 103463250001393198770413453)
                  ·
                    refine ⟨38798718750522449538905045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103463250001393198770413453 38798718750522449538905045)
                    ·
                      refine ⟨909344970715369911068087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38798718750522449538905045 909344970715369911068087)
                      ·
                        rfl

theorem cell23_1770943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1770943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770943 prefixEnd_1770943 := by exact prefixLift 1770943
  have htrace : WordTrace (prefixWord ++ tailWord_1770943) baseStart_1770943 baseEnd_1770943 := by
    simpa [prefixWord, tailWord_1770943, baseEnd_1770943] using wordTrace_append hprefix tailTrace_1770943
  have hstable : (prefixWord ++ tailWord_1770943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770943).length < 2 ^ (prefixWord ++ tailWord_1770943).sum := by decide
  have hdescent : baseEnd_1770943 < baseStart_1770943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1770998 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1770998 : Nat := 118140960795 + 1770998 * 2 ^ 59
def prefixEnd_1770998 : Nat := 4983230072969 + 3 ^ 40 * 1770998 * 2
def baseEnd_1770998 : Nat := 909373212151367195880335

theorem tailTrace_1770998 : CollatzResearch.WordTrace tailWord_1770998 prefixEnd_1770998 909373212151367195880335 := by
  unfold tailWord_1770998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037100227374011451453103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43062402425322788815499765 4037100227374011451453103)
  ·
    refine ⟨6055650341061017177179655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037100227374011451453103 6055650341061017177179655)
    ·
      refine ⟨9083475511591525765769483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6055650341061017177179655 9083475511591525765769483)
      ·
        refine ⟨13625213267387288648654225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9083475511591525765769483 13625213267387288648654225)
        ·
          refine ⟨10218909950540466486490669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13625213267387288648654225 10218909950540466486490669)
          ·
            refine ⟨3832091231452674932434001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10218909950540466486490669 3832091231452674932434001)
            ·
              refine ⟨2874068423589506199325501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832091231452674932434001 2874068423589506199325501)
              ·
                refine ⟨1077775658846064824747063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874068423589506199325501 1077775658846064824747063)
                ·
                  refine ⟨1616663488269097237120595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077775658846064824747063 1616663488269097237120595)
                  ·
                    refine ⟨2424995232403645855680893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616663488269097237120595 2424995232403645855680893)
                    ·
                      refine ⟨909373212151367195880335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2424995232403645855680893 909373212151367195880335)
                      ·
                        rfl

theorem cell23_1770998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1770998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1770998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1770998 prefixEnd_1770998 := by exact prefixLift 1770998
  have htrace : WordTrace (prefixWord ++ tailWord_1770998) baseStart_1770998 baseEnd_1770998 := by
    simpa [prefixWord, tailWord_1770998, baseEnd_1770998] using wordTrace_append hprefix tailTrace_1770998
  have hstable : (prefixWord ++ tailWord_1770998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1770998).length < 2 ^ (prefixWord ++ tailWord_1770998).sum := by decide
  have hdescent : baseEnd_1770998 < baseStart_1770998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1770998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771004 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_1771004 : Nat := 118140960795 + 1771004 * 2 ^ 59
def prefixEnd_1771004 : Nat := 4983230072969 + 3 ^ 40 * 1771004 * 2
def baseEnd_1771004 : Nat := 909376293035294172405307

theorem tailTrace_1771004 : CollatzResearch.WordTrace tailWord_1771004 prefixEnd_1771004 909376293035294172405307 := by
  unfold tailWord_1771004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32296911237981223123984033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43062548317308297498645377 32296911237981223123984033)
  ·
    refine ⟨24222683428485917342988025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32296911237981223123984033 24222683428485917342988025)
    ·
      refine ⟨18167012571364438007241019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24222683428485917342988025 18167012571364438007241019)
      ·
        refine ⟨27250518857046657010861529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18167012571364438007241019 27250518857046657010861529)
        ·
          refine ⟨20437889142784992758146147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27250518857046657010861529 20437889142784992758146147)
          ·
            refine ⟨30656833714177489137219221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437889142784992758146147 30656833714177489137219221)
            ·
              refine ⟨1437039080352069803307151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30656833714177489137219221 1437039080352069803307151)
              ·
                refine ⟨2155558620528104704960727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437039080352069803307151 2155558620528104704960727)
                ·
                  refine ⟨3233337930792157057441091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155558620528104704960727 3233337930792157057441091)
                  ·
                    refine ⟨4850006896188235586161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3233337930792157057441091 4850006896188235586161637)
                    ·
                      refine ⟨909376293035294172405307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4850006896188235586161637 909376293035294172405307)
                      ·
                        rfl

theorem cell23_1771004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_1771004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771004 prefixEnd_1771004 := by exact prefixLift 1771004
  have htrace : WordTrace (prefixWord ++ tailWord_1771004) baseStart_1771004 baseEnd_1771004 := by
    simpa [prefixWord, tailWord_1771004, baseEnd_1771004] using wordTrace_append hprefix tailTrace_1771004
  have hstable : (prefixWord ++ tailWord_1771004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771004).length < 2 ^ (prefixWord ++ tailWord_1771004).sum := by decide
  have hdescent : baseEnd_1771004 < baseStart_1771004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771127 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1771127 : Nat := 118140960795 + 1771127 * 2 ^ 59
def prefixEnd_1771127 : Nat := 4983230072969 + 3 ^ 40 * 1771127 * 2
def baseEnd_1771127 : Nat := 909439451155797191167241

theorem tailTrace_1771127 : CollatzResearch.WordTrace tailWord_1771127 prefixEnd_1771127 909439451155797191167241 := by
  unfold tailWord_1771127
  simp only [CollatzResearch.WordTrace]
  refine ⟨64598308654516838254695635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43065539103011225503130423 64598308654516838254695635)
  ·
    refine ⟨96897462981775257382043453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64598308654516838254695635 96897462981775257382043453)
    ·
      refine ⟨36336548618165721518266295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96897462981775257382043453 36336548618165721518266295)
      ·
        refine ⟨54504822927248582277399443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36336548618165721518266295 54504822927248582277399443)
        ·
          refine ⟨81757234390872873416099165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54504822927248582277399443 81757234390872873416099165)
          ·
            refine ⟨30658962896577327531037187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81757234390872873416099165 30658962896577327531037187)
            ·
              refine ⟨45988444344865991296555781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30658962896577327531037187 45988444344865991296555781)
              ·
                refine ⟨8622833314662373368104209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45988444344865991296555781 8622833314662373368104209)
                ·
                  refine ⟨6467124985996780026078157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8622833314662373368104209 6467124985996780026078157)
                  ·
                    refine ⟨2425171869748792509779309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6467124985996780026078157 2425171869748792509779309)
                    ·
                      refine ⟨909439451155797191167241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425171869748792509779309 909439451155797191167241)
                      ·
                        rfl

theorem cell23_1771127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1771127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771127 prefixEnd_1771127 := by exact prefixLift 1771127
  have htrace : WordTrace (prefixWord ++ tailWord_1771127) baseStart_1771127 baseEnd_1771127 := by
    simpa [prefixWord, tailWord_1771127, baseEnd_1771127] using wordTrace_append hprefix tailTrace_1771127
  have hstable : (prefixWord ++ tailWord_1771127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771127).length < 2 ^ (prefixWord ++ tailWord_1771127).sum := by decide
  have hdescent : baseEnd_1771127 < baseStart_1771127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771164 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1771164 : Nat := 118140960795 + 1771164 * 2 ^ 59
def prefixEnd_1771164 : Nat := 4983230072969 + 3 ^ 40 * 1771164 * 2
def baseEnd_1771164 : Nat := 303152816646671182134857

theorem tailTrace_1771164 : CollatzResearch.WordTrace tailWord_1771164 prefixEnd_1771164 303152816646671182134857 := by
  unfold tailWord_1771164
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299829077691396786896273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43066438770255195715861697 32299829077691396786896273)
  ·
    refine ⟨24224871808268547590172205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32299829077691396786896273 24224871808268547590172205)
    ·
      refine ⟨9084326928100705346314577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24224871808268547590172205 9084326928100705346314577)
      ·
        refine ⟨6813245196075529009735933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084326928100705346314577 6813245196075529009735933)
        ·
          refine ⟨2554966948528323378650975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6813245196075529009735933 2554966948528323378650975)
          ·
            refine ⟨3832450422792485067976463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554966948528323378650975 3832450422792485067976463)
            ·
              refine ⟨5748675634188727601964695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832450422792485067976463 5748675634188727601964695)
              ·
                refine ⟨8623013451283091402947043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748675634188727601964695 8623013451283091402947043)
                ·
                  refine ⟨12934520176924637104420565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8623013451283091402947043 12934520176924637104420565)
                  ·
                    refine ⟨303152816646671182134857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12934520176924637104420565 303152816646671182134857)
                    ·
                      rfl

theorem cell23_1771164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1771164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771164 prefixEnd_1771164 := by exact prefixLift 1771164
  have htrace : WordTrace (prefixWord ++ tailWord_1771164) baseStart_1771164 baseEnd_1771164 := by
    simpa [prefixWord, tailWord_1771164, baseEnd_1771164] using wordTrace_append hprefix tailTrace_1771164
  have hstable : (prefixWord ++ tailWord_1771164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771164).length < 2 ^ (prefixWord ++ tailWord_1771164).sum := by decide
  have hdescent : baseEnd_1771164 < baseStart_1771164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771184 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2]
def baseStart_1771184 : Nat := 118140960795 + 1771184 * 2 ^ 59
def prefixEnd_1771184 : Nat := 4983230072969 + 3 ^ 40 * 1771184 * 2
def baseEnd_1771184 : Nat := 909468719553103468154479

theorem tailTrace_1771184 : CollatzResearch.WordTrace tailWord_1771184 prefixEnd_1771184 909468719553103468154479 := by
  unfold tailWord_1771184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300193807655168494760303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43066925076873557993013737 32300193807655168494760303)
  ·
    refine ⟨48450290711482752742140455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32300193807655168494760303 48450290711482752742140455)
    ·
      refine ⟨72675436067224129113210683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48450290711482752742140455 72675436067224129113210683)
      ·
        refine ⟨109013154100836193669816025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72675436067224129113210683 109013154100836193669816025)
        ·
          refine ⟨81759865575627145252362019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109013154100836193669816025 81759865575627145252362019)
          ·
            refine ⟨122639798363440717878543029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81759865575627145252362019 122639798363440717878543029)
            ·
              refine ⟨11497481096572567301113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122639798363440717878543029 11497481096572567301113409)
              ·
                refine ⟨8623110822429425475835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11497481096572567301113409 8623110822429425475835057)
                ·
                  refine ⟨6467333116822069106876293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8623110822429425475835057 6467333116822069106876293)
                  ·
                    refine ⟨1212624959404137957539305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6467333116822069106876293 1212624959404137957539305)
                    ·
                      refine ⟨909468719553103468154479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212624959404137957539305 909468719553103468154479)
                      ·
                        rfl

theorem cell23_1771184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 4, 2].length) (baseStart_1771184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771184 prefixEnd_1771184 := by exact prefixLift 1771184
  have htrace : WordTrace (prefixWord ++ tailWord_1771184) baseStart_1771184 baseEnd_1771184 := by
    simpa [prefixWord, tailWord_1771184, baseEnd_1771184] using wordTrace_append hprefix tailTrace_1771184
  have hstable : (prefixWord ++ tailWord_1771184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771184).length < 2 ^ (prefixWord ++ tailWord_1771184).sum := by decide
  have hdescent : baseEnd_1771184 < baseStart_1771184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771194 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_1771194 : Nat := 118140960795 + 1771194 * 2 ^ 59
def prefixEnd_1771194 : Nat := 4983230072969 + 3 ^ 40 * 1771194 * 2
def baseEnd_1771194 : Nat := 303157951453216143009811

theorem tailTrace_1771194 : CollatzResearch.WordTrace tailWord_1771194 prefixEnd_1771194 303157951453216143009811 := by
  unfold tailWord_1771194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16150188086318527174346159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43067168230182739131589757 16150188086318527174346159)
  ·
    refine ⟨24225282129477790761519239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16150188086318527174346159 24225282129477790761519239)
    ·
      refine ⟨36337923194216686142278859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24225282129477790761519239 36337923194216686142278859)
      ·
        refine ⟨54506884791325029213418289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36337923194216686142278859 54506884791325029213418289)
        ·
          refine ⟨40880163593493771910063717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54506884791325029213418289 40880163593493771910063717)
          ·
            refine ⟨7665030673780082233136947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40880163593493771910063717 7665030673780082233136947)
            ·
              refine ⟨11497546010670123349705421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665030673780082233136947 11497546010670123349705421)
              ·
                refine ⟨4311579754001296256139533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11497546010670123349705421 4311579754001296256139533)
                ·
                  refine ⟨1616842407750486096052325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311579754001296256139533 1616842407750486096052325)
                  ·
                    refine ⟨303157951453216143009811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616842407750486096052325 303157951453216143009811)
                    ·
                      rfl

theorem cell23_1771194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_1771194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771194 prefixEnd_1771194 := by exact prefixLift 1771194
  have htrace : WordTrace (prefixWord ++ tailWord_1771194) baseStart_1771194 baseEnd_1771194 := by
    simpa [prefixWord, tailWord_1771194, baseEnd_1771194] using wordTrace_append hprefix tailTrace_1771194
  have hstable : (prefixWord ++ tailWord_1771194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771194).length < 2 ^ (prefixWord ++ tailWord_1771194).sum := by decide
  have hdescent : baseEnd_1771194 < baseStart_1771194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771197 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1771197 : Nat := 118140960795 + 1771197 * 2 ^ 59
def prefixEnd_1771197 : Nat := 4983230072969 + 3 ^ 40 * 1771197 * 2
def baseEnd_1771197 : Nat := 909475394801611917291919

theorem tailTrace_1771197 : CollatzResearch.WordTrace tailWord_1771197 prefixEnd_1771197 909475394801611917291919 := by
  unfold tailWord_1771197
  simp only [CollatzResearch.WordTrace]
  refine ⟨64600861764263240209743845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43067241176175493473162563 64600861764263240209743845)
  ·
    refine ⟨12112661580799357539326971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64600861764263240209743845 12112661580799357539326971)
    ·
      refine ⟨18168992371199036308990457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112661580799357539326971 18168992371199036308990457)
      ·
        refine ⟨13626744278399277231742843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18168992371199036308990457 13626744278399277231742843)
        ·
          refine ⟨20440116417598915847614265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13626744278399277231742843 20440116417598915847614265)
          ·
            refine ⟨15330087313199186885710699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20440116417598915847614265 15330087313199186885710699)
            ·
              refine ⟨22995130969798780328566049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15330087313199186885710699 22995130969798780328566049)
              ·
                refine ⟨17246348227349085246424537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22995130969798780328566049 17246348227349085246424537)
                ·
                  refine ⟨12934761170511813934818403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17246348227349085246424537 12934761170511813934818403)
                  ·
                    refine ⟨19402141755767720902227605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12934761170511813934818403 19402141755767720902227605)
                    ·
                      refine ⟨909475394801611917291919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19402141755767720902227605 909475394801611917291919)
                      ·
                        rfl

theorem cell23_1771197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1771197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771197 prefixEnd_1771197 := by exact prefixLift 1771197
  have htrace : WordTrace (prefixWord ++ tailWord_1771197) baseStart_1771197 baseEnd_1771197 := by
    simpa [prefixWord, tailWord_1771197, baseEnd_1771197] using wordTrace_append hprefix tailTrace_1771197
  have hstable : (prefixWord ++ tailWord_1771197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771197).length < 2 ^ (prefixWord ++ tailWord_1771197).sum := by decide
  have hdescent : baseEnd_1771197 < baseStart_1771197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771204 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1771204 : Nat := 118140960795 + 1771204 * 2 ^ 59
def prefixEnd_1771204 : Nat := 4983230072969 + 3 ^ 40 * 1771204 * 2
def baseEnd_1771204 : Nat := 909478989166193389904387

theorem tailTrace_1771204 : CollatzResearch.WordTrace tailWord_1771204 prefixEnd_1771204 909478989166193389904387 := by
  unfold tailWord_1771204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32300558537618940202624333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43067411383491920270165777 32300558537618940202624333)
  ·
    refine ⟨12112709451607102575984125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32300558537618940202624333 12112709451607102575984125)
    ·
      refine ⟨4542266044352663465994047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12112709451607102575984125 4542266044352663465994047)
      ·
        refine ⟨6813399066528995198991071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542266044352663465994047 6813399066528995198991071)
        ·
          refine ⟨10220098599793492798486607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813399066528995198991071 10220098599793492798486607)
          ·
            refine ⟨15330147899690239197729911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10220098599793492798486607 15330147899690239197729911)
            ·
              refine ⟨22995221849535358796594867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15330147899690239197729911 22995221849535358796594867)
              ·
                refine ⟨34492832774303038194892301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22995221849535358796594867 34492832774303038194892301)
                ·
                  refine ⟨12934812290363639323084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34492832774303038194892301 12934812290363639323084613)
                  ·
                    refine ⟨2425277304443182373078365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12934812290363639323084613 2425277304443182373078365)
                    ·
                      refine ⟨909478989166193389904387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425277304443182373078365 909478989166193389904387)
                      ·
                        rfl

theorem cell23_1771204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1771204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771204 prefixEnd_1771204 := by exact prefixLift 1771204
  have htrace : WordTrace (prefixWord ++ tailWord_1771204) baseStart_1771204 baseEnd_1771204 := by
    simpa [prefixWord, tailWord_1771204, baseEnd_1771204] using wordTrace_append hprefix tailTrace_1771204
  have hstable : (prefixWord ++ tailWord_1771204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771204).length < 2 ^ (prefixWord ++ tailWord_1771204).sum := by decide
  have hdescent : baseEnd_1771204 < baseStart_1771204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771245 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1771245 : Nat := 118140960795 + 1771245 * 2 ^ 59
def prefixEnd_1771245 : Nat := 4983230072969 + 3 ^ 40 * 1771245 * 2
def baseEnd_1771245 : Nat := 303166680624342576497233

theorem tailTrace_1771245 : CollatzResearch.WordTrace tailWord_1771245 prefixEnd_1771245 303166680624342576497233 := by
  unfold tailWord_1771245
  simp only [CollatzResearch.WordTrace]
  refine ⟨64602612468089344407491189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43068408312059562938327459 64602612468089344407491189)
  ·
    refine ⟨6056494918883376038202299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64602612468089344407491189 6056494918883376038202299)
    ·
      refine ⟨9084742378325064057303449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6056494918883376038202299 9084742378325064057303449)
      ·
        refine ⟨6813556783743798042977587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9084742378325064057303449 6813556783743798042977587)
        ·
          refine ⟨10220335175615697064466381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813556783743798042977587 10220335175615697064466381)
          ·
            refine ⟨3832625690855886399174893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10220335175615697064466381 3832625690855886399174893)
            ·
              refine ⟨1437234634070957399690585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3832625690855886399174893 1437234634070957399690585)
              ·
                refine ⟨1077925975553218049767939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437234634070957399690585 1077925975553218049767939)
                ·
                  refine ⟨1616888963329827074651909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077925975553218049767939 1616888963329827074651909)
                  ·
                    refine ⟨303166680624342576497233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616888963329827074651909 303166680624342576497233)
                    ·
                      rfl

theorem cell23_1771245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1771245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771245 prefixEnd_1771245 := by exact prefixLift 1771245
  have htrace : WordTrace (prefixWord ++ tailWord_1771245) baseStart_1771245 baseEnd_1771245 := by
    simpa [prefixWord, tailWord_1771245, baseEnd_1771245] using wordTrace_append hprefix tailTrace_1771245
  have hstable : (prefixWord ++ tailWord_1771245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771245).length < 2 ^ (prefixWord ++ tailWord_1771245).sum := by decide
  have hdescent : baseEnd_1771245 < baseStart_1771245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771251 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 3]
def baseStart_1771251 : Nat := 118140960795 + 1771251 * 2 ^ 59
def prefixEnd_1771251 : Nat := 4983230072969 + 3 ^ 40 * 1771251 * 2
def baseEnd_1771251 : Nat := 909503122756954706016671

theorem tailTrace_1771251 : CollatzResearch.WordTrace tailWord_1771251 prefixEnd_1771251 909503122756954706016671 := by
  unfold tailWord_1771251
  simp only [CollatzResearch.WordTrace]
  refine ⟨64602831306067607432209607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43068554204045071621473071 64602831306067607432209607)
  ·
    refine ⟨96904246959101411148314411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64602831306067607432209607 96904246959101411148314411)
    ·
      refine ⟨145356370438652116722471617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96904246959101411148314411 145356370438652116722471617)
      ·
        refine ⟨109017277828989087541853713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145356370438652116722471617 109017277828989087541853713)
        ·
          refine ⟨81762958371741815656390285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109017277828989087541853713 81762958371741815656390285)
          ·
            refine ⟨30661109389403180871146357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81762958371741815656390285 30661109389403180871146357)
            ·
              refine ⟨2874479005256548206669971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30661109389403180871146357 2874479005256548206669971)
              ·
                refine ⟨4311718507884822310004957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874479005256548206669971 4311718507884822310004957)
                ·
                  refine ⟨1616894440456808366251859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311718507884822310004957 1616894440456808366251859)
                  ·
                    refine ⟨2425341660685212549377789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1616894440456808366251859 2425341660685212549377789)
                    ·
                      refine ⟨909503122756954706016671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425341660685212549377789 909503122756954706016671)
                      ·
                        rfl

theorem cell23_1771251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_1771251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771251 prefixEnd_1771251 := by exact prefixLift 1771251
  have htrace : WordTrace (prefixWord ++ tailWord_1771251) baseStart_1771251 baseEnd_1771251 := by
    simpa [prefixWord, tailWord_1771251, baseEnd_1771251] using wordTrace_append hprefix tailTrace_1771251
  have hstable : (prefixWord ++ tailWord_1771251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771251).length < 2 ^ (prefixWord ++ tailWord_1771251).sum := by decide
  have hdescent : baseEnd_1771251 < baseStart_1771251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771257 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1771257 : Nat := 118140960795 + 1771257 * 2 ^ 59
def prefixEnd_1771257 : Nat := 4983230072969 + 3 ^ 40 * 1771257 * 2
def baseEnd_1771257 : Nat := 909506203640881682541643

theorem tailTrace_1771257 : CollatzResearch.WordTrace tailWord_1771257 prefixEnd_1771257 909506203640881682541643 := by
  unfold tailWord_1771257
  simp only [CollatzResearch.WordTrace]
  refine ⟨64603050144045870456928025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43068700096030580304618683 64603050144045870456928025)
  ·
    refine ⟨48452287608034402842696019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64603050144045870456928025 48452287608034402842696019)
    ·
      refine ⟨72678431412051604264044029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48452287608034402842696019 72678431412051604264044029)
      ·
        refine ⟨27254411779519351599016511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72678431412051604264044029 27254411779519351599016511)
        ·
          refine ⟨40881617669279027398524767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27254411779519351599016511 40881617669279027398524767)
          ·
            refine ⟨61322426503918541097787151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40881617669279027398524767 61322426503918541097787151)
            ·
              refine ⟨91983639755877811646680727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61322426503918541097787151 91983639755877811646680727)
              ·
                refine ⟨137975459633816717470021091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91983639755877811646680727 137975459633816717470021091)
                ·
                  refine ⟨206963189450725076205031637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137975459633816717470021091 206963189450725076205031637)
                  ·
                    refine ⟨4850699752751368973555429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206963189450725076205031637 4850699752751368973555429)
                    ·
                      refine ⟨909506203640881682541643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4850699752751368973555429 909506203640881682541643)
                      ·
                        rfl

theorem cell23_1771257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1771257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771257 prefixEnd_1771257 := by exact prefixLift 1771257
  have htrace : WordTrace (prefixWord ++ tailWord_1771257) baseStart_1771257 baseEnd_1771257 := by
    simpa [prefixWord, tailWord_1771257, baseEnd_1771257] using wordTrace_append hprefix tailTrace_1771257
  have hstable : (prefixWord ++ tailWord_1771257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771257).length < 2 ^ (prefixWord ++ tailWord_1771257).sum := by decide
  have hdescent : baseEnd_1771257 < baseStart_1771257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771271 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1771271 : Nat := 118140960795 + 1771271 * 2 ^ 59
def prefixEnd_1771271 : Nat := 4983230072969 + 3 ^ 40 * 1771271 * 2
def baseEnd_1771271 : Nat := 303171130790014875922193

theorem tailTrace_1771271 : CollatzResearch.WordTrace tailWord_1771271 prefixEnd_1771271 303171130790014875922193 := by
  unfold tailWord_1771271
  simp only [CollatzResearch.WordTrace]
  refine ⟨64603560765995150847937667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43069040510663433898625111 64603560765995150847937667)
  ·
    refine ⟨96905341148992726271906501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64603560765995150847937667 96905341148992726271906501)
    ·
      refine ⟨18169751465436136175982469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96905341148992726271906501 18169751465436136175982469)
      ·
        refine ⟨3406828399769275532996713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18169751465436136175982469 3406828399769275532996713)
        ·
          refine ⟨2555121299826956649747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3406828399769275532996713 2555121299826956649747535)
          ·
            refine ⟨3832681949740434974621303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555121299826956649747535 3832681949740434974621303)
            ·
              refine ⟨5749022924610652461931955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832681949740434974621303 5749022924610652461931955)
              ·
                refine ⟨8623534386915978692897933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749022924610652461931955 8623534386915978692897933)
                ·
                  refine ⟨3233825395093492009836725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8623534386915978692897933 3233825395093492009836725)
                  ·
                    refine ⟨303171130790014875922193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3233825395093492009836725 303171130790014875922193)
                    ·
                      rfl

theorem cell23_1771271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1771271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771271 prefixEnd_1771271 := by exact prefixLift 1771271
  have htrace : WordTrace (prefixWord ++ tailWord_1771271) baseStart_1771271 baseEnd_1771271 := by
    simpa [prefixWord, tailWord_1771271, baseEnd_1771271] using wordTrace_append hprefix tailTrace_1771271
  have hstable : (prefixWord ++ tailWord_1771271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771271).length < 2 ^ (prefixWord ++ tailWord_1771271).sum := by decide
  have hdescent : baseEnd_1771271 < baseStart_1771271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 5, 2, 2]
def baseStart_1771291 : Nat := 118140960795 + 1771291 * 2 ^ 59
def prefixEnd_1771291 : Nat := 4983230072969 + 3 ^ 40 * 1771291 * 2
def baseEnd_1771291 : Nat := 909523661983134549516487

theorem tailTrace_1771291 : CollatzResearch.WordTrace tailWord_1771291 prefixEnd_1771291 909523661983134549516487 := by
  unfold tailWord_1771291
  simp only [CollatzResearch.WordTrace]
  refine ⟨64604290225922694263665727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43069526817281796175777151 64604290225922694263665727)
  ·
    refine ⟨96906435338884041395498591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64604290225922694263665727 96906435338884041395498591)
    ·
      refine ⟨145359653008326062093247887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96906435338884041395498591 145359653008326062093247887)
      ·
        refine ⟨218039479512489093139871831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145359653008326062093247887 218039479512489093139871831)
        ·
          refine ⟨327059219268733639709807747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218039479512489093139871831 327059219268733639709807747)
          ·
            refine ⟨490588828903100459564711621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327059219268733639709807747 490588828903100459564711621)
            ·
              refine ⟨91985405419331336168383429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490588828903100459564711621 91985405419331336168383429)
              ·
                refine ⟨17247263516124625531571893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91985405419331336168383429 17247263516124625531571893)
                ·
                  refine ⟨1616930954636683643584865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17247263516124625531571893 1616930954636683643584865)
                  ·
                    refine ⟨1212698215977512732688649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616930954636683643584865 1212698215977512732688649)
                    ·
                      refine ⟨909523661983134549516487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212698215977512732688649 909523661983134549516487)
                      ·
                        rfl

theorem cell23_1771291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2, 2].length) (baseStart_1771291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771291 prefixEnd_1771291 := by exact prefixLift 1771291
  have htrace : WordTrace (prefixWord ++ tailWord_1771291) baseStart_1771291 baseEnd_1771291 := by
    simpa [prefixWord, tailWord_1771291, baseEnd_1771291] using wordTrace_append hprefix tailTrace_1771291
  have hstable : (prefixWord ++ tailWord_1771291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771291).length < 2 ^ (prefixWord ++ tailWord_1771291).sum := by decide
  have hdescent : baseEnd_1771291 < baseStart_1771291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771297 : List Nat := [1, 2, 3, 2, 1, 14]
def baseStart_1771297 : Nat := 118140960795 + 1771297 * 2 ^ 59
def prefixEnd_1771297 : Nat := 4983230072969 + 3 ^ 40 * 1771297 * 2
def baseEnd_1771297 : Nat := 3742908406860335498113

theorem tailTrace_1771297 : CollatzResearch.WordTrace tailWord_1771297 prefixEnd_1771297 3742908406860335498113 := by
  unfold tailWord_1771297
  simp only [CollatzResearch.WordTrace]
  refine ⟨64604509063900957288384145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43069672709267304858922763 64604509063900957288384145)
  ·
    refine ⟨48453381797925717966288109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64604509063900957288384145 48453381797925717966288109)
    ·
      refine ⟨18170018174222144237358041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48453381797925717966288109 18170018174222144237358041)
      ·
        refine ⟨13627513630666608178018531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18170018174222144237358041 13627513630666608178018531)
        ·
          refine ⟨20441270445999912267027797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13627513630666608178018531 20441270445999912267027797)
          ·
            refine ⟨3742908406860335498113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 20441270445999912267027797 3742908406860335498113)
            ·
              rfl

theorem cell23_1771297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 14].length) (baseStart_1771297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771297 prefixEnd_1771297 := by exact prefixLift 1771297
  have htrace : WordTrace (prefixWord ++ tailWord_1771297) baseStart_1771297 baseEnd_1771297 := by
    simpa [prefixWord, tailWord_1771297, baseEnd_1771297] using wordTrace_append hprefix tailTrace_1771297
  have hstable : (prefixWord ++ tailWord_1771297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771297).length < 2 ^ (prefixWord ++ tailWord_1771297).sum := by decide
  have hdescent : baseEnd_1771297 < baseStart_1771297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771301 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_1771301 : Nat := 118140960795 + 1771301 * 2 ^ 59
def prefixEnd_1771301 : Nat := 4983230072969 + 3 ^ 40 * 1771301 * 2
def baseEnd_1771301 : Nat := 303176265596559836797147

theorem tailTrace_1771301 : CollatzResearch.WordTrace tailWord_1771301 prefixEnd_1771301 303176265596559836797147 := by
  unfold tailWord_1771301
  simp only [CollatzResearch.WordTrace]
  refine ⟨64604654955886465971529757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43069769970590977314353171 64604654955886465971529757)
  ·
    refine ⟨24226745608457424739323659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64604654955886465971529757 24226745608457424739323659)
    ·
      refine ⟨36340118412686137108985489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24226745608457424739323659 36340118412686137108985489)
      ·
        refine ⟨27255088809514602831739117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36340118412686137108985489 27255088809514602831739117)
        ·
          refine ⟨10220658303567976061902169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27255088809514602831739117 10220658303567976061902169)
          ·
            refine ⟨7665493727675982046426627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220658303567976061902169 7665493727675982046426627)
            ·
              refine ⟨11498240591513973069639941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665493727675982046426627 11498240591513973069639941)
              ·
                refine ⟨2155920110908869950557489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11498240591513973069639941 2155920110908869950557489)
                ·
                  refine ⟨1616940083181652462918117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2155920110908869950557489 1616940083181652462918117)
                  ·
                    refine ⟨303176265596559836797147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616940083181652462918117 303176265596559836797147)
                    ·
                      rfl

theorem cell23_1771301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_1771301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771301 prefixEnd_1771301 := by exact prefixLift 1771301
  have htrace : WordTrace (prefixWord ++ tailWord_1771301) baseStart_1771301 baseEnd_1771301 := by
    simpa [prefixWord, tailWord_1771301, baseEnd_1771301] using wordTrace_append hprefix tailTrace_1771301
  have hstable : (prefixWord ++ tailWord_1771301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771301).length < 2 ^ (prefixWord ++ tailWord_1771301).sum := by decide
  have hdescent : baseEnd_1771301 < baseStart_1771301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771314 : List Nat := [3, 2, 1, 1, 3, 2, 3, 8]
def baseStart_1771314 : Nat := 118140960795 + 1771314 * 2 ^ 59
def prefixEnd_1771314 : Nat := 4983230072969 + 3 ^ 40 * 1771314 * 2
def baseEnd_1771314 : Nat := 33686498964377331834403

theorem tailTrace_1771314 : CollatzResearch.WordTrace tailWord_1771314 prefixEnd_1771314 33686498964377331834403 := by
  unfold tailWord_1771314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151282276209842297938249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43070086069892912794501997 16151282276209842297938249)
  ·
    refine ⟨12113461707157381723453687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16151282276209842297938249 12113461707157381723453687)
    ·
      refine ⟨18170192560736072585180531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113461707157381723453687 18170192560736072585180531)
      ·
        refine ⟨27255288841104108877770797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18170192560736072585180531 27255288841104108877770797)
        ·
          refine ⟨10220733315414040829164049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27255288841104108877770797 10220733315414040829164049)
          ·
            refine ⟨7665549986560530621873037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220733315414040829164049 7665549986560530621873037)
            ·
              refine ⟨2874581244960198983202389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7665549986560530621873037 2874581244960198983202389)
              ·
                refine ⟨33686498964377331834403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2874581244960198983202389 33686498964377331834403)
                ·
                  rfl

theorem cell23_1771314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_1771314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771314 prefixEnd_1771314 := by exact prefixLift 1771314
  have htrace : WordTrace (prefixWord ++ tailWord_1771314) baseStart_1771314 baseEnd_1771314 := by
    simpa [prefixWord, tailWord_1771314, baseEnd_1771314] using wordTrace_append hprefix tailTrace_1771314
  have hstable : (prefixWord ++ tailWord_1771314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771314).length < 2 ^ (prefixWord ++ tailWord_1771314).sum := by decide
  have hdescent : baseEnd_1771314 < baseStart_1771314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771318 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1771318 : Nat := 118140960795 + 1771318 * 2 ^ 59
def prefixEnd_1771318 : Nat := 4983230072969 + 3 ^ 40 * 1771318 * 2
def baseEnd_1771318 : Nat := 303179175320268647959621

theorem tailTrace_1771318 : CollatzResearch.WordTrace tailWord_1771318 prefixEnd_1771318 303179175320268647959621 := by
  unfold tailWord_1771318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037829687301554867181163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43070183331216585249932405 4037829687301554867181163)
  ·
    refine ⟨6056744530952332300771745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4037829687301554867181163 6056744530952332300771745)
    ·
      refine ⟨4542558398214249225578809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6056744530952332300771745 4542558398214249225578809)
      ·
        refine ⟨3406918798660686919184107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542558398214249225578809 3406918798660686919184107)
        ·
          refine ⟨5110378197991030378776161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406918798660686919184107 5110378197991030378776161)
          ·
            refine ⟨3832783648493272784082121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110378197991030378776161 3832783648493272784082121)
            ·
              refine ⟨2874587736369954588061591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832783648493272784082121 2874587736369954588061591)
              ·
                refine ⟨4311881604554931882092387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874587736369954588061591 4311881604554931882092387)
                ·
                  refine ⟨6467822406832397823138581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4311881604554931882092387 6467822406832397823138581)
                  ·
                    refine ⟨303179175320268647959621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6467822406832397823138581 303179175320268647959621)
                    ·
                      rfl

theorem cell23_1771318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1771318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771318 prefixEnd_1771318 := by exact prefixLift 1771318
  have htrace : WordTrace (prefixWord ++ tailWord_1771318) baseStart_1771318 baseEnd_1771318 := by
    simpa [prefixWord, tailWord_1771318, baseEnd_1771318] using wordTrace_append hprefix tailTrace_1771318
  have hstable : (prefixWord ++ tailWord_1771318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771318).length < 2 ^ (prefixWord ++ tailWord_1771318).sum := by decide
  have hdescent : baseEnd_1771318 < baseStart_1771318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771325 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1771325 : Nat := 118140960795 + 1771325 * 2 ^ 59
def prefixEnd_1771325 : Nat := 4983230072969 + 3 ^ 40 * 1771325 * 2
def baseEnd_1771325 : Nat := 909541120325387416491331

theorem tailTrace_1771325 : CollatzResearch.WordTrace tailWord_1771325 prefixEnd_1771325 909541120325387416491331 := by
  unfold tailWord_1771325
  simp only [CollatzResearch.WordTrace]
  refine ⟨64605530307799518070403429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43070353538533012046935619 64605530307799518070403429)
  ·
    refine ⟨12113536932712409638200643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64605530307799518070403429 12113536932712409638200643)
    ·
      refine ⟨18170305399068614457300965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113536932712409638200643 18170305399068614457300965)
      ·
        refine ⟨3406932262325365210743931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18170305399068614457300965 3406932262325365210743931)
        ·
          refine ⟨5110398393488047816115897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406932262325365210743931 5110398393488047816115897)
          ·
            refine ⟨3832798795116035862086923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5110398393488047816115897 3832798795116035862086923)
            ·
              refine ⟨5749198192674053793130385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832798795116035862086923 5749198192674053793130385)
              ·
                refine ⟨4311898644505540344847789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749198192674053793130385 4311898644505540344847789)
                ·
                  refine ⟨1616961991689577629317921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311898644505540344847789 1616961991689577629317921)
                  ·
                    refine ⟨1212721493767183221988441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1616961991689577629317921 1212721493767183221988441)
                    ·
                      refine ⟨909541120325387416491331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212721493767183221988441 909541120325387416491331)
                      ·
                        rfl

theorem cell23_1771325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1771325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771325 prefixEnd_1771325 := by exact prefixLift 1771325
  have htrace : WordTrace (prefixWord ++ tailWord_1771325) baseStart_1771325 baseEnd_1771325 := by
    simpa [prefixWord, tailWord_1771325, baseEnd_1771325] using wordTrace_append hprefix tailTrace_1771325
  have hstable : (prefixWord ++ tailWord_1771325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771325).length < 2 ^ (prefixWord ++ tailWord_1771325).sum := by decide
  have hdescent : baseEnd_1771325 < baseStart_1771325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771345 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_1771345 : Nat := 118140960795 + 1771345 * 2 ^ 59
def prefixEnd_1771345 : Nat := 4983230072969 + 3 ^ 40 * 1771345 * 2
def baseEnd_1771345 : Nat := 909551389938477338241239

theorem tailTrace_1771345 : CollatzResearch.WordTrace tailWord_1771345 prefixEnd_1771345 909551389938477338241239 := by
  unfold tailWord_1771345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64606259767727061486131489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43070839845151374324087659 64606259767727061486131489)
  ·
    refine ⟨48454694825795296114598617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64606259767727061486131489 48454694825795296114598617)
    ·
      refine ⟨36341021119346472085948963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48454694825795296114598617 36341021119346472085948963)
      ·
        refine ⟨54511531679019708128923445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36341021119346472085948963 54511531679019708128923445)
        ·
          refine ⟨5110456094908097637086573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54511531679019708128923445 5110456094908097637086573)
          ·
            refine ⟨1916421035590536613907465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5110456094908097637086573 1916421035590536613907465)
            ·
              refine ⟨1437315776692902460430599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916421035590536613907465 1437315776692902460430599)
              ·
                refine ⟨2155973665039353690645899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437315776692902460430599 2155973665039353690645899)
                ·
                  refine ⟨3233960497559030535968849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155973665039353690645899 3233960497559030535968849)
                  ·
                    refine ⟨2425470373169272901976637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3233960497559030535968849 2425470373169272901976637)
                    ·
                      refine ⟨909551389938477338241239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425470373169272901976637 909551389938477338241239)
                      ·
                        rfl

theorem cell23_1771345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_1771345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771345 prefixEnd_1771345 := by exact prefixLift 1771345
  have htrace : WordTrace (prefixWord ++ tailWord_1771345) baseStart_1771345 baseEnd_1771345 := by
    simpa [prefixWord, tailWord_1771345, baseEnd_1771345] using wordTrace_append hprefix tailTrace_1771345
  have hstable : (prefixWord ++ tailWord_1771345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771345).length < 2 ^ (prefixWord ++ tailWord_1771345).sum := by decide
  have hdescent : baseEnd_1771345 < baseStart_1771345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771384 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1771384 : Nat := 118140960795 + 1771384 * 2 ^ 59
def prefixEnd_1771384 : Nat := 4983230072969 + 3 ^ 40 * 1771384 * 2
def baseEnd_1771384 : Nat := 909571415684002685653559

theorem tailTrace_1771384 : CollatzResearch.WordTrace tailWord_1771384 prefixEnd_1771384 909571415684002685653559 := by
  unfold tailWord_1771384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32303841107292885573400603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43071788143057180764534137 32303841107292885573400603)
  ·
    refine ⟨48455761660939328360100905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32303841107292885573400603 48455761660939328360100905)
    ·
      refine ⟨36341821245704496270075679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48455761660939328360100905 36341821245704496270075679)
      ·
        refine ⟨54512731868556744405113519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36341821245704496270075679 54512731868556744405113519)
        ·
          refine ⟨81769097802835116607670279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54512731868556744405113519 81769097802835116607670279)
          ·
            refine ⟨122653646704252674911505419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81769097802835116607670279 122653646704252674911505419)
            ·
              refine ⟨183980470056379012367258129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122653646704252674911505419 183980470056379012367258129)
              ·
                refine ⟨137985352542284259275443597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183980470056379012367258129 137985352542284259275443597)
                ·
                  refine ⟨51744507203356597228291349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137985352542284259275443597 51744507203356597228291349)
                  ·
                    refine ⟨2425523775157340495076157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51744507203356597228291349 2425523775157340495076157)
                    ·
                      refine ⟨909571415684002685653559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425523775157340495076157 909571415684002685653559)
                      ·
                        rfl

theorem cell23_1771384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1771384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771384 prefixEnd_1771384 := by exact prefixLift 1771384
  have htrace : WordTrace (prefixWord ++ tailWord_1771384) baseStart_1771384 baseEnd_1771384 := by
    simpa [prefixWord, tailWord_1771384, baseEnd_1771384] using wordTrace_append hprefix tailTrace_1771384
  have hstable : (prefixWord ++ tailWord_1771384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771384).length < 2 ^ (prefixWord ++ tailWord_1771384).sum := by decide
  have hdescent : baseEnd_1771384 < baseStart_1771384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771421 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 7]
def baseStart_1771421 : Nat := 118140960795 + 1771421 * 2 ^ 59
def prefixEnd_1771421 : Nat := 4983230072969 + 3 ^ 40 * 1771421 * 2
def baseEnd_1771421 : Nat := 101065601607579893432321

theorem tailTrace_1771421 : CollatzResearch.WordTrace tailWord_1771421 prefixEnd_1771421 101065601607579893432321 := by
  unfold tailWord_1771421
  simp only [CollatzResearch.WordTrace]
  refine ⟨64609031715451726465898117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43072687810301150977265411 64609031715451726465898117)
  ·
    refine ⟨12114193446647198712355897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64609031715451726465898117 12114193446647198712355897)
    ·
      refine ⟨9085645084985399034266923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12114193446647198712355897 9085645084985399034266923)
      ·
        refine ⟨13628467627478098551400385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9085645084985399034266923 13628467627478098551400385)
        ·
          refine ⟨10221350720608573913550289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13628467627478098551400385 10221350720608573913550289)
          ·
            refine ⟨7666013040456430435162717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10221350720608573913550289 7666013040456430435162717)
            ·
              refine ⟨2874754890171161413186019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7666013040456430435162717 2874754890171161413186019)
              ·
                refine ⟨4312132335256742119779029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874754890171161413186019 4312132335256742119779029)
                ·
                  refine ⟨101065601607579893432321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4312132335256742119779029 101065601607579893432321)
                  ·
                    rfl

theorem cell23_1771421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_1771421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771421 prefixEnd_1771421 := by exact prefixLift 1771421
  have htrace : WordTrace (prefixWord ++ tailWord_1771421) baseStart_1771421 baseEnd_1771421 := by
    simpa [prefixWord, tailWord_1771421, baseEnd_1771421] using wordTrace_append hprefix tailTrace_1771421
  have hstable : (prefixWord ++ tailWord_1771421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771421).length < 2 ^ (prefixWord ++ tailWord_1771421).sum := by decide
  have hdescent : baseEnd_1771421 < baseStart_1771421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771471 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_1771471 : Nat := 118140960795 + 1771471 * 2 ^ 59
def prefixEnd_1771471 : Nat := 4983230072969 + 3 ^ 40 * 1771471 * 2
def baseEnd_1771471 : Nat := 909616088500943845265659

theorem tailTrace_1771471 : CollatzResearch.WordTrace tailWord_1771471 prefixEnd_1771471 909616088500943845265659 := by
  unfold tailWord_1771471
  simp only [CollatzResearch.WordTrace]
  refine ⟨64610855365270585005218267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43073903576847056670145511 64610855365270585005218267)
  ·
    refine ⟨96916283047905877507827401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64610855365270585005218267 96916283047905877507827401)
    ·
      refine ⟨72687212285929408130870551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96916283047905877507827401 72687212285929408130870551)
      ·
        refine ⟨109030818428894112196305827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72687212285929408130870551 109030818428894112196305827)
        ·
          refine ⟨163546227643341168294458741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109030818428894112196305827 163546227643341168294458741)
          ·
            refine ⟨15332458841563234527605507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163546227643341168294458741 15332458841563234527605507)
            ·
              refine ⟨22998688262344851791408261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15332458841563234527605507 22998688262344851791408261)
              ·
                refine ⟨4312254049189659710889049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22998688262344851791408261 4312254049189659710889049)
                ·
                  refine ⟨3234190536892244783166787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312254049189659710889049 3234190536892244783166787)
                  ·
                    refine ⟨4851285805338367174750181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234190536892244783166787 4851285805338367174750181)
                    ·
                      refine ⟨909616088500943845265659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4851285805338367174750181 909616088500943845265659)
                      ·
                        rfl

theorem cell23_1771471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_1771471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771471 prefixEnd_1771471 := by exact prefixLift 1771471
  have htrace : WordTrace (prefixWord ++ tailWord_1771471) baseStart_1771471 baseEnd_1771471 := by
    simpa [prefixWord, tailWord_1771471, baseEnd_1771471] using wordTrace_append hprefix tailTrace_1771471
  have hstable : (prefixWord ++ tailWord_1771471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771471).length < 2 ^ (prefixWord ++ tailWord_1771471).sum := by decide
  have hdescent : baseEnd_1771471 < baseStart_1771471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771498 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1771498 : Nat := 118140960795 + 1771498 * 2 ^ 59
def prefixEnd_1771498 : Nat := 4983230072969 + 3 ^ 40 * 1771498 * 2
def baseEnd_1771498 : Nat := 303209984159538413209345

theorem tailTrace_1771498 : CollatzResearch.WordTrace tailWord_1771498 prefixEnd_1771498 303209984159538413209345 := by
  unfold tailWord_1771498
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152960034043192154112787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43074560090781845744300765 16152960034043192154112787)
  ·
    refine ⟨24229440051064788231169181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16152960034043192154112787 24229440051064788231169181)
    ·
      refine ⟨9086040019149295586688443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24229440051064788231169181 9086040019149295586688443)
      ·
        refine ⟨13629060028723943380032665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9086040019149295586688443 13629060028723943380032665)
        ·
          refine ⟨10221795021542957535024499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13629060028723943380032665 10221795021542957535024499)
          ·
            refine ⟨15332692532314436302536749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221795021542957535024499 15332692532314436302536749)
            ·
              refine ⟨5749759699617913613451281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15332692532314436302536749 5749759699617913613451281)
              ·
                refine ⟨4312319774713435210088461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749759699617913613451281 4312319774713435210088461)
                ·
                  refine ⟨1617119915517538203783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4312319774713435210088461 1617119915517538203783173)
                  ·
                    refine ⟨303209984159538413209345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617119915517538203783173 303209984159538413209345)
                    ·
                      rfl

theorem cell23_1771498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1771498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771498 prefixEnd_1771498 := by exact prefixLift 1771498
  have htrace : WordTrace (prefixWord ++ tailWord_1771498) baseStart_1771498 baseEnd_1771498 := by
    simpa [prefixWord, tailWord_1771498, baseEnd_1771498] using wordTrace_append hprefix tailTrace_1771498
  have hstable : (prefixWord ++ tailWord_1771498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771498).length < 2 ^ (prefixWord ++ tailWord_1771498).sum := by decide
  have hdescent : baseEnd_1771498 < baseStart_1771498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771505 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_1771505 : Nat := 118140960795 + 1771505 * 2 ^ 59
def prefixEnd_1771505 : Nat := 4983230072969 + 3 ^ 40 * 1771505 * 2
def baseEnd_1771505 : Nat := 909633546843196712240503

theorem tailTrace_1771505 : CollatzResearch.WordTrace tailWord_1771505 prefixEnd_1771505 909633546843196712240503 := by
  unfold tailWord_1771505
  simp only [CollatzResearch.WordTrace]
  refine ⟨64612095447147408811955969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43074730298098272541303979 64612095447147408811955969)
  ·
    refine ⟨48459071585360556608966977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64612095447147408811955969 48459071585360556608966977)
    ·
      refine ⟨36344303689020417456725233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48459071585360556608966977 36344303689020417456725233)
      ·
        refine ⟨27258227766765313092543925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36344303689020417456725233 27258227766765313092543925)
        ·
          refine ⟨2555458853134248102425993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27258227766765313092543925 2555458853134248102425993)
          ·
            refine ⟨1916594139850686076819495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555458853134248102425993 1916594139850686076819495)
            ·
              refine ⟨2874891209776029115229243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916594139850686076819495 2874891209776029115229243)
              ·
                refine ⟨4312336814664043672843865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874891209776029115229243 4312336814664043672843865)
                ·
                  refine ⟨3234252610998032754632899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4312336814664043672843865 3234252610998032754632899)
                  ·
                    refine ⟨4851378916497049131949349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234252610998032754632899 4851378916497049131949349)
                    ·
                      refine ⟨909633546843196712240503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4851378916497049131949349 909633546843196712240503)
                      ·
                        rfl

theorem cell23_1771505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_1771505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771505 prefixEnd_1771505 := by exact prefixLift 1771505
  have htrace : WordTrace (prefixWord ++ tailWord_1771505) baseStart_1771505 baseEnd_1771505 := by
    simpa [prefixWord, tailWord_1771505, baseEnd_1771505] using wordTrace_append hprefix tailTrace_1771505
  have hstable : (prefixWord ++ tailWord_1771505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771505).length < 2 ^ (prefixWord ++ tailWord_1771505).sum := by decide
  have hdescent : baseEnd_1771505 < baseStart_1771505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771518 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1771518 : Nat := 118140960795 + 1771518 * 2 ^ 59
def prefixEnd_1771518 : Nat := 4983230072969 + 3 ^ 40 * 1771518 * 2
def baseEnd_1771518 : Nat := 909640222091705161377943

theorem tailTrace_1771518 : CollatzResearch.WordTrace tailWord_1771518 prefixEnd_1771518 909640222091705161377943 := by
  unfold tailWord_1771518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076571199512539004022401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43075046397400208021452805 8076571199512539004022401)
  ·
    refine ⟨6057428399634404253016801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8076571199512539004022401 6057428399634404253016801)
    ·
      refine ⟨4543071299725803189762601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6057428399634404253016801 4543071299725803189762601)
      ·
        refine ⟨3407303474794352392321951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4543071299725803189762601 3407303474794352392321951)
        ·
          refine ⟨5110955212191528588482927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407303474794352392321951 5110955212191528588482927)
          ·
            refine ⟨7666432818287292882724391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110955212191528588482927 7666432818287292882724391)
            ·
              refine ⟨11499649227430939324086587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7666432818287292882724391 11499649227430939324086587)
              ·
                refine ⟨17249473841146408986129881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11499649227430939324086587 17249473841146408986129881)
                ·
                  refine ⟨12937105380859806739597411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17249473841146408986129881 12937105380859806739597411)
                  ·
                    refine ⟨19405658071289710109396117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12937105380859806739597411 19405658071289710109396117)
                    ·
                      refine ⟨909640222091705161377943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19405658071289710109396117 909640222091705161377943)
                      ·
                        rfl

theorem cell23_1771518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1771518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771518 prefixEnd_1771518 := by exact prefixLift 1771518
  have htrace : WordTrace (prefixWord ++ tailWord_1771518) baseStart_1771518 baseEnd_1771518 := by
    simpa [prefixWord, tailWord_1771518, baseEnd_1771518] using wordTrace_append hprefix tailTrace_1771518
  have hstable : (prefixWord ++ tailWord_1771518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771518).length < 2 ^ (prefixWord ++ tailWord_1771518).sum := by decide
  have hdescent : baseEnd_1771518 < baseStart_1771518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771561 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_1771561 : Nat := 118140960795 + 1771561 * 2 ^ 59
def prefixEnd_1771561 : Nat := 4983230072969 + 3 ^ 40 * 1771561 * 2
def baseEnd_1771561 : Nat := 909662301759848493140245

theorem tailTrace_1771561 : CollatzResearch.WordTrace tailWord_1771561 prefixEnd_1771561 909662301759848493140245 := by
  unfold tailWord_1771561
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614137934944530375994537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43076091956629686917329691 64614137934944530375994537)
  ·
    refine ⟨48460603451208397781995903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64614137934944530375994537 48460603451208397781995903)
    ·
      refine ⟨72690905176812596672993855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48460603451208397781995903 72690905176812596672993855)
      ·
        refine ⟨109036357765218895009490783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72690905176812596672993855 109036357765218895009490783)
        ·
          refine ⟨163554536647828342514236175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109036357765218895009490783 163554536647828342514236175)
          ·
            refine ⟨245331804971742513771354263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163554536647828342514236175 245331804971742513771354263)
            ·
              refine ⟨367997707457613770657031395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245331804971742513771354263 367997707457613770657031395)
              ·
                refine ⟨551996561186420655985547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367997707457613770657031395 551996561186420655985547093)
                ·
                  refine ⟨3234354850701683531165315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 551996561186420655985547093 3234354850701683531165315)
                  ·
                    refine ⟨4851532276052525296747973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234354850701683531165315 4851532276052525296747973)
                    ·
                      refine ⟨909662301759848493140245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4851532276052525296747973 909662301759848493140245)
                      ·
                        rfl

theorem cell23_1771561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_1771561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771561 prefixEnd_1771561 := by exact prefixLift 1771561
  have htrace : WordTrace (prefixWord ++ tailWord_1771561) baseStart_1771561 baseEnd_1771561 := by
    simpa [prefixWord, tailWord_1771561, baseEnd_1771561] using wordTrace_append hprefix tailTrace_1771561
  have hstable : (prefixWord ++ tailWord_1771561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771561).length < 2 ^ (prefixWord ++ tailWord_1771561).sum := by decide
  have hdescent : baseEnd_1771561 < baseStart_1771561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771571 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 6]
def baseStart_1771571 : Nat := 118140960795 + 1771571 * 2 ^ 59
def prefixEnd_1771571 : Nat := 4983230072969 + 3 ^ 40 * 1771571 * 2
def baseEnd_1771571 : Nat := 303222478855464484671733

theorem tailTrace_1771571 : CollatzResearch.WordTrace tailWord_1771571 prefixEnd_1771571 303222478855464484671733 := by
  unfold tailWord_1771571
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614502664908302083858567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43076335109938868055905711 64614502664908302083858567)
  ·
    refine ⟨96921753997362453125787851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64614502664908302083858567 96921753997362453125787851)
    ·
      refine ⟨145382630996043679688681777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96921753997362453125787851 145382630996043679688681777)
      ·
        refine ⟨109036973247032759766511333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145382630996043679688681777 109036973247032759766511333)
        ·
          refine ⟨20444432483818642456220875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109036973247032759766511333 20444432483818642456220875)
          ·
            refine ⟨30666648725727963684331313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20444432483818642456220875 30666648725727963684331313)
            ·
              refine ⟨22999986544295972763248485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30666648725727963684331313 22999986544295972763248485)
              ·
                refine ⟨4312497477055494893109091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22999986544295972763248485 4312497477055494893109091)
                ·
                  refine ⟨6468746215583242339663637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312497477055494893109091 6468746215583242339663637)
                  ·
                    refine ⟨303222478855464484671733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6468746215583242339663637 303222478855464484671733)
                    ·
                      rfl

theorem cell23_1771571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_1771571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771571 prefixEnd_1771571 := by exact prefixLift 1771571
  have htrace : WordTrace (prefixWord ++ tailWord_1771571) baseStart_1771571 baseEnd_1771571 := by
    simpa [prefixWord, tailWord_1771571, baseEnd_1771571] using wordTrace_append hprefix tailTrace_1771571
  have hstable : (prefixWord ++ tailWord_1771571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771571).length < 2 ^ (prefixWord ++ tailWord_1771571).sum := by decide
  have hdescent : baseEnd_1771571 < baseStart_1771571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771591 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1771591 : Nat := 118140960795 + 1771591 * 2 ^ 59
def prefixEnd_1771591 : Nat := 4983230072969 + 3 ^ 40 * 1771591 * 2
def baseEnd_1771591 : Nat := 909677706179483375765107

theorem tailTrace_1771591 : CollatzResearch.WordTrace tailWord_1771591 prefixEnd_1771591 909677706179483375765107 := by
  unfold tailWord_1771591
  simp only [CollatzResearch.WordTrace]
  refine ⟨64615232124835845499586627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43076821416557230333057751 64615232124835845499586627)
  ·
    refine ⟨96922848187253768249379941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64615232124835845499586627 96922848187253768249379941)
    ·
      refine ⟨18173034035110081546758739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96922848187253768249379941 18173034035110081546758739)
      ·
        refine ⟨27259551052665122320138109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18173034035110081546758739 27259551052665122320138109)
        ·
          refine ⟨10222331644749420870051791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27259551052665122320138109 10222331644749420870051791)
          ·
            refine ⟨15333497467124131305077687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222331644749420870051791 15333497467124131305077687)
            ·
              refine ⟨23000246200686196957616531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15333497467124131305077687 23000246200686196957616531)
              ·
                refine ⟨34500369301029295436424797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23000246200686196957616531 34500369301029295436424797)
                ·
                  refine ⟨12937638487885985788659299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34500369301029295436424797 12937638487885985788659299)
                  ·
                    refine ⟨19406457731828978682988949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12937638487885985788659299 19406457731828978682988949)
                    ·
                      refine ⟨909677706179483375765107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19406457731828978682988949 909677706179483375765107)
                      ·
                        rfl

theorem cell23_1771591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1771591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771591 prefixEnd_1771591 := by exact prefixLift 1771591
  have htrace : WordTrace (prefixWord ++ tailWord_1771591) baseStart_1771591 baseEnd_1771591 := by
    simpa [prefixWord, tailWord_1771591, baseEnd_1771591] using wordTrace_append hprefix tailTrace_1771591
  have hstable : (prefixWord ++ tailWord_1771591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771591).length < 2 ^ (prefixWord ++ tailWord_1771591).sum := by decide
  have hdescent : baseEnd_1771591 < baseStart_1771591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771598 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1771598 : Nat := 118140960795 + 1771598 * 2 ^ 59
def prefixEnd_1771598 : Nat := 4983230072969 + 3 ^ 40 * 1771598 * 2
def baseEnd_1771598 : Nat := 909681300544064848377575

theorem tailTrace_1771598 : CollatzResearch.WordTrace tailWord_1771598 prefixEnd_1771598 909681300544064848377575 := by
  unfold tailWord_1771598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076935929476310711886431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43076991623873657130060965 8076935929476310711886431)
  ·
    refine ⟨12115403894214466067829647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8076935929476310711886431 12115403894214466067829647)
    ·
      refine ⟨18173105841321699101744471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115403894214466067829647 18173105841321699101744471)
      ·
        refine ⟨27259658761982548652616707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18173105841321699101744471 27259658761982548652616707)
        ·
          refine ⟨40889488142973822978925061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27259658761982548652616707 40889488142973822978925061)
          ·
            refine ⟨7666779026807591808548449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40889488142973822978925061 7666779026807591808548449)
            ·
              refine ⟨5750084270105693856411337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7666779026807591808548449 5750084270105693856411337)
              ·
                refine ⟨4312563202579270392308503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750084270105693856411337 4312563202579270392308503)
                ·
                  refine ⟨6468844803868905588462755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312563202579270392308503 6468844803868905588462755)
                  ·
                    refine ⟨9703267205803358382694133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6468844803868905588462755 9703267205803358382694133)
                    ·
                      refine ⟨909681300544064848377575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9703267205803358382694133 909681300544064848377575)
                      ·
                        rfl

theorem cell23_1771598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1771598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771598 prefixEnd_1771598 := by exact prefixLift 1771598
  have htrace : WordTrace (prefixWord ++ tailWord_1771598) baseStart_1771598 baseEnd_1771598 := by
    simpa [prefixWord, tailWord_1771598, baseEnd_1771598] using wordTrace_append hprefix tailTrace_1771598
  have hstable : (prefixWord ++ tailWord_1771598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771598).length < 2 ^ (prefixWord ++ tailWord_1771598).sum := by decide
  have hdescent : baseEnd_1771598 < baseStart_1771598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771605 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1771605 : Nat := 118140960795 + 1771605 * 2 ^ 59
def prefixEnd_1771605 : Nat := 4983230072969 + 3 ^ 40 * 1771605 * 2
def baseEnd_1771605 : Nat := 303228298302882106996681

theorem tailTrace_1771605 : CollatzResearch.WordTrace tailWord_1771605 prefixEnd_1771605 303228298302882106996681 := by
  unfold tailWord_1771605
  simp only [CollatzResearch.WordTrace]
  refine ⟨64615742746785125890596269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43077161831190083927064179 64615742746785125890596269)
  ·
    refine ⟨24230903530044422208973601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64615742746785125890596269 24230903530044422208973601)
    ·
      refine ⟨18173177647533316656730201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24230903530044422208973601 18173177647533316656730201)
      ·
        refine ⟨13629883235649987492547651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18173177647533316656730201 13629883235649987492547651)
        ·
          refine ⟨20444824853474981238821477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629883235649987492547651 20444824853474981238821477)
          ·
            refine ⟨3833404660026558982279027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20444824853474981238821477 3833404660026558982279027)
            ·
              refine ⟨5750106990039838473418541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833404660026558982279027 5750106990039838473418541)
              ·
                refine ⟨2156290121264939427531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5750106990039838473418541 2156290121264939427531953)
                ·
                  refine ⟨1617217590948704570648965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156290121264939427531953 1617217590948704570648965)
                  ·
                    refine ⟨303228298302882106996681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617217590948704570648965 303228298302882106996681)
                    ·
                      rfl

theorem cell23_1771605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1771605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771605 prefixEnd_1771605 := by exact prefixLift 1771605
  have htrace : WordTrace (prefixWord ++ tailWord_1771605) baseStart_1771605 baseEnd_1771605 := by
    simpa [prefixWord, tailWord_1771605, baseEnd_1771605] using wordTrace_append hprefix tailTrace_1771605
  have hstable : (prefixWord ++ tailWord_1771605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771605).length < 2 ^ (prefixWord ++ tailWord_1771605).sum := by decide
  have hdescent : baseEnd_1771605 < baseStart_1771605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771612 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1771612 : Nat := 118140960795 + 1771612 * 2 ^ 59
def prefixEnd_1771612 : Nat := 4983230072969 + 3 ^ 40 * 1771612 * 2
def baseEnd_1771612 : Nat := 909688489273227793602511

theorem tailTrace_1771612 : CollatzResearch.WordTrace tailWord_1771612 prefixEnd_1771612 909688489273227793602511 := by
  unfold tailWord_1771612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307999028879883043050545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43077332038506510724067393 32307999028879883043050545)
  ·
    refine ⟨24230999271659912282287909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32307999028879883043050545 24230999271659912282287909)
    ·
      refine ⟨4543312363436233552928983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24230999271659912282287909 4543312363436233552928983)
      ·
        refine ⟨6814968545154350329393475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543312363436233552928983 6814968545154350329393475)
        ·
          refine ⟨10222452817731525494090213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814968545154350329393475 10222452817731525494090213)
          ·
            refine ⟨1916709903324661030141915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10222452817731525494090213 1916709903324661030141915)
            ·
              refine ⟨2875064854986991545212873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916709903324661030141915 2875064854986991545212873)
              ·
                refine ⟨2156298641240243658909655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875064854986991545212873 2156298641240243658909655)
                ·
                  refine ⟨3234447961860365488364483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156298641240243658909655 3234447961860365488364483)
                  ·
                    refine ⟨4851671942790548232546725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3234447961860365488364483 4851671942790548232546725)
                    ·
                      refine ⟨909688489273227793602511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4851671942790548232546725 909688489273227793602511)
                      ·
                        rfl

theorem cell23_1771612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1771612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771612 prefixEnd_1771612 := by exact prefixLift 1771612
  have htrace : WordTrace (prefixWord ++ tailWord_1771612) baseStart_1771612 baseEnd_1771612 := by
    simpa [prefixWord, tailWord_1771612, baseEnd_1771612] using wordTrace_append hprefix tailTrace_1771612
  have hstable : (prefixWord ++ tailWord_1771612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771612).length < 2 ^ (prefixWord ++ tailWord_1771612).sum := by decide
  have hdescent : baseEnd_1771612 < baseStart_1771612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771628 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1771628 : Nat := 118140960795 + 1771628 * 2 ^ 59
def prefixEnd_1771628 : Nat := 4983230072969 + 3 ^ 40 * 1771628 * 2
def baseEnd_1771628 : Nat := 909696704963699731002437

theorem tailTrace_1771628 : CollatzResearch.WordTrace tailWord_1771628 prefixEnd_1771628 909696704963699731002437 := by
  unfold tailWord_1771628
  simp only [CollatzResearch.WordTrace]
  refine ⟨32308290812850900409341769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43077721083801200545789025 32308290812850900409341769)
  ·
    refine ⟨24231218109638175307006327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32308290812850900409341769 24231218109638175307006327)
    ·
      refine ⟨36346827164457262960509491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24231218109638175307006327 36346827164457262960509491)
      ·
        refine ⟨54520240746685894440764237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36346827164457262960509491 54520240746685894440764237)
        ·
          refine ⟨20445090280007210415286589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54520240746685894440764237 20445090280007210415286589)
          ·
            refine ⟨7666908855002703905732471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20445090280007210415286589 7666908855002703905732471)
            ·
              refine ⟨11500363282504055858598707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7666908855002703905732471 11500363282504055858598707)
              ·
                refine ⟨17250544923756083787898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500363282504055858598707 17250544923756083787898061)
                ·
                  refine ⟨6468954346408531420461773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17250544923756083787898061 6468954346408531420461773)
                  ·
                    refine ⟨2425857879903199282673165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6468954346408531420461773 2425857879903199282673165)
                    ·
                      refine ⟨909696704963699731002437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425857879903199282673165 909696704963699731002437)
                      ·
                        rfl

theorem cell23_1771628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1771628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771628 prefixEnd_1771628 := by exact prefixLift 1771628
  have htrace : WordTrace (prefixWord ++ tailWord_1771628) baseStart_1771628 baseEnd_1771628 := by
    simpa [prefixWord, tailWord_1771628, baseEnd_1771628] using wordTrace_append hprefix tailTrace_1771628
  have hstable : (prefixWord ++ tailWord_1771628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771628).length < 2 ^ (prefixWord ++ tailWord_1771628).sum := by decide
  have hdescent : baseEnd_1771628 < baseStart_1771628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771629 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_1771629 : Nat := 118140960795 + 1771629 * 2 ^ 59
def prefixEnd_1771629 : Nat := 4983230072969 + 3 ^ 40 * 1771629 * 2
def baseEnd_1771629 : Nat := 909697218444354227089933

theorem tailTrace_1771629 : CollatzResearch.WordTrace tailWord_1771629 prefixEnd_1771629 909697218444354227089933 := by
  unfold tailWord_1771629
  simp only [CollatzResearch.WordTrace]
  refine ⟨64616618098698177989469941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43077745399132118659646627 64616618098698177989469941)
  ·
    refine ⟨6057807946752954186512807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64616618098698177989469941 6057807946752954186512807)
    ·
      refine ⟨9086711920129431279769211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6057807946752954186512807 9086711920129431279769211)
      ·
        refine ⟨13630067880194146919653817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9086711920129431279769211 13630067880194146919653817)
        ·
          refine ⟨10222550910145610189740363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13630067880194146919653817 10222550910145610189740363)
          ·
            refine ⟨15333826365218415284610545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222550910145610189740363 15333826365218415284610545)
            ·
              refine ⟨11500369773913811463457909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333826365218415284610545 11500369773913811463457909)
              ·
                refine ⟨1078159666304419824699179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11500369773913811463457909 1078159666304419824699179)
                ·
                  refine ⟨1617239499456629737048769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078159666304419824699179 1617239499456629737048769)
                  ·
                    refine ⟨1212929624592472302786577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617239499456629737048769 1212929624592472302786577)
                    ·
                      refine ⟨909697218444354227089933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212929624592472302786577 909697218444354227089933)
                      ·
                        rfl

theorem cell23_1771629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_1771629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771629 prefixEnd_1771629 := by exact prefixLift 1771629
  have htrace : WordTrace (prefixWord ++ tailWord_1771629) baseStart_1771629 baseEnd_1771629 := by
    simpa [prefixWord, tailWord_1771629, baseEnd_1771629] using wordTrace_append hprefix tailTrace_1771629
  have hstable : (prefixWord ++ tailWord_1771629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771629).length < 2 ^ (prefixWord ++ tailWord_1771629).sum := by decide
  have hdescent : baseEnd_1771629 < baseStart_1771629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771632 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3]
def baseStart_1771632 : Nat := 118140960795 + 1771632 * 2 ^ 59
def prefixEnd_1771632 : Nat := 4983230072969 + 3 ^ 40 * 1771632 * 2
def baseEnd_1771632 : Nat := 909698758886317715352419

theorem tailTrace_1771632 : CollatzResearch.WordTrace tailWord_1771632 prefixEnd_1771632 909698758886317715352419 := by
  unfold tailWord_1771632
  simp only [CollatzResearch.WordTrace]
  refine ⟨32308363758843654750914575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43077818345124873001219433 32308363758843654750914575)
  ·
    refine ⟨48462545638265482126371863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32308363758843654750914575 48462545638265482126371863)
    ·
      refine ⟨72693818457398223189557795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48462545638265482126371863 72693818457398223189557795)
      ·
        refine ⟨109040727686097334784336693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72693818457398223189557795 109040727686097334784336693)
        ·
          refine ⟨10222568220571625136031565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109040727686097334784336693 10222568220571625136031565)
          ·
            refine ⟨3833463082714359426011837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10222568220571625136031565 3833463082714359426011837)
            ·
              refine ⟨1437548656017884784754439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3833463082714359426011837 1437548656017884784754439)
              ·
                refine ⟨2156322984026827177131659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437548656017884784754439 2156322984026827177131659)
                ·
                  refine ⟨3234484476040240765697489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2156322984026827177131659 3234484476040240765697489)
                  ·
                    refine ⟨2425863357030180574273117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234484476040240765697489 2425863357030180574273117)
                    ·
                      refine ⟨909698758886317715352419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425863357030180574273117 909698758886317715352419)
                      ·
                        rfl

theorem cell23_1771632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3].length) (baseStart_1771632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771632 prefixEnd_1771632 := by exact prefixLift 1771632
  have htrace : WordTrace (prefixWord ++ tailWord_1771632) baseStart_1771632 baseEnd_1771632 := by
    simpa [prefixWord, tailWord_1771632, baseEnd_1771632] using wordTrace_append hprefix tailTrace_1771632
  have hstable : (prefixWord ++ tailWord_1771632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771632).length < 2 ^ (prefixWord ++ tailWord_1771632).sum := by decide
  have hdescent : baseEnd_1771632 < baseStart_1771632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771655 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_1771655 : Nat := 118140960795 + 1771655 * 2 ^ 59
def prefixEnd_1771655 : Nat := 4983230072969 + 3 ^ 40 * 1771655 * 2
def baseEnd_1771655 : Nat := 909710568941371125364813

theorem tailTrace_1771655 : CollatzResearch.WordTrace tailWord_1771655 prefixEnd_1771655 909710568941371125364813 := by
  unfold tailWord_1771655
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617566396603984429916419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43078377597735989619944279 64617566396603984429916419)
  ·
    refine ⟨96926349594905976644874629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64617566396603984429916419 96926349594905976644874629)
    ·
      refine ⟨18173690549044870620913993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96926349594905976644874629 18173690549044870620913993)
      ·
        refine ⟨13630267911783652965685495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18173690549044870620913993 13630267911783652965685495)
        ·
          refine ⟨20445401867675479448528243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630267911783652965685495 20445401867675479448528243)
          ·
            refine ⟨30668102801513219172792365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20445401867675479448528243 30668102801513219172792365)
            ·
              refine ⟨11500538550567457189797137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30668102801513219172792365 11500538550567457189797137)
              ·
                refine ⟨8625403912925592892347853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11500538550567457189797137 8625403912925592892347853)
                ·
                  refine ⟨3234526467347097334630445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8625403912925592892347853 3234526467347097334630445)
                  ·
                    refine ⟨1212947425255161500486417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3234526467347097334630445 1212947425255161500486417)
                    ·
                      refine ⟨909710568941371125364813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212947425255161500486417 909710568941371125364813)
                      ·
                        rfl

theorem cell23_1771655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_1771655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771655 prefixEnd_1771655 := by exact prefixLift 1771655
  have htrace : WordTrace (prefixWord ++ tailWord_1771655) baseStart_1771655 baseEnd_1771655 := by
    simpa [prefixWord, tailWord_1771655, baseEnd_1771655] using wordTrace_append hprefix tailTrace_1771655
  have hstable : (prefixWord ++ tailWord_1771655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771655).length < 2 ^ (prefixWord ++ tailWord_1771655).sum := by decide
  have hdescent : baseEnd_1771655 < baseStart_1771655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771662 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1771662 : Nat := 118140960795 + 1771662 * 2 ^ 59
def prefixEnd_1771662 : Nat := 4983230072969 + 3 ^ 40 * 1771662 * 2
def baseEnd_1771662 : Nat := 909714163305952597977281

theorem tailTrace_1771662 : CollatzResearch.WordTrace tailWord_1771662 prefixEnd_1771662 909714163305952597977281 := by
  unfold tailWord_1771662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077227713447328078177655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43078547805052416416947493 8077227713447328078177655)
  ·
    refine ⟨12115841570170992117266483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077227713447328078177655 12115841570170992117266483)
    ·
      refine ⟨18173762355256488175899725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12115841570170992117266483 18173762355256488175899725)
      ·
        refine ⟨6815160883221183065962397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18173762355256488175899725 6815160883221183065962397)
        ·
          refine ⟨2555685331207943649735899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6815160883221183065962397 2555685331207943649735899)
          ·
            refine ⟨3833527996811915474603849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555685331207943649735899 3833527996811915474603849)
            ·
              refine ⟨2875145997608936605952887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833527996811915474603849 2875145997608936605952887)
              ·
                refine ⟨4312718996413404908929331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875145997608936605952887 4312718996413404908929331)
                ·
                  refine ⟨6469078494620107363393997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312718996413404908929331 6469078494620107363393997)
                  ·
                    refine ⟨2425904435482540261272749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6469078494620107363393997 2425904435482540261272749)
                    ·
                      refine ⟨909714163305952597977281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2425904435482540261272749 909714163305952597977281)
                      ·
                        rfl

theorem cell23_1771662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1771662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771662 prefixEnd_1771662 := by exact prefixLift 1771662
  have htrace : WordTrace (prefixWord ++ tailWord_1771662) baseStart_1771662 baseEnd_1771662 := by
    simpa [prefixWord, tailWord_1771662, baseEnd_1771662] using wordTrace_append hprefix tailTrace_1771662
  have hstable : (prefixWord ++ tailWord_1771662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771662).length < 2 ^ (prefixWord ++ tailWord_1771662).sum := by decide
  have hdescent : baseEnd_1771662 < baseStart_1771662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771685 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_1771685 : Nat := 118140960795 + 1771685 * 2 ^ 59
def prefixEnd_1771685 : Nat := 4983230072969 + 3 ^ 40 * 1771685 * 2
def baseEnd_1771685 : Nat := 909725973361006007989675

theorem tailTrace_1771685 : CollatzResearch.WordTrace tailWord_1771685 prefixEnd_1771685 909725973361006007989675 := by
  unfold tailWord_1771685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64618660586495299553508509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43079107057663533035672339 64618660586495299553508509)
  ·
    refine ⟨24231997719935737332565691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64618660586495299553508509 24231997719935737332565691)
    ·
      refine ⟨36347996579903605998848537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24231997719935737332565691 36347996579903605998848537)
      ·
        refine ⟨27260997434927704499136403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36347996579903605998848537 27260997434927704499136403)
        ·
          refine ⟨40891496152391556748704605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27260997434927704499136403 40891496152391556748704605)
          ·
            refine ⟨15334311057146833780764227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40891496152391556748704605 15334311057146833780764227)
            ·
              refine ⟨23001466585720250671146341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334311057146833780764227 23001466585720250671146341)
              ·
                refine ⟨4312774984822547000839939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23001466585720250671146341 4312774984822547000839939)
                ·
                  refine ⟨6469162477233820501259909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312774984822547000839939 6469162477233820501259909)
                  ·
                    refine ⟨1212967964481341343986233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469162477233820501259909 1212967964481341343986233)
                    ·
                      refine ⟨909725973361006007989675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1212967964481341343986233 909725973361006007989675)
                      ·
                        rfl

theorem cell23_1771685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_1771685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771685 prefixEnd_1771685 := by exact prefixLift 1771685
  have htrace : WordTrace (prefixWord ++ tailWord_1771685) baseStart_1771685 baseEnd_1771685 := by
    simpa [prefixWord, tailWord_1771685, baseEnd_1771685] using wordTrace_append hprefix tailTrace_1771685
  have hstable : (prefixWord ++ tailWord_1771685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771685).length < 2 ^ (prefixWord ++ tailWord_1771685).sum := by decide
  have hdescent : baseEnd_1771685 < baseStart_1771685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771698 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1771698 : Nat := 118140960795 + 1771698 * 2 ^ 59
def prefixEnd_1771698 : Nat := 4983230072969 + 3 ^ 40 * 1771698 * 2
def baseEnd_1771698 : Nat := 909732648609514457127115

theorem tailTrace_1771698 : CollatzResearch.WordTrace tailWord_1771698 prefixEnd_1771698 909732648609514457127115 := by
  unfold tailWord_1771698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154783683862050693432937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43079423156965468515821165 16154783683862050693432937)
  ·
    refine ⟨12116087762896538020074703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16154783683862050693432937 12116087762896538020074703)
    ·
      refine ⟨18174131644344807030112055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116087762896538020074703 18174131644344807030112055)
      ·
        refine ⟨27261197466517210545168083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174131644344807030112055 27261197466517210545168083)
        ·
          refine ⟨40891796199775815817752125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27261197466517210545168083 40891796199775815817752125)
          ·
            refine ⟨15334423574915930931657047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40891796199775815817752125 15334423574915930931657047)
            ·
              refine ⟨23001635362373896397485571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334423574915930931657047 23001635362373896397485571)
              ·
                refine ⟨34502453043560844596228357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23001635362373896397485571 34502453043560844596228357)
                ·
                  refine ⟨6469209945667658361792817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34502453043560844596228357 6469209945667658361792817)
                  ·
                    refine ⟨4851907459250743771344613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469209945667658361792817 4851907459250743771344613)
                    ·
                      refine ⟨909732648609514457127115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4851907459250743771344613 909732648609514457127115)
                      ·
                        rfl

theorem cell23_1771698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1771698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771698 prefixEnd_1771698 := by exact prefixLift 1771698
  have htrace : WordTrace (prefixWord ++ tailWord_1771698) baseStart_1771698 baseEnd_1771698 := by
    simpa [prefixWord, tailWord_1771698, baseEnd_1771698] using wordTrace_append hprefix tailTrace_1771698
  have hstable : (prefixWord ++ tailWord_1771698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771698).length < 2 ^ (prefixWord ++ tailWord_1771698).sum := by decide
  have hdescent : baseEnd_1771698 < baseStart_1771698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771738 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1771738 : Nat := 118140960795 + 1771738 * 2 ^ 59
def prefixEnd_1771738 : Nat := 4983230072969 + 3 ^ 40 * 1771738 * 2
def baseEnd_1771738 : Nat := 303251062611898100208977

theorem tailTrace_1771738 : CollatzResearch.WordTrace tailWord_1771738 prefixEnd_1771738 303251062611898100208977 := by
  unfold tailWord_1771738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155148413825822401296967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43080395770202193070125245 16155148413825822401296967)
  ·
    refine ⟨24232722620738733601945451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16155148413825822401296967 24232722620738733601945451)
    ·
      refine ⟨36349083931108100402918177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24232722620738733601945451 36349083931108100402918177)
      ·
        refine ⟨27261812948331075302188633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36349083931108100402918177 27261812948331075302188633)
        ·
          refine ⟨20446359711248306476641475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27261812948331075302188633 20446359711248306476641475)
          ·
            refine ⟨30669539566872459714962213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446359711248306476641475 30669539566872459714962213)
            ·
              refine ⟨5750538668788586196555415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30669539566872459714962213 5750538668788586196555415)
              ·
                refine ⟨8625808003182879294833123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750538668788586196555415 8625808003182879294833123)
                ·
                  refine ⟨12938712004774318942249685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625808003182879294833123 12938712004774318942249685)
                  ·
                    refine ⟨303251062611898100208977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12938712004774318942249685 303251062611898100208977)
                    ·
                      rfl

theorem cell23_1771738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1771738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771738 prefixEnd_1771738 := by exact prefixLift 1771738
  have htrace : WordTrace (prefixWord ++ tailWord_1771738) baseStart_1771738 baseEnd_1771738 := by
    simpa [prefixWord, tailWord_1771738, baseEnd_1771738] using wordTrace_append hprefix tailTrace_1771738
  have hstable : (prefixWord ++ tailWord_1771738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771738).length < 2 ^ (prefixWord ++ tailWord_1771738).sum := by decide
  have hdescent : baseEnd_1771738 < baseStart_1771738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771748 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1771748 : Nat := 118140960795 + 1771748 * 2 ^ 59
def prefixEnd_1771748 : Nat := 4983230072969 + 3 ^ 40 * 1771748 * 2
def baseEnd_1771748 : Nat := 909758322642239261501885

theorem tailTrace_1771748 : CollatzResearch.WordTrace tailWord_1771748 prefixEnd_1771748 909758322642239261501885 := by
  unfold tailWord_1771748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32310479192633530656525949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43080638923511374208701265 32310479192633530656525949)
  ·
    refine ⟨12116429697237573996197231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32310479192633530656525949 12116429697237573996197231)
    ·
      refine ⟨18174644545856360994295847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116429697237573996197231 18174644545856360994295847)
      ·
        refine ⟨27261966818784541491443771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174644545856360994295847 27261966818784541491443771)
        ·
          refine ⟨40892950228176812237165657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27261966818784541491443771 40892950228176812237165657)
          ·
            refine ⟨30669712671132609177874243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40892950228176812237165657 30669712671132609177874243)
            ·
              refine ⟨46004569006698913766811365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30669712671132609177874243 46004569006698913766811365)
              ·
                refine ⟨8625856688756046331277131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46004569006698913766811365 8625856688756046331277131)
                ·
                  refine ⟨12938785033134069496915697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625856688756046331277131 12938785033134069496915697)
                  ·
                    refine ⟨9704088774850552122686773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12938785033134069496915697 9704088774850552122686773)
                    ·
                      refine ⟨909758322642239261501885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9704088774850552122686773 909758322642239261501885)
                      ·
                        rfl

theorem cell23_1771748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1771748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771748 prefixEnd_1771748 := by exact prefixLift 1771748
  have htrace : WordTrace (prefixWord ++ tailWord_1771748) baseStart_1771748 baseEnd_1771748 := by
    simpa [prefixWord, tailWord_1771748, baseEnd_1771748] using wordTrace_append hprefix tailTrace_1771748
  have hstable : (prefixWord ++ tailWord_1771748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771748).length < 2 ^ (prefixWord ++ tailWord_1771748).sum := by decide
  have hdescent : baseEnd_1771748 < baseStart_1771748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771775 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 6, 2]
def baseStart_1771775 : Nat := 118140960795 + 1771775 * 2 ^ 59
def prefixEnd_1771775 : Nat := 4983230072969 + 3 ^ 40 * 1771775 * 2
def baseEnd_1771775 : Nat := 909772186619910655864261

theorem tailTrace_1771775 : CollatzResearch.WordTrace tailWord_1771775 prefixEnd_1771775 909772186619910655864261 := by
  unfold tailWord_1771775
  simp only [CollatzResearch.WordTrace]
  refine ⟨64621943156169244924284779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43081295437446163282856519 64621943156169244924284779)
  ·
    refine ⟨96932914734253867386427169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64621943156169244924284779 96932914734253867386427169)
    ·
      refine ⟨72699686050690400539820377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96932914734253867386427169 72699686050690400539820377)
      ·
        refine ⟨54524764538017800404865283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72699686050690400539820377 54524764538017800404865283)
        ·
          refine ⟨81787146807026700607297925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54524764538017800404865283 81787146807026700607297925)
          ·
            refine ⟨15335090026317506363868361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81787146807026700607297925 15335090026317506363868361)
            ·
              refine ⟨11501317519738129772901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15335090026317506363868361 11501317519738129772901271)
              ·
                refine ⟨17251976279607194659351907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501317519738129772901271 17251976279607194659351907)
                ·
                  refine ⟨25877964419410791989027861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251976279607194659351907 25877964419410791989027861)
                  ·
                    refine ⟨1213029582159880874485681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25877964419410791989027861 1213029582159880874485681)
                    ·
                      refine ⟨909772186619910655864261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213029582159880874485681 909772186619910655864261)
                      ·
                        rfl

theorem cell23_1771775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_1771775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771775 prefixEnd_1771775 := by exact prefixLift 1771775
  have htrace : WordTrace (prefixWord ++ tailWord_1771775) baseStart_1771775 baseEnd_1771775 := by
    simpa [prefixWord, tailWord_1771775, baseEnd_1771775] using wordTrace_append hprefix tailTrace_1771775
  have hstable : (prefixWord ++ tailWord_1771775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771775).length < 2 ^ (prefixWord ++ tailWord_1771775).sum := by decide
  have hdescent : baseEnd_1771775 < baseStart_1771775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771812 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1771812 : Nat := 118140960795 + 1771812 * 2 ^ 59
def prefixEnd_1771812 : Nat := 4983230072969 + 3 ^ 40 * 1771812 * 2
def baseEnd_1771812 : Nat := 909791185404127011101591

theorem tailTrace_1771812 : CollatzResearch.WordTrace tailWord_1771812 prefixEnd_1771812 909791185404127011101591 := by
  unfold tailWord_1771812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32311646328517600121690845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43082195104690133495587793 32311646328517600121690845)
  ·
    refine ⟨12116867373194100045634067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32311646328517600121690845 12116867373194100045634067)
    ·
      refine ⟨18175301059791150068451101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116867373194100045634067 18175301059791150068451101)
      ·
        refine ⟨6815737897421681275669163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18175301059791150068451101 6815737897421681275669163)
        ·
          refine ⟨10223606846132521913503745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6815737897421681275669163 10223606846132521913503745)
          ·
            refine ⟨7667705134599391435127809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10223606846132521913503745 7667705134599391435127809)
            ·
              refine ⟨5750778850949543576345857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667705134599391435127809 5750778850949543576345857)
              ·
                refine ⟨4313084138212157682259393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750778850949543576345857 4313084138212157682259393)
                ·
                  refine ⟨3234813103659118261694545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313084138212157682259393 3234813103659118261694545)
                  ·
                    refine ⟨2426109827744338696270909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3234813103659118261694545 2426109827744338696270909)
                    ·
                      refine ⟨909791185404127011101591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2426109827744338696270909 909791185404127011101591)
                      ·
                        rfl

theorem cell23_1771812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1771812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771812 prefixEnd_1771812 := by exact prefixLift 1771812
  have htrace : WordTrace (prefixWord ++ tailWord_1771812) baseStart_1771812 baseEnd_1771812 := by
    simpa [prefixWord, tailWord_1771812, baseEnd_1771812] using wordTrace_append hprefix tailTrace_1771812
  have hstable : (prefixWord ++ tailWord_1771812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771812).length < 2 ^ (prefixWord ++ tailWord_1771812).sum := by decide
  have hdescent : baseEnd_1771812 < baseStart_1771812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771852 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_1771852 : Nat := 118140960795 + 1771852 * 2 ^ 59
def prefixEnd_1771852 : Nat := 4983230072969 + 3 ^ 40 * 1771852 * 2
def baseEnd_1771852 : Nat := 909811724630306854601407

theorem tailTrace_1771852 : CollatzResearch.WordTrace tailWord_1771852 prefixEnd_1771852 909811724630306854601407 := by
  unfold tailWord_1771852
  simp only [CollatzResearch.WordTrace]
  refine ⟨32312375788445143537418905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43083167717926858049891873 32312375788445143537418905)
  ·
    refine ⟨24234281841333857653064179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32312375788445143537418905 24234281841333857653064179)
    ·
      refine ⟨36351422762000786479596269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24234281841333857653064179 36351422762000786479596269)
      ·
        refine ⟨13631783535750294929848601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36351422762000786479596269 13631783535750294929848601)
        ·
          refine ⟨10223837651812721197386451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631783535750294929848601 10223837651812721197386451)
          ·
            refine ⟨15335756477719081796079677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223837651812721197386451 15335756477719081796079677)
            ·
              refine ⟨5750908679144655673529879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15335756477719081796079677 5750908679144655673529879)
              ·
                refine ⟨8626363018716983510294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5750908679144655673529879 8626363018716983510294819)
                ·
                  refine ⟨12939544528075475265442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8626363018716983510294819 12939544528075475265442229)
                  ·
                    refine ⟨1213082299507075806135209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12939544528075475265442229 1213082299507075806135209)
                    ·
                      refine ⟨909811724630306854601407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213082299507075806135209 909811724630306854601407)
                      ·
                        rfl

theorem cell23_1771852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_1771852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771852 prefixEnd_1771852 := by exact prefixLift 1771852
  have htrace : WordTrace (prefixWord ++ tailWord_1771852) baseStart_1771852 baseEnd_1771852 := by
    simpa [prefixWord, tailWord_1771852, baseEnd_1771852] using wordTrace_append hprefix tailTrace_1771852
  have hstable : (prefixWord ++ tailWord_1771852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771852).length < 2 ^ (prefixWord ++ tailWord_1771852).sum := by decide
  have hdescent : baseEnd_1771852 < baseStart_1771852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771870 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1771870 : Nat := 118140960795 + 1771870 * 2 ^ 59
def prefixEnd_1771870 : Nat := 4983230072969 + 3 ^ 40 * 1771870 * 2
def baseEnd_1771870 : Nat := 303273655760695928058775

theorem tailTrace_1771870 : CollatzResearch.WordTrace tailWord_1771870 prefixEnd_1771870 303273655760695928058775 := by
  unfold tailWord_1771870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078176011353134518624133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43083605393883384099328709 8078176011353134518624133)
  ·
    refine ⟨1514658002128712722242025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8078176011353134518624133 1514658002128712722242025)
    ·
      refine ⟨1135993501596534541681519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514658002128712722242025 1135993501596534541681519)
      ·
        refine ⟨1703990252394801812522279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135993501596534541681519 1703990252394801812522279)
        ·
          refine ⟨2555985378592202718783419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703990252394801812522279 2555985378592202718783419)
          ·
            refine ⟨3833978067888304078175129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555985378592202718783419 3833978067888304078175129)
            ·
              refine ⟨2875483550916228058631347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833978067888304078175129 2875483550916228058631347)
              ·
                refine ⟨4313225326374342087947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875483550916228058631347 4313225326374342087947021)
                ·
                  refine ⟨1617459497390378282980133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4313225326374342087947021 1617459497390378282980133)
                  ·
                    refine ⟨303273655760695928058775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617459497390378282980133 303273655760695928058775)
                    ·
                      rfl

theorem cell23_1771870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1771870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771870 prefixEnd_1771870 := by exact prefixLift 1771870
  have htrace : WordTrace (prefixWord ++ tailWord_1771870) baseStart_1771870 baseEnd_1771870 := by
    simpa [prefixWord, tailWord_1771870, baseEnd_1771870] using wordTrace_append hprefix tailTrace_1771870
  have hstable : (prefixWord ++ tailWord_1771870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771870).length < 2 ^ (prefixWord ++ tailWord_1771870).sum := by decide
  have hdescent : baseEnd_1771870 < baseStart_1771870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771895 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1771895 : Nat := 118140960795 + 1771895 * 2 ^ 59
def prefixEnd_1771895 : Nat := 4983230072969 + 3 ^ 40 * 1771895 * 2
def baseEnd_1771895 : Nat := 909833804298450186363709

theorem tailTrace_1771895 : CollatzResearch.WordTrace tailWord_1771895 prefixEnd_1771895 909833804298450186363709 := by
  unfold tailWord_1771895
  simp only [CollatzResearch.WordTrace]
  refine ⟨64626319915734505418653139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43084213277156336945768759 64626319915734505418653139)
  ·
    refine ⟨96939479873601758127979709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64626319915734505418653139 96939479873601758127979709)
    ·
      refine ⟨36352304952600659297992391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96939479873601758127979709 36352304952600659297992391)
      ·
        refine ⟨54528457428900988946988587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36352304952600659297992391 54528457428900988946988587)
        ·
          refine ⟨81792686143351483420482881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54528457428900988946988587 81792686143351483420482881)
          ·
            refine ⟨61344514607513612565362161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81792686143351483420482881 61344514607513612565362161)
            ·
              refine ⟨46008385955635209424021621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61344514607513612565362161 46008385955635209424021621)
              ·
                refine ⟨4313286183340800883502027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46008385955635209424021621 4313286183340800883502027)
                ·
                  refine ⟨6469929275011201325253041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313286183340800883502027 6469929275011201325253041)
                  ·
                    refine ⟨4852446956258400993939781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469929275011201325253041 4852446956258400993939781)
                    ·
                      refine ⟨909833804298450186363709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4852446956258400993939781 909833804298450186363709)
                      ·
                        rfl

theorem cell23_1771895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1771895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771895 prefixEnd_1771895 := by exact prefixLift 1771895
  have htrace : WordTrace (prefixWord ++ tailWord_1771895) baseStart_1771895 baseEnd_1771895 := by
    simpa [prefixWord, tailWord_1771895, baseEnd_1771895] using wordTrace_append hprefix tailTrace_1771895
  have hstable : (prefixWord ++ tailWord_1771895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771895).length < 2 ^ (prefixWord ++ tailWord_1771895).sum := by decide
  have hdescent : baseEnd_1771895 < baseStart_1771895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771899 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 3, 2, 2]
def baseStart_1771899 : Nat := 118140960795 + 1771899 * 2 ^ 59
def prefixEnd_1771899 : Nat := 4983230072969 + 3 ^ 40 * 1771899 * 2
def baseEnd_1771899 : Nat := 909835858221068170713691

theorem tailTrace_1771899 : CollatzResearch.WordTrace tailWord_1771899 prefixEnd_1771899 909835858221068170713691 := by
  unfold tailWord_1771899
  simp only [CollatzResearch.WordTrace]
  refine ⟨64626465807720014101798751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43084310538480009401199167 64626465807720014101798751)
  ·
    refine ⟨96939698711580021152698127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64626465807720014101798751 96939698711580021152698127)
    ·
      refine ⟨145409548067370031729047191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96939698711580021152698127 145409548067370031729047191)
      ·
        refine ⟨218114322101055047593570787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145409548067370031729047191 218114322101055047593570787)
        ·
          refine ⟨327171483151582571390356181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218114322101055047593570787 327171483151582571390356181)
          ·
            refine ⟨7668081636365216516961473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 327171483151582571390356181 7668081636365216516961473)
            ·
              refine ⟨5751061227273912387721105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7668081636365216516961473 5751061227273912387721105)
              ·
                refine ⟨4313295920455434290790829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751061227273912387721105 4313295920455434290790829)
                ·
                  refine ⟨1617485970170787859046561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4313295920455434290790829 1617485970170787859046561)
                  ·
                    refine ⟨1213114477628090894284921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617485970170787859046561 1213114477628090894284921)
                    ·
                      refine ⟨909835858221068170713691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213114477628090894284921 909835858221068170713691)
                      ·
                        rfl

theorem cell23_1771899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2, 2].length) (baseStart_1771899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771899 prefixEnd_1771899 := by exact prefixLift 1771899
  have htrace : WordTrace (prefixWord ++ tailWord_1771899) baseStart_1771899 baseEnd_1771899 := by
    simpa [prefixWord, tailWord_1771899, baseEnd_1771899] using wordTrace_append hprefix tailTrace_1771899
  have hstable : (prefixWord ++ tailWord_1771899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771899).length < 2 ^ (prefixWord ++ tailWord_1771899).sum := by decide
  have hdescent : baseEnd_1771899 < baseStart_1771899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771933 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1771933 : Nat := 118140960795 + 1771933 * 2 ^ 59
def prefixEnd_1771933 : Nat := 4983230072969 + 3 ^ 40 * 1771933 * 2
def baseEnd_1771933 : Nat := 909853316563321037688535

theorem tailTrace_1771933 : CollatzResearch.WordTrace tailWord_1771933 prefixEnd_1771933 909853316563321037688535 := by
  unfold tailWord_1771933
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627705889596837908536453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43085137259731225272357635 64627705889596837908536453)
  ·
    refine ⟨12117694854299407107850585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64627705889596837908536453 12117694854299407107850585)
    ·
      refine ⟨9088271140724555330887939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117694854299407107850585 9088271140724555330887939)
      ·
        refine ⟨13632406711086832996331909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088271140724555330887939 13632406711086832996331909)
        ·
          refine ⟨2556076258328781186812233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13632406711086832996331909 2556076258328781186812233)
          ·
            refine ⟨1917057193746585890109175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2556076258328781186812233 1917057193746585890109175)
            ·
              refine ⟨2875585790619878835163763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917057193746585890109175 2875585790619878835163763)
              ·
                refine ⟨4313378685929818252745645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875585790619878835163763 4313378685929818252745645)
                ·
                  refine ⟨1617517007223681844779617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4313378685929818252745645 1617517007223681844779617)
                  ·
                    refine ⟨1213137755417761383584713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617517007223681844779617 1213137755417761383584713)
                    ·
                      refine ⟨909853316563321037688535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213137755417761383584713 909853316563321037688535)
                      ·
                        rfl

theorem cell23_1771933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1771933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771933 prefixEnd_1771933 := by exact prefixLift 1771933
  have htrace : WordTrace (prefixWord ++ tailWord_1771933) baseStart_1771933 baseEnd_1771933 := by
    simpa [prefixWord, tailWord_1771933, baseEnd_1771933] using wordTrace_append hprefix tailTrace_1771933
  have hstable : (prefixWord ++ tailWord_1771933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771933).length < 2 ^ (prefixWord ++ tailWord_1771933).sum := by decide
  have hdescent : baseEnd_1771933 < baseStart_1771933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771935 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 7]
def baseStart_1771935 : Nat := 118140960795 + 1771935 * 2 ^ 59
def prefixEnd_1771935 : Nat := 4983230072969 + 3 ^ 40 * 1771935 * 2
def baseEnd_1771935 : Nat := 303284781174876676621175

theorem tailTrace_1771935 : CollatzResearch.WordTrace tailWord_1771935 prefixEnd_1771935 303284781174876676621175 := by
  unfold tailWord_1771935
  simp only [CollatzResearch.WordTrace]
  refine ⟨64627778835589592250109259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43085185890393061500072839 64627778835589592250109259)
  ·
    refine ⟨96941668253384388375163889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64627778835589592250109259 96941668253384388375163889)
    ·
      refine ⟨72706251190038291281372917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96941668253384388375163889 72706251190038291281372917)
      ·
        refine ⟨6816211049066089807628711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72706251190038291281372917 6816211049066089807628711)
        ·
          refine ⟨10224316573599134711443067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816211049066089807628711 10224316573599134711443067)
          ·
            refine ⟨15336474860398702067164601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224316573599134711443067 15336474860398702067164601)
            ·
              refine ⟨11502356145299026550373451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15336474860398702067164601 11502356145299026550373451)
              ·
                refine ⟨17253534217948539825560177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11502356145299026550373451 17253534217948539825560177)
                ·
                  refine ⟨12940150663461404869170133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17253534217948539825560177 12940150663461404869170133)
                  ·
                    refine ⟨303284781174876676621175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12940150663461404869170133 303284781174876676621175)
                    ·
                      rfl

theorem cell23_1771935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_1771935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771935 prefixEnd_1771935 := by exact prefixLift 1771935
  have htrace : WordTrace (prefixWord ++ tailWord_1771935) baseStart_1771935 baseEnd_1771935 := by
    simpa [prefixWord, tailWord_1771935, baseEnd_1771935] using wordTrace_append hprefix tailTrace_1771935
  have hstable : (prefixWord ++ tailWord_1771935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771935).length < 2 ^ (prefixWord ++ tailWord_1771935).sum := by decide
  have hdescent : baseEnd_1771935 < baseStart_1771935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771959 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_1771959 : Nat := 118140960795 + 1771959 * 2 ^ 59
def prefixEnd_1771959 : Nat := 4983230072969 + 3 ^ 40 * 1771959 * 2
def baseEnd_1771959 : Nat := 909866667060337935963415

theorem tailTrace_1771959 : CollatzResearch.WordTrace tailWord_1771959 prefixEnd_1771959 909866667060337935963415 := by
  unfold tailWord_1771959
  simp only [CollatzResearch.WordTrace]
  refine ⟨64628654187502644348982931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43085769458335096232655287 64628654187502644348982931)
  ·
    refine ⟨96942981281253966523474397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64628654187502644348982931 96942981281253966523474397)
    ·
      refine ⟨36353617980470237446302899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96942981281253966523474397 36353617980470237446302899)
      ·
        refine ⟨54530426970705356169454349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36353617980470237446302899 54530426970705356169454349)
        ·
          refine ⟨20448910114014508563545381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54530426970705356169454349 20448910114014508563545381)
          ·
            refine ⟨3834170646377720355664759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20448910114014508563545381 3834170646377720355664759)
            ·
              refine ⟨5751255969566580533497139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834170646377720355664759 5751255969566580533497139)
              ·
                refine ⟨8626883954349870800245709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751255969566580533497139 8626883954349870800245709)
                ·
                  refine ⟨3235081482881201550092141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8626883954349870800245709 3235081482881201550092141)
                  ·
                    refine ⟨1213155556080450581284553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235081482881201550092141 1213155556080450581284553)
                    ·
                      refine ⟨909866667060337935963415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213155556080450581284553 909866667060337935963415)
                      ·
                        rfl

theorem cell23_1771959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_1771959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771959 prefixEnd_1771959 := by exact prefixLift 1771959
  have htrace : WordTrace (prefixWord ++ tailWord_1771959) baseStart_1771959 baseEnd_1771959 := by
    simpa [prefixWord, tailWord_1771959, baseEnd_1771959] using wordTrace_append hprefix tailTrace_1771959
  have hstable : (prefixWord ++ tailWord_1771959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771959).length < 2 ^ (prefixWord ++ tailWord_1771959).sum := by decide
  have hdescent : baseEnd_1771959 < baseStart_1771959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1771985 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1771985 : Nat := 118140960795 + 1771985 * 2 ^ 59
def prefixEnd_1771985 : Nat := 4983230072969 + 3 ^ 40 * 1771985 * 2
def baseEnd_1771985 : Nat := 909880017557354834238295

theorem tailTrace_1771985 : CollatzResearch.WordTrace tailWord_1771985 prefixEnd_1771985 909880017557354834238295 := by
  unfold tailWord_1771985
  simp only [CollatzResearch.WordTrace]
  refine ⟨64629602485408450789429409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43086401656938967192952939 64629602485408450789429409)
  ·
    refine ⟨48472201864056338092072057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64629602485408450789429409 48472201864056338092072057)
    ·
      refine ⟨36354151398042253569054043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48472201864056338092072057 36354151398042253569054043)
      ·
        refine ⟨54531227097063380353581065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36354151398042253569054043 54531227097063380353581065)
        ·
          refine ⟨40898420322797535265185799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54531227097063380353581065 40898420322797535265185799)
          ·
            refine ⟨61347630484196302897778699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40898420322797535265185799 61347630484196302897778699)
            ·
              refine ⟨92021445726294454346668049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61347630484196302897778699 92021445726294454346668049)
              ·
                refine ⟨69016084294720840760001037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92021445726294454346668049 69016084294720840760001037)
                ·
                  refine ⟨25881031610520315285000389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69016084294720840760001037 25881031610520315285000389)
                  ·
                    refine ⟨4852693426972559115937573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25881031610520315285000389 4852693426972559115937573)
                    ·
                      refine ⟨909880017557354834238295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4852693426972559115937573 909880017557354834238295)
                      ·
                        rfl

theorem cell23_1771985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1771985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1771985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1771985 prefixEnd_1771985 := by exact prefixLift 1771985
  have htrace : WordTrace (prefixWord ++ tailWord_1771985) baseStart_1771985 baseEnd_1771985 := by
    simpa [prefixWord, tailWord_1771985, baseEnd_1771985] using wordTrace_append hprefix tailTrace_1771985
  have hstable : (prefixWord ++ tailWord_1771985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1771985).length < 2 ^ (prefixWord ++ tailWord_1771985).sum := by decide
  have hdescent : baseEnd_1771985 < baseStart_1771985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1771985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772029 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 5]
def baseStart_1772029 : Nat := 118140960795 + 1772029 * 2 ^ 59
def prefixEnd_1772029 : Nat := 4983230072969 + 3 ^ 40 * 1772029 * 2
def baseEnd_1772029 : Nat := 101100290078461406898677

theorem tailTrace_1772029 : CollatzResearch.WordTrace tailWord_1772029 prefixEnd_1772029 101100290078461406898677 := by
  unfold tailWord_1772029
  simp only [CollatzResearch.WordTrace]
  refine ⟨64631207297249046304031141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43087471531499364202687427 64631207297249046304031141)
  ·
    refine ⟨12118351368234196182005839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64631207297249046304031141 12118351368234196182005839)
    ·
      refine ⟨18177527052351294273008759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118351368234196182005839 18177527052351294273008759)
      ·
        refine ⟨27266290578526941409513139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18177527052351294273008759 27266290578526941409513139)
        ·
          refine ⟨40899435867790412114269709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27266290578526941409513139 40899435867790412114269709)
          ·
            refine ⟨15337288450421404542851141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40899435867790412114269709 15337288450421404542851141)
            ·
              refine ⟨2875741584454013351784589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15337288450421404542851141 2875741584454013351784589)
              ·
                refine ⟨1078403094170255006919221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2875741584454013351784589 1078403094170255006919221)
                ·
                  refine ⟨101100290078461406898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1078403094170255006919221 101100290078461406898677)
                  ·
                    rfl

theorem cell23_1772029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_1772029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772029 prefixEnd_1772029 := by exact prefixLift 1772029
  have htrace : WordTrace (prefixWord ++ tailWord_1772029) baseStart_1772029 baseEnd_1772029 := by
    simpa [prefixWord, tailWord_1772029, baseEnd_1772029] using wordTrace_append hprefix tailTrace_1772029
  have hstable : (prefixWord ++ tailWord_1772029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772029).length < 2 ^ (prefixWord ++ tailWord_1772029).sum := by decide
  have hdescent : baseEnd_1772029 < baseStart_1772029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772042 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1772042 : Nat := 118140960795 + 1772042 * 2 ^ 59
def prefixEnd_1772042 : Nat := 4983230072969 + 3 ^ 40 * 1772042 * 2
def baseEnd_1772042 : Nat := 303303095318220370408511

theorem tailTrace_1772042 : CollatzResearch.WordTrace tailWord_1772042 prefixEnd_1772042 303303095318220370408511 := by
  unfold tailWord_1772042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16157920361550487381063595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43087787630801299682836253 16157920361550487381063595)
  ·
    refine ⟨24236880542325731071595393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16157920361550487381063595 24236880542325731071595393)
    ·
      refine ⟨18177660406744298303696545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24236880542325731071595393 18177660406744298303696545)
      ·
        refine ⟨13633245305058223727772409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18177660406744298303696545 13633245305058223727772409)
        ·
          refine ⟨10224933978793667795829307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13633245305058223727772409 10224933978793667795829307)
          ·
            refine ⟨15337400968190501693743961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224933978793667795829307 15337400968190501693743961)
            ·
              refine ⟨11503050726142876270307971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15337400968190501693743961 11503050726142876270307971)
              ·
                refine ⟨17254576089214314405461957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503050726142876270307971 17254576089214314405461957)
                ·
                  refine ⟨3235233016727683951024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17254576089214314405461957 3235233016727683951024117)
                  ·
                    refine ⟨303303095318220370408511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3235233016727683951024117 303303095318220370408511)
                    ·
                      rfl

theorem cell23_1772042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1772042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772042 prefixEnd_1772042 := by exact prefixLift 1772042
  have htrace : WordTrace (prefixWord ++ tailWord_1772042) baseStart_1772042 baseEnd_1772042 := by
    simpa [prefixWord, tailWord_1772042, baseEnd_1772042] using wordTrace_append hprefix tailTrace_1772042
  have hstable : (prefixWord ++ tailWord_1772042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772042).length < 2 ^ (prefixWord ++ tailWord_1772042).sum := by decide
  have hdescent : baseEnd_1772042 < baseStart_1772042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772106 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1772106 : Nat := 118140960795 + 1772106 * 2 ^ 59
def prefixEnd_1772106 : Nat := 4983230072969 + 3 ^ 40 * 1772106 * 2
def baseEnd_1772106 : Nat := 303314049572182953608413

theorem tailTrace_1772106 : CollatzResearch.WordTrace tailWord_1772106 prefixEnd_1772106 303314049572182953608413 := by
  unfold tailWord_1772106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16158503929492522113646043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43089343811980058969722781 16158503929492522113646043)
  ·
    refine ⟨24237755894238783170469065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16158503929492522113646043 24237755894238783170469065)
    ·
      refine ⟨18178316920679087377851799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24237755894238783170469065 18178316920679087377851799)
      ·
        refine ⟨27267475381018631066777699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178316920679087377851799 27267475381018631066777699)
        ·
          refine ⟨40901213071527946600166549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27267475381018631066777699 40901213071527946600166549)
          ·
            refine ⟨1917244362727872496882807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40901213071527946600166549 1917244362727872496882807)
            ·
              refine ⟨2875866544091808745324211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917244362727872496882807 2875866544091808745324211)
              ·
                refine ⟨4313799816137713117986317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875866544091808745324211 4313799816137713117986317)
                ·
                  refine ⟨1617674931051642419244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4313799816137713117986317 1617674931051642419244869)
                  ·
                    refine ⟨303314049572182953608413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617674931051642419244869 303314049572182953608413)
                    ·
                      rfl

theorem cell23_1772106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1772106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772106 prefixEnd_1772106 := by exact prefixLift 1772106
  have htrace : WordTrace (prefixWord ++ tailWord_1772106) baseStart_1772106 baseEnd_1772106 := by
    simpa [prefixWord, tailWord_1772106, baseEnd_1772106] using wordTrace_append hprefix tailTrace_1772106
  have hstable : (prefixWord ++ tailWord_1772106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772106).length < 2 ^ (prefixWord ++ tailWord_1772106).sum := by decide
  have hdescent : baseEnd_1772106 < baseStart_1772106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772112 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_1772112 : Nat := 118140960795 + 1772112 * 2 ^ 59
def prefixEnd_1772112 : Nat := 4983230072969 + 3 ^ 40 * 1772112 * 2
def baseEnd_1772112 : Nat := 909945229600475837350211

theorem tailTrace_1772112 : CollatzResearch.WordTrace tailWord_1772112 prefixEnd_1772112 909945229600475837350211 := by
  unfold tailWord_1772112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317117277974175739651295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43089489703965567652868393 32317117277974175739651295)
  ·
    refine ⟨48475675916961263609476943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32317117277974175739651295 48475675916961263609476943)
    ·
      refine ⟨72713513875441895414215415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48475675916961263609476943 72713513875441895414215415)
      ·
        refine ⟨109070270813162843121323123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72713513875441895414215415 109070270813162843121323123)
        ·
          refine ⟨163605406219744264681984685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109070270813162843121323123 163605406219744264681984685)
          ·
            refine ⟨61352027332404099255744257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163605406219744264681984685 61352027332404099255744257)
            ·
              refine ⟨46014020499303074441808193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61352027332404099255744257 46014020499303074441808193)
              ·
                refine ⟨34510515374477305831356145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46014020499303074441808193 34510515374477305831356145)
                ·
                  refine ⟨25882886530857979373517109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34510515374477305831356145 25882886530857979373517109)
                  ·
                    refine ⟨2426520612267935566267229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25882886530857979373517109 2426520612267935566267229)
                    ·
                      refine ⟨909945229600475837350211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2426520612267935566267229 909945229600475837350211)
                      ·
                        rfl

theorem cell23_1772112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_1772112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772112 prefixEnd_1772112 := by exact prefixLift 1772112
  have htrace : WordTrace (prefixWord ++ tailWord_1772112) baseStart_1772112 baseEnd_1772112 := by
    simpa [prefixWord, tailWord_1772112, baseEnd_1772112] using wordTrace_append hprefix tailTrace_1772112
  have hstable : (prefixWord ++ tailWord_1772112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772112).length < 2 ^ (prefixWord ++ tailWord_1772112).sum := by decide
  have hdescent : baseEnd_1772112 < baseStart_1772112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772156 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_1772156 : Nat := 118140960795 + 1772156 * 2 ^ 59
def prefixEnd_1772156 : Nat := 4983230072969 + 3 ^ 40 * 1772156 * 2
def baseEnd_1772156 : Nat := 909967822749273665200009

theorem tailTrace_1772156 : CollatzResearch.WordTrace tailWord_1772156 prefixEnd_1772156 909967822749273665200009 := by
  unfold tailWord_1772156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317919683894473496952161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43090559578525964662602881 32317919683894473496952161)
  ·
    refine ⟨24238439762920855122714121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32317919683894473496952161 24238439762920855122714121)
    ·
      refine ⟨18178829822190641342035591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24238439762920855122714121 18178829822190641342035591)
      ·
        refine ⟨27268244733285962013053387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178829822190641342035591 27268244733285962013053387)
        ·
          refine ⟨40902367099928943019580081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27268244733285962013053387 40902367099928943019580081)
          ·
            refine ⟨30676775324946707264685061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40902367099928943019580081 30676775324946707264685061)
            ·
              refine ⟨5751895373427507612128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30676775324946707264685061 5751895373427507612128449)
              ·
                refine ⟨4313921530070630709096337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751895373427507612128449 4313921530070630709096337)
                ·
                  refine ⟨3235441147552973031822253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4313921530070630709096337 3235441147552973031822253)
                  ·
                    refine ⟨1213290430332364886933345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3235441147552973031822253 1213290430332364886933345)
                    ·
                      refine ⟨909967822749273665200009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213290430332364886933345 909967822749273665200009)
                      ·
                        rfl

theorem cell23_1772156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_1772156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772156 prefixEnd_1772156 := by exact prefixLift 1772156
  have htrace : WordTrace (prefixWord ++ tailWord_1772156) baseStart_1772156 baseEnd_1772156 := by
    simpa [prefixWord, tailWord_1772156, baseEnd_1772156] using wordTrace_append hprefix tailTrace_1772156
  have hstable : (prefixWord ++ tailWord_1772156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772156).length < 2 ^ (prefixWord ++ tailWord_1772156).sum := by decide
  have hdescent : baseEnd_1772156 < baseStart_1772156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772157 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1772157 : Nat := 118140960795 + 1772157 * 2 ^ 59
def prefixEnd_1772157 : Nat := 4983230072969 + 3 ^ 40 * 1772157 * 2
def baseEnd_1772157 : Nat := 303322778743309387095835

theorem tailTrace_1772157 : CollatzResearch.WordTrace tailWord_1772157 prefixEnd_1772157 303322778743309387095835 := by
  unfold tailWord_1772157
  simp only [CollatzResearch.WordTrace]
  refine ⟨64635875840785324164690725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43090583893856882776460483 64635875840785324164690725)
  ·
    refine ⟨12119226720147248280879511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64635875840785324164690725 12119226720147248280879511)
    ·
      refine ⟨18178840080220872421319267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12119226720147248280879511 18178840080220872421319267)
      ·
        refine ⟨27268260120331308631978901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178840080220872421319267 27268260120331308631978901)
        ·
          refine ⟨1278199693140530092124011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27268260120331308631978901 1278199693140530092124011)
          ·
            refine ⟨1917299539710795138186017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278199693140530092124011 1917299539710795138186017)
            ·
              refine ⟨1437974654783096353639513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917299539710795138186017 1437974654783096353639513)
              ·
                refine ⟨1078480991087322265229635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437974654783096353639513 1078480991087322265229635)
                ·
                  refine ⟨1617721486630983397844453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078480991087322265229635 1617721486630983397844453)
                  ·
                    refine ⟨303322778743309387095835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617721486630983397844453 303322778743309387095835)
                    ·
                      rfl

theorem cell23_1772157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1772157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772157 prefixEnd_1772157 := by exact prefixLift 1772157
  have htrace : WordTrace (prefixWord ++ tailWord_1772157) baseStart_1772157 baseEnd_1772157 := by
    simpa [prefixWord, tailWord_1772157, baseEnd_1772157] using wordTrace_append hprefix tailTrace_1772157
  have hstable : (prefixWord ++ tailWord_1772157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772157).length < 2 ^ (prefixWord ++ tailWord_1772157).sum := by decide
  have hdescent : baseEnd_1772157 < baseStart_1772157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772169 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 6, 2]
def baseStart_1772169 : Nat := 118140960795 + 1772169 * 2 ^ 59
def prefixEnd_1772169 : Nat := 4983230072969 + 3 ^ 40 * 1772169 * 2
def baseEnd_1772169 : Nat := 909974497997782114337449

theorem tailTrace_1772169 : CollatzResearch.WordTrace tailWord_1772169 prefixEnd_1772169 909974497997782114337449 := by
  unfold tailWord_1772169
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636313516741850214127561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43090875677827900142751707 64636313516741850214127561)
  ·
    refine ⟨48477235137556387660595671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64636313516741850214127561 48477235137556387660595671)
    ·
      refine ⟨72715852706334581490893507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48477235137556387660595671 72715852706334581490893507)
      ·
        refine ⟨109073779059501872236340261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72715852706334581490893507 109073779059501872236340261)
        ·
          refine ⟨20451333573656601044313799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109073779059501872236340261 20451333573656601044313799)
          ·
            refine ⟨30677000360484901566470699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20451333573656601044313799 30677000360484901566470699)
            ·
              refine ⟨46015500540727352349706049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30677000360484901566470699 46015500540727352349706049)
              ·
                refine ⟨34511625405545514262279537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46015500540727352349706049 34511625405545514262279537)
                ·
                  refine ⟨25883719054159135696709653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34511625405545514262279537 25883719054159135696709653)
                  ·
                    refine ⟨1213299330663709485783265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25883719054159135696709653 1213299330663709485783265)
                    ·
                      refine ⟨909974497997782114337449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213299330663709485783265 909974497997782114337449)
                      ·
                        rfl

theorem cell23_1772169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6, 2].length) (baseStart_1772169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772169 prefixEnd_1772169 := by exact prefixLift 1772169
  have htrace : WordTrace (prefixWord ++ tailWord_1772169) baseStart_1772169 baseEnd_1772169 := by
    simpa [prefixWord, tailWord_1772169, baseEnd_1772169] using wordTrace_append hprefix tailTrace_1772169
  have hstable : (prefixWord ++ tailWord_1772169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772169).length < 2 ^ (prefixWord ++ tailWord_1772169).sum := by decide
  have hdescent : baseEnd_1772169 < baseStart_1772169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772213 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1772213 : Nat := 118140960795 + 1772213 * 2 ^ 59
def prefixEnd_1772213 : Nat := 4983230072969 + 3 ^ 40 * 1772213 * 2
def baseEnd_1772213 : Nat := 303332363715526647395749

theorem tailTrace_1772213 : CollatzResearch.WordTrace tailWord_1772213 prefixEnd_1772213 303332363715526647395749 := by
  unfold tailWord_1772213
  simp only [CollatzResearch.WordTrace]
  refine ⟨64637918328582445728729293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43091945552388297152486195 64637918328582445728729293)
  ·
    refine ⟨24239219373218417148273485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64637918328582445728729293 24239219373218417148273485)
    ·
      refine ⟨9089707264956906430602557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24239219373218417148273485 9089707264956906430602557)
      ·
        refine ⟨3408640224358839911475959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9089707264956906430602557 3408640224358839911475959)
        ·
          refine ⟨5112960336538259867213939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408640224358839911475959 5112960336538259867213939)
          ·
            refine ⟨7669440504807389800820909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112960336538259867213939 7669440504807389800820909)
            ·
              refine ⟨2876040189302771175307841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7669440504807389800820909 2876040189302771175307841)
              ·
                refine ⟨2157030141977078381480881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876040189302771175307841 2157030141977078381480881)
                ·
                  refine ⟨1617772606482808786110661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157030141977078381480881 1617772606482808786110661)
                  ·
                    refine ⟨303332363715526647395749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617772606482808786110661 303332363715526647395749)
                    ·
                      rfl

theorem cell23_1772213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1772213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772213 prefixEnd_1772213 := by exact prefixLift 1772213
  have htrace : WordTrace (prefixWord ++ tailWord_1772213) baseStart_1772213 baseEnd_1772213 := by
    simpa [prefixWord, tailWord_1772213, baseEnd_1772213] using wordTrace_append hprefix tailTrace_1772213
  have hstable : (prefixWord ++ tailWord_1772213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772213).length < 2 ^ (prefixWord ++ tailWord_1772213).sum := by decide
  have hdescent : baseEnd_1772213 < baseStart_1772213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772220 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1772220 : Nat := 118140960795 + 1772220 * 2 ^ 59
def prefixEnd_1772220 : Nat := 4983230072969 + 3 ^ 40 * 1772220 * 2
def baseEnd_1772220 : Nat := 910000685511161414799715

theorem tailTrace_1772220 : CollatzResearch.WordTrace tailWord_1772220 prefixEnd_1772220 910000685511161414799715 := by
  unfold tailWord_1772220
  simp only [CollatzResearch.WordTrace]
  refine ⟨32319086819778542962117057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43092115759704723949489409 32319086819778542962117057)
  ·
    refine ⟨24239315114833907221587793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32319086819778542962117057 24239315114833907221587793)
    ·
      refine ⟨18179486336125430416190845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24239315114833907221587793 18179486336125430416190845)
      ·
        refine ⟨6817307376047036406071567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18179486336125430416190845 6817307376047036406071567)
        ·
          refine ⟨10225961064070554609107351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817307376047036406071567 10225961064070554609107351)
          ·
            refine ⟨15338941596105831913661027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225961064070554609107351 15338941596105831913661027)
            ·
              refine ⟨23008412394158747870491541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15338941596105831913661027 23008412394158747870491541)
              ·
                refine ⟨1078519330976191306429291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23008412394158747870491541 1078519330976191306429291)
                ·
                  refine ⟨1617778996464286959643937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078519330976191306429291 1617778996464286959643937)
                  ·
                    refine ⟨1213334247348215219732953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1617778996464286959643937 1213334247348215219732953)
                    ·
                      refine ⟨910000685511161414799715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213334247348215219732953 910000685511161414799715)
                      ·
                        rfl

theorem cell23_1772220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1772220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772220 prefixEnd_1772220 := by exact prefixLift 1772220
  have htrace : WordTrace (prefixWord ++ tailWord_1772220) baseStart_1772220 baseEnd_1772220 := by
    simpa [prefixWord, tailWord_1772220, baseEnd_1772220] using wordTrace_append hprefix tailTrace_1772220
  have hstable : (prefixWord ++ tailWord_1772220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772220).length < 2 ^ (prefixWord ++ tailWord_1772220).sum := by decide
  have hdescent : baseEnd_1772220 < baseStart_1772220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772279 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1772279 : Nat := 118140960795 + 1772279 * 2 ^ 59
def prefixEnd_1772279 : Nat := 4983230072969 + 3 ^ 40 * 1772279 * 2
def baseEnd_1772279 : Nat := 910030980869776683961943

theorem tailTrace_1772279 : CollatzResearch.WordTrace tailWord_1772279 prefixEnd_1772279 910030980869776683961943 := by
  unfold tailWord_1772279
  simp only [CollatzResearch.WordTrace]
  refine ⟨64640325546343339000631891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43093550364228892667087927 64640325546343339000631891)
  ·
    refine ⟨96960488319515008500947837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64640325546343339000631891 96960488319515008500947837)
    ·
      refine ⟨36360183119818128187855439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96960488319515008500947837 36360183119818128187855439)
      ·
        refine ⟨54540274679727192281783159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36360183119818128187855439 54540274679727192281783159)
        ·
          refine ⟨81810412019590788422674739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54540274679727192281783159 81810412019590788422674739)
          ·
            refine ⟨122715618029386182634012109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81810412019590788422674739 122715618029386182634012109)
            ·
              refine ⟨46018356761019818487754541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122715618029386182634012109 46018356761019818487754541)
              ·
                refine ⟨17256883785382431932907953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46018356761019818487754541 17256883785382431932907953)
                ·
                  refine ⟨12942662839036823949680965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17256883785382431932907953 12942662839036823949680965)
                  ·
                    refine ⟨2426749282319404490565181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12942662839036823949680965 2426749282319404490565181)
                    ·
                      refine ⟨910030980869776683961943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2426749282319404490565181 910030980869776683961943)
                      ·
                        rfl

theorem cell23_1772279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1772279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772279 prefixEnd_1772279 := by exact prefixLift 1772279
  have htrace : WordTrace (prefixWord ++ tailWord_1772279) baseStart_1772279 baseEnd_1772279 := by
    simpa [prefixWord, tailWord_1772279, baseEnd_1772279] using wordTrace_append hprefix tailTrace_1772279
  have hstable : (prefixWord ++ tailWord_1772279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772279).length < 2 ^ (prefixWord ++ tailWord_1772279).sum := by decide
  have hdescent : baseEnd_1772279 < baseStart_1772279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772289 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1772289 : Nat := 118140960795 + 1772289 * 2 ^ 59
def prefixEnd_1772289 : Nat := 4983230072969 + 3 ^ 40 * 1772289 * 2
def baseEnd_1772289 : Nat := 910036115676321644836897

theorem tailTrace_1772289 : CollatzResearch.WordTrace tailWord_1772289 prefixEnd_1772289 910036115676321644836897 := by
  unfold tailWord_1772289
  simp only [CollatzResearch.WordTrace]
  refine ⟨64640690276307110708495921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43093793517538073805663947 64640690276307110708495921)
  ·
    refine ⟨48480517707230333031371941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64640690276307110708495921 48480517707230333031371941)
    ·
      refine ⟨9090097070105687443382239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48480517707230333031371941 9090097070105687443382239)
      ·
        refine ⟨13635145605158531165073359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9090097070105687443382239 13635145605158531165073359)
        ·
          refine ⟨20452718407737796747610039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635145605158531165073359 20452718407737796747610039)
          ·
            refine ⟨30679077611606695121415059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452718407737796747610039 30679077611606695121415059)
            ·
              refine ⟨46018616417410042682122589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30679077611606695121415059 46018616417410042682122589)
              ·
                refine ⟨17256981156528766005795971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46018616417410042682122589 17256981156528766005795971)
                ·
                  refine ⟨25885471734793149008693957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17256981156528766005795971 25885471734793149008693957)
                  ·
                    refine ⟨4853525950273715439130117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25885471734793149008693957 4853525950273715439130117)
                    ·
                      refine ⟨910036115676321644836897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4853525950273715439130117 910036115676321644836897)
                      ·
                        rfl

theorem cell23_1772289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1772289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772289 prefixEnd_1772289 := by exact prefixLift 1772289
  have htrace : WordTrace (prefixWord ++ tailWord_1772289) baseStart_1772289 baseEnd_1772289 := by
    simpa [prefixWord, tailWord_1772289, baseEnd_1772289] using wordTrace_append hprefix tailTrace_1772289
  have hstable : (prefixWord ++ tailWord_1772289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772289).length < 2 ^ (prefixWord ++ tailWord_1772289).sum := by decide
  have hdescent : baseEnd_1772289 < baseStart_1772289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772444 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1772444 : Nat := 118140960795 + 1772444 * 2 ^ 59
def prefixEnd_1772444 : Nat := 4983230072969 + 3 ^ 40 * 1772444 * 2
def baseEnd_1772444 : Nat := 303371901725922846132895

theorem tailTrace_1772444 : CollatzResearch.WordTrace tailWord_1772444 prefixEnd_1772444 303371901725922846132895 := by
  unfold tailWord_1772444
  simp only [CollatzResearch.WordTrace]
  refine ⟨32323171795372786090194193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43097562393830381453592257 32323171795372786090194193)
  ·
    refine ⟨24242378846529589567645645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32323171795372786090194193 24242378846529589567645645)
    ·
      refine ⟨9090892067448596087867117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24242378846529589567645645 9090892067448596087867117)
      ·
        refine ⟨3409084525293223532950169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9090892067448596087867117 3409084525293223532950169)
        ·
          refine ⟨2556813393969917649712627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409084525293223532950169 2556813393969917649712627)
          ·
            refine ⟨3835220090954876474568941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556813393969917649712627 3835220090954876474568941)
            ·
              refine ⟨1438207534108078677963353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3835220090954876474568941 1438207534108078677963353)
              ·
                refine ⟨1078655650581059008472515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438207534108078677963353 1078655650581059008472515)
                ·
                  refine ⟨1617983475871588512708773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078655650581059008472515 1617983475871588512708773)
                  ·
                    refine ⟨303371901725922846132895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617983475871588512708773 303371901725922846132895)
                    ·
                      rfl

theorem cell23_1772444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1772444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772444 prefixEnd_1772444 := by exact prefixLift 1772444
  have htrace : WordTrace (prefixWord ++ tailWord_1772444) baseStart_1772444 baseEnd_1772444 := by
    simpa [prefixWord, tailWord_1772444, baseEnd_1772444] using wordTrace_append hprefix tailTrace_1772444
  have hstable : (prefixWord ++ tailWord_1772444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772444).length < 2 ^ (prefixWord ++ tailWord_1772444).sum := by decide
  have hdescent : baseEnd_1772444 < baseStart_1772444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772473 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1772473 : Nat := 118140960795 + 1772473 * 2 ^ 59
def prefixEnd_1772473 : Nat := 4983230072969 + 3 ^ 40 * 1772473 * 2
def baseEnd_1772473 : Nat := 910130596116748924936051

theorem tailTrace_1772473 : CollatzResearch.WordTrace tailWord_1772473 prefixEnd_1772473 910130596116748924936051 := by
  unfold tailWord_1772473
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647401307640510133194073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43098267538427006755462715 64647401307640510133194073)
  ·
    refine ⟨48485550980730382599895555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64647401307640510133194073 48485550980730382599895555)
    ·
      refine ⟨72728326471095573899843333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48485550980730382599895555 72728326471095573899843333)
      ·
        refine ⟨13636561213330420106220625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72728326471095573899843333 13636561213330420106220625)
        ·
          refine ⟨10227420909997815079665469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13636561213330420106220625 10227420909997815079665469)
          ·
            refine ⟨3835282841249180654874551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10227420909997815079665469 3835282841249180654874551)
            ·
              refine ⟨5752924261873770982311827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835282841249180654874551 5752924261873770982311827)
              ·
                refine ⟨8629386392810656473467741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752924261873770982311827 8629386392810656473467741)
                ·
                  refine ⟨3236019897303996177550403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8629386392810656473467741 3236019897303996177550403)
                  ·
                    refine ⟨4854029845955994266325605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3236019897303996177550403 4854029845955994266325605)
                    ·
                      refine ⟨910130596116748924936051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4854029845955994266325605 910130596116748924936051)
                      ·
                        rfl

theorem cell23_1772473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1772473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772473 prefixEnd_1772473 := by exact prefixLift 1772473
  have htrace : WordTrace (prefixWord ++ tailWord_1772473) baseStart_1772473 baseEnd_1772473 := by
    simpa [prefixWord, tailWord_1772473, baseEnd_1772473] using wordTrace_append hprefix tailTrace_1772473
  have hstable : (prefixWord ++ tailWord_1772473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772473).length < 2 ^ (prefixWord ++ tailWord_1772473).sum := by decide
  have hdescent : baseEnd_1772473 < baseStart_1772473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772477 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1772477 : Nat := 118140960795 + 1772477 * 2 ^ 59
def prefixEnd_1772477 : Nat := 4983230072969 + 3 ^ 40 * 1772477 * 2
def baseEnd_1772477 : Nat := 910132650039366909286033

theorem tailTrace_1772477 : CollatzResearch.WordTrace tailWord_1772477 prefixEnd_1772477 910132650039366909286033 := by
  unfold tailWord_1772477
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647547199626018816339685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43098364799750679210893123 64647547199626018816339685)
  ·
    refine ⟨12121415099929878528063691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64647547199626018816339685 12121415099929878528063691)
    ·
      refine ⟨18182122649894817792095537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12121415099929878528063691 18182122649894817792095537)
      ·
        refine ⟨13636591987421113344071653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18182122649894817792095537 13636591987421113344071653)
        ·
          refine ⟨2556860997641458752013435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13636591987421113344071653 2556860997641458752013435)
          ·
            refine ⟨3835291496462188128020153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556860997641458752013435 3835291496462188128020153)
            ·
              refine ⟨2876468622346641096015115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835291496462188128020153 2876468622346641096015115)
              ·
                refine ⟨4314702933519961644022673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876468622346641096015115 4314702933519961644022673)
                ·
                  refine ⟨3236027200139971233017005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4314702933519961644022673 3236027200139971233017005)
                  ·
                    refine ⟨1213510200052489212381377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3236027200139971233017005 1213510200052489212381377)
                    ·
                      refine ⟨910132650039366909286033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213510200052489212381377 910132650039366909286033)
                      ·
                        rfl

theorem cell23_1772477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1772477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772477 prefixEnd_1772477 := by exact prefixLift 1772477
  have htrace : WordTrace (prefixWord ++ tailWord_1772477) baseStart_1772477 baseEnd_1772477 := by
    simpa [prefixWord, tailWord_1772477, baseEnd_1772477] using wordTrace_append hprefix tailTrace_1772477
  have hstable : (prefixWord ++ tailWord_1772477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772477).length < 2 ^ (prefixWord ++ tailWord_1772477).sum := by decide
  have hdescent : baseEnd_1772477 < baseStart_1772477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772500 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1772500 : Nat := 118140960795 + 1772500 * 2 ^ 59
def prefixEnd_1772500 : Nat := 4983230072969 + 3 ^ 40 * 1772500 * 2
def baseEnd_1772500 : Nat := 303381486698140106432809

theorem tailTrace_1772500 : CollatzResearch.WordTrace tailWord_1772500 prefixEnd_1772500 303381486698140106432809 := by
  unfold tailWord_1772500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324193039271346872213477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43098924052361795829617969 32324193039271346872213477)
  ·
    refine ⟨6060786194863377538540027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32324193039271346872213477 6060786194863377538540027)
    ·
      refine ⟨9091179292295066307810041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060786194863377538540027 9091179292295066307810041)
      ·
        refine ⟨6818384469221299730857531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091179292295066307810041 6818384469221299730857531)
        ·
          refine ⟨10227576703831949596286297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6818384469221299730857531 10227576703831949596286297)
          ·
            refine ⟨7670682527873962197214723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10227576703831949596286297 7670682527873962197214723)
            ·
              refine ⟨11506023791810943295822085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670682527873962197214723 11506023791810943295822085)
              ·
                refine ⟨2157379460964551867966641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11506023791810943295822085 2157379460964551867966641)
                ·
                  refine ⟨1618034595723413900974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157379460964551867966641 1618034595723413900974981)
                  ·
                    refine ⟨303381486698140106432809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618034595723413900974981 303381486698140106432809)
                    ·
                      rfl

theorem cell23_1772500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1772500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772500 prefixEnd_1772500 := by exact prefixLift 1772500
  have htrace : WordTrace (prefixWord ++ tailWord_1772500) baseStart_1772500 baseEnd_1772500 := by
    simpa [prefixWord, tailWord_1772500, baseEnd_1772500] using wordTrace_append hprefix tailTrace_1772500
  have hstable : (prefixWord ++ tailWord_1772500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772500).length < 2 ^ (prefixWord ++ tailWord_1772500).sum := by decide
  have hdescent : baseEnd_1772500 < baseStart_1772500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772501 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1772501 : Nat := 118140960795 + 1772501 * 2 ^ 59
def prefixEnd_1772501 : Nat := 4983230072969 + 3 ^ 40 * 1772501 * 2
def baseEnd_1772501 : Nat := 910144973575074815385923

theorem tailTrace_1772501 : CollatzResearch.WordTrace tailWord_1772501 prefixEnd_1772501 910144973575074815385923 := by
  unfold tailWord_1772501
  simp only [CollatzResearch.WordTrace]
  refine ⟨64648422551539070915213357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43098948367692713943475571 64648422551539070915213357)
  ·
    refine ⟨24243158456827151593205009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64648422551539070915213357 24243158456827151593205009)
    ·
      refine ⟨18182368842620363694903757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24243158456827151593205009 18182368842620363694903757)
      ·
        refine ⟨6818388315982636385588909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18182368842620363694903757 6818388315982636385588909)
        ·
          refine ⟨2556895618493488644595841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6818388315982636385588909 2556895618493488644595841)
          ·
            refine ⟨1917671713870116483446881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2556895618493488644595841 1917671713870116483446881)
            ·
              refine ⟨1438253785402587362585161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917671713870116483446881 1438253785402587362585161)
              ·
                refine ⟨1078690339051940521938871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438253785402587362585161 1078690339051940521938871)
                ·
                  refine ⟨1618035508577910782908307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078690339051940521938871 1618035508577910782908307)
                  ·
                    refine ⟨2427053262866866174362461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618035508577910782908307 2427053262866866174362461)
                    ·
                      refine ⟨910144973575074815385923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427053262866866174362461 910144973575074815385923)
                      ·
                        rfl

theorem cell23_1772501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1772501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772501 prefixEnd_1772501 := by exact prefixLift 1772501
  have htrace : WordTrace (prefixWord ++ tailWord_1772501) baseStart_1772501 baseEnd_1772501 := by
    simpa [prefixWord, tailWord_1772501, baseEnd_1772501] using wordTrace_append hprefix tailTrace_1772501
  have hstable : (prefixWord ++ tailWord_1772501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772501).length < 2 ^ (prefixWord ++ tailWord_1772501).sum := by decide
  have hdescent : baseEnd_1772501 < baseStart_1772501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772523 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 3]
def baseStart_1772523 : Nat := 118140960795 + 1772523 * 2 ^ 59
def prefixEnd_1772523 : Nat := 4983230072969 + 3 ^ 40 * 1772523 * 2
def baseEnd_1772523 : Nat := 910156270149473729310821

theorem tailTrace_1772523 : CollatzResearch.WordTrace tailWord_1772523 prefixEnd_1772523 910156270149473729310821 := by
  unfold tailWord_1772523
  simp only [CollatzResearch.WordTrace]
  refine ⟨64649224957459368672514223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43099483304972912448342815 64649224957459368672514223)
  ·
    refine ⟨96973837436189053008771335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64649224957459368672514223 96973837436189053008771335)
    ·
      refine ⟨145460756154283579513157003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96973837436189053008771335 145460756154283579513157003)
      ·
        refine ⟨218191134231425369269735505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145460756154283579513157003 218191134231425369269735505)
        ·
          refine ⟨163643350673569026952301629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218191134231425369269735505 163643350673569026952301629)
          ·
            refine ⟨61366256502588385107113111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163643350673569026952301629 61366256502588385107113111)
            ·
              refine ⟨92049384753882577660669667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61366256502588385107113111 92049384753882577660669667)
              ·
                refine ⟨138074077130823866491004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92049384753882577660669667 138074077130823866491004501)
                ·
                  refine ⟨1618055591376842185441459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 138074077130823866491004501 1618055591376842185441459)
                  ·
                    refine ⟨2427083387065263278162189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618055591376842185441459 2427083387065263278162189)
                    ·
                      refine ⟨910156270149473729310821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427083387065263278162189 910156270149473729310821)
                      ·
                        rfl

theorem cell23_1772523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 3].length) (baseStart_1772523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772523 prefixEnd_1772523 := by exact prefixLift 1772523
  have htrace : WordTrace (prefixWord ++ tailWord_1772523) baseStart_1772523 baseEnd_1772523 := by
    simpa [prefixWord, tailWord_1772523, baseEnd_1772523] using wordTrace_append hprefix tailTrace_1772523
  have hstable : (prefixWord ++ tailWord_1772523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772523).length < 2 ^ (prefixWord ++ tailWord_1772523).sum := by decide
  have hdescent : baseEnd_1772523 < baseStart_1772523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772536 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1772536 : Nat := 118140960795 + 1772536 * 2 ^ 59
def prefixEnd_1772536 : Nat := 4983230072969 + 3 ^ 40 * 1772536 * 2
def baseEnd_1772536 : Nat := 910162945397982178448261

theorem tailTrace_1772536 : CollatzResearch.WordTrace tailWord_1772536 prefixEnd_1772536 910162945397982178448261 := by
  unfold tailWord_1772536
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324849553206135946368731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43099799404274847928491641 32324849553206135946368731)
  ·
    refine ⟨48487274329809203919553097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32324849553206135946368731 48487274329809203919553097)
    ·
      refine ⟨36365455747356902939664823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48487274329809203919553097 36365455747356902939664823)
      ·
        refine ⟨54548183621035354409497235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36365455747356902939664823 54548183621035354409497235)
        ·
          refine ⟨81822275431553031614245853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54548183621035354409497235 81822275431553031614245853)
          ·
            refine ⟨30683353286832386855342195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81822275431553031614245853 30683353286832386855342195)
            ·
              refine ⟨46025029930248580283013293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30683353286832386855342195 46025029930248580283013293)
              ·
                refine ⟨17259386223843217606129985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46025029930248580283013293 17259386223843217606129985)
                ·
                  refine ⟨12944539667882413204597489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17259386223843217606129985 12944539667882413204597489)
                  ·
                    refine ⟨9708404750911809903448117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12944539667882413204597489 9708404750911809903448117)
                    ·
                      refine ⟨910162945397982178448261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9708404750911809903448117 910162945397982178448261)
                      ·
                        rfl

theorem cell23_1772536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1772536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772536 prefixEnd_1772536 := by exact prefixLift 1772536
  have htrace : WordTrace (prefixWord ++ tailWord_1772536) baseStart_1772536 baseEnd_1772536 := by
    simpa [prefixWord, tailWord_1772536, baseEnd_1772536] using wordTrace_append hprefix tailTrace_1772536
  have hstable : (prefixWord ++ tailWord_1772536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772536).length < 2 ^ (prefixWord ++ tailWord_1772536).sum := by decide
  have hdescent : baseEnd_1772536 < baseStart_1772536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772613 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1772613 : Nat := 118140960795 + 1772613 * 2 ^ 59
def prefixEnd_1772613 : Nat := 4983230072969 + 3 ^ 40 * 1772613 * 2
def baseEnd_1772613 : Nat := 910202483408378377185407

theorem tailTrace_1772613 : CollatzResearch.WordTrace tailWord_1772613 prefixEnd_1772613 910202483408378377185407 := by
  unfold tailWord_1772613
  simp only [CollatzResearch.WordTrace]
  refine ⟨64652507527133314043290493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43101671684755542695526995 64652507527133314043290493)
  ·
    refine ⟨24244690322674992766233935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64652507527133314043290493 24244690322674992766233935)
    ·
      refine ⟨36367035484012489149350903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24244690322674992766233935 36367035484012489149350903)
      ·
        refine ⟨54550553226018733724026355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36367035484012489149350903 54550553226018733724026355)
        ·
          refine ⟨81825829839028100586039533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54550553226018733724026355 81825829839028100586039533)
          ·
            refine ⟨30684686189635537719764825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81825829839028100586039533 30684686189635537719764825)
            ·
              refine ⟨23013514642226653289823619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30684686189635537719764825 23013514642226653289823619)
              ·
                refine ⟨34520271963339979934735429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23013514642226653289823619 34520271963339979934735429)
                ·
                  refine ⟨6472550993126246237762893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34520271963339979934735429 6472550993126246237762893)
                  ·
                    refine ⟨2427206622422342339161085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6472550993126246237762893 2427206622422342339161085)
                    ·
                      refine ⟨910202483408378377185407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427206622422342339161085 910202483408378377185407)
                      ·
                        rfl

theorem cell23_1772613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1772613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772613 prefixEnd_1772613 := by exact prefixLift 1772613
  have htrace : WordTrace (prefixWord ++ tailWord_1772613) baseStart_1772613 baseEnd_1772613 := by
    simpa [prefixWord, tailWord_1772613, baseEnd_1772613] using wordTrace_append hprefix tailTrace_1772613
  have hstable : (prefixWord ++ tailWord_1772613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772613).length < 2 ^ (prefixWord ++ tailWord_1772613).sum := by decide
  have hdescent : baseEnd_1772613 < baseStart_1772613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772650 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1772650 : Nat := 118140960795 + 1772650 * 2 ^ 59
def prefixEnd_1772650 : Nat := 4983230072969 + 3 ^ 40 * 1772650 * 2
def baseEnd_1772650 : Nat := 303407160730864910807579

theorem tailTrace_1772650 : CollatzResearch.WordTrace tailWord_1772650 prefixEnd_1772650 303407160730864910807579 := by
  unfold tailWord_1772650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163464256999817340596851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43102571351999512908258269 16163464256999817340596851)
  ·
    refine ⟨24245196385499726010895277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16163464256999817340596851 24245196385499726010895277)
    ·
      refine ⟨9091948644562397254085729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24245196385499726010895277 9091948644562397254085729)
      ·
        refine ⟨6818961483421797940564297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091948644562397254085729 6818961483421797940564297)
        ·
          refine ⟨5114221112566348455423223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818961483421797940564297 5114221112566348455423223)
          ·
            refine ⟨7671331668849522683134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114221112566348455423223 7671331668849522683134835)
            ·
              refine ⟨11506997503274284024702253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671331668849522683134835 11506997503274284024702253)
              ·
                refine ⟨4315124063727856509263345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11506997503274284024702253 4315124063727856509263345)
                ·
                  refine ⟨3236343047795892381947509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315124063727856509263345 3236343047795892381947509)
                  ·
                    refine ⟨303407160730864910807579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3236343047795892381947509 303407160730864910807579)
                    ·
                      rfl

theorem cell23_1772650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1772650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772650 prefixEnd_1772650 := by exact prefixLift 1772650
  have htrace : WordTrace (prefixWord ++ tailWord_1772650) baseStart_1772650 baseEnd_1772650 := by
    simpa [prefixWord, tailWord_1772650, baseEnd_1772650] using wordTrace_append hprefix tailTrace_1772650
  have hstable : (prefixWord ++ tailWord_1772650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772650).length < 2 ^ (prefixWord ++ tailWord_1772650).sum := by decide
  have hdescent : baseEnd_1772650 < baseStart_1772650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772757 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1772757 : Nat := 118140960795 + 1772757 * 2 ^ 59
def prefixEnd_1772757 : Nat := 4983230072969 + 3 ^ 40 * 1772757 * 2
def baseEnd_1772757 : Nat := 303425474874208604594915

theorem tailTrace_1772757 : CollatzResearch.WordTrace tailWord_1772757 prefixEnd_1772757 303425474874208604594915 := by
  unfold tailWord_1772757
  simp only [CollatzResearch.WordTrace]
  refine ⟨64657759638611626636532525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43105173092407751091021683 64657759638611626636532525)
  ·
    refine ⟨24246659864479359988699697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64657759638611626636532525 24246659864479359988699697)
    ·
      refine ⟨18184994898359519991524773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24246659864479359988699697 18184994898359519991524773)
      ·
        refine ⟨3409686543442409998410895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18184994898359519991524773 3409686543442409998410895)
        ·
          refine ⟨5114529815163614997616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409686543442409998410895 5114529815163614997616343)
          ·
            refine ⟨7671794722745422496424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114529815163614997616343 7671794722745422496424515)
            ·
              refine ⟨11507692084118133744636773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671794722745422496424515 11507692084118133744636773)
              ·
                refine ⟨2157692265772150077119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11507692084118133744636773 2157692265772150077119395)
                ·
                  refine ⟨3236538398658225115679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157692265772150077119395 3236538398658225115679093)
                  ·
                    refine ⟨303425474874208604594915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3236538398658225115679093 303425474874208604594915)
                    ·
                      rfl

theorem cell23_1772757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1772757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772757 prefixEnd_1772757 := by exact prefixLift 1772757
  have htrace : WordTrace (prefixWord ++ tailWord_1772757) baseStart_1772757 baseEnd_1772757 := by
    simpa [prefixWord, tailWord_1772757, baseEnd_1772757] using wordTrace_append hprefix tailTrace_1772757
  have hstable : (prefixWord ++ tailWord_1772757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772757).length < 2 ^ (prefixWord ++ tailWord_1772757).sum := by decide
  have hdescent : baseEnd_1772757 < baseStart_1772757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772780 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1772780 : Nat := 118140960795 + 1772780 * 2 ^ 59
def prefixEnd_1772780 : Nat := 4983230072969 + 3 ^ 40 * 1772780 * 2
def baseEnd_1772780 : Nat := 910288234677679223797139

theorem tailTrace_1772780 : CollatzResearch.WordTrace tailWord_1772780 prefixEnd_1772780 910288234677679223797139 := by
  unfold tailWord_1772780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32329299258764150782309897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43105732345018867709746529 32329299258764150782309897)
  ·
    refine ⟨24246974444073113086732423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32329299258764150782309897 24246974444073113086732423)
    ·
      refine ⟨36370461666109669630098635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246974444073113086732423 36370461666109669630098635)
      ·
        refine ⟨54555692499164504445147953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36370461666109669630098635 54555692499164504445147953)
        ·
          refine ⟨40916769374373378333860965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54555692499164504445147953 40916769374373378333860965)
          ·
            refine ⟨7671894257695008437598931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40916769374373378333860965 7671894257695008437598931)
            ·
              refine ⟨11507841386542512656398397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671894257695008437598931 11507841386542512656398397)
              ·
                refine ⟨4315440519953442246149399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11507841386542512656398397 4315440519953442246149399)
                ·
                  refine ⟨6473160779930163369224099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315440519953442246149399 6473160779930163369224099)
                  ·
                    refine ⟨9709741169895245053836149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6473160779930163369224099 9709741169895245053836149)
                    ·
                      refine ⟨910288234677679223797139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9709741169895245053836149 910288234677679223797139)
                      ·
                        rfl

theorem cell23_1772780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1772780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772780 prefixEnd_1772780 := by exact prefixLift 1772780
  have htrace : WordTrace (prefixWord ++ tailWord_1772780) baseStart_1772780 baseEnd_1772780 := by
    simpa [prefixWord, tailWord_1772780, baseEnd_1772780] using wordTrace_append hprefix tailTrace_1772780
  have hstable : (prefixWord ++ tailWord_1772780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772780).length < 2 ^ (prefixWord ++ tailWord_1772780).sum := by decide
  have hdescent : baseEnd_1772780 < baseStart_1772780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772804 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1772804 : Nat := 118140960795 + 1772804 * 2 ^ 59
def prefixEnd_1772804 : Nat := 4983230072969 + 3 ^ 40 * 1772804 * 2
def baseEnd_1772804 : Nat := 303433519404462376632343

theorem tailTrace_1772804 : CollatzResearch.WordTrace tailWord_1772804 prefixEnd_1772804 303433519404462376632343 := by
  unfold tailWord_1772804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32329736934720676831746733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43106315912960902442328977 32329736934720676831746733)
  ·
    refine ⟨12123651350520253811905025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32329736934720676831746733 12123651350520253811905025)
    ·
      refine ⟨9092738512890190358928769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12123651350520253811905025 9092738512890190358928769)
      ·
        refine ⟨6819553884667642769196577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9092738512890190358928769 6819553884667642769196577)
        ·
          refine ⟨5114665413500732076897433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6819553884667642769196577 5114665413500732076897433)
          ·
            refine ⟨3835999060125549057673075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114665413500732076897433 3835999060125549057673075)
            ·
              refine ⟨5753998590188323586509613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835999060125549057673075 5753998590188323586509613)
              ·
                refine ⟨2157749471320621344941105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5753998590188323586509613 2157749471320621344941105)
                ·
                  refine ⟨1618312103490466008705829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2157749471320621344941105 1618312103490466008705829)
                  ·
                    refine ⟨303433519404462376632343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618312103490466008705829 303433519404462376632343)
                    ·
                      rfl

theorem cell23_1772804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1772804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772804 prefixEnd_1772804 := by exact prefixLift 1772804
  have htrace : WordTrace (prefixWord ++ tailWord_1772804) baseStart_1772804 baseEnd_1772804 := by
    simpa [prefixWord, tailWord_1772804, baseEnd_1772804] using wordTrace_append hprefix tailTrace_1772804
  have hstable : (prefixWord ++ tailWord_1772804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772804).length < 2 ^ (prefixWord ++ tailWord_1772804).sum := by decide
  have hdescent : baseEnd_1772804 < baseStart_1772804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772814 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1772814 : Nat := 118140960795 + 1772814 * 2 ^ 59
def prefixEnd_1772814 : Nat := 4983230072969 + 3 ^ 40 * 1772814 * 2
def baseEnd_1772814 : Nat := 910305693019932090771983

theorem tailTrace_1772814 : CollatzResearch.WordTrace tailWord_1772814 prefixEnd_1772814 910305693019932090771983 := by
  unfold tailWord_1772814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082479824925640671419687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43106559066270083580904997 8082479824925640671419687)
  ·
    refine ⟨12123719737388461007129531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8082479824925640671419687 12123719737388461007129531)
    ·
      refine ⟨18185579606082691510694297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12123719737388461007129531 18185579606082691510694297)
      ·
        refine ⟨13639184704562018633020723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18185579606082691510694297 13639184704562018633020723)
        ·
          refine ⟨20458777056843027949531085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639184704562018633020723 20458777056843027949531085)
          ·
            refine ⟨7672041396316135481074157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20458777056843027949531085 7672041396316135481074157)
            ·
              refine ⟨2877015523618550805402809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7672041396316135481074157 2877015523618550805402809)
              ·
                refine ⟨2157761642713913104052107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877015523618550805402809 2157761642713913104052107)
                ·
                  refine ⟨3236642464070869656078161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157761642713913104052107 3236642464070869656078161)
                  ·
                    refine ⟨2427481848053152242058621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236642464070869656078161 2427481848053152242058621)
                    ·
                      refine ⟨910305693019932090771983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427481848053152242058621 910305693019932090771983)
                      ·
                        rfl

theorem cell23_1772814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1772814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772814 prefixEnd_1772814 := by exact prefixLift 1772814
  have htrace : WordTrace (prefixWord ++ tailWord_1772814) baseStart_1772814 baseEnd_1772814 := by
    simpa [prefixWord, tailWord_1772814, baseEnd_1772814] using wordTrace_append hprefix tailTrace_1772814
  have hstable : (prefixWord ++ tailWord_1772814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772814).length < 2 ^ (prefixWord ++ tailWord_1772814).sum := by decide
  have hdescent : baseEnd_1772814 < baseStart_1772814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772831 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 1, 2, 3]
def baseStart_1772831 : Nat := 118140960795 + 1772831 * 2 ^ 59
def prefixEnd_1772831 : Nat := 4983230072969 + 3 ^ 40 * 1772831 * 2
def baseEnd_1772831 : Nat := 910314422191058524259405

theorem tailTrace_1772831 : CollatzResearch.WordTrace tailWord_1772831 prefixEnd_1772831 910314422191058524259405 := by
  unfold tailWord_1772831
  simp only [CollatzResearch.WordTrace]
  refine ⟨64660458640343537274726347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43106972426895691516484231 64660458640343537274726347)
  ·
    refine ⟨96990687960515305912089521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64660458640343537274726347 96990687960515305912089521)
    ·
      refine ⟨72743015970386479434067141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96990687960515305912089521 72743015970386479434067141)
      ·
        refine ⟨13639315494447464893887589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72743015970386479434067141 13639315494447464893887589)
        ·
          refine ⟨2557371655208899667603923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13639315494447464893887589 2557371655208899667603923)
          ·
            refine ⟨3836057482813349501405885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557371655208899667603923 3836057482813349501405885)
            ·
              refine ⟨1438521556055006063027207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3836057482813349501405885 1438521556055006063027207)
              ·
                refine ⟨2157782334082509094540811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438521556055006063027207 2157782334082509094540811)
                ·
                  refine ⟨3236673501123763641811217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157782334082509094540811 3236673501123763641811217)
                  ·
                    refine ⟨2427505125842822731358413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3236673501123763641811217 2427505125842822731358413)
                    ·
                      refine ⟨910314422191058524259405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427505125842822731358413 910314422191058524259405)
                      ·
                        rfl

theorem cell23_1772831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_1772831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772831 prefixEnd_1772831 := by exact prefixLift 1772831
  have htrace : WordTrace (prefixWord ++ tailWord_1772831) baseStart_1772831 baseEnd_1772831 := by
    simpa [prefixWord, tailWord_1772831, baseEnd_1772831] using wordTrace_append hprefix tailTrace_1772831
  have hstable : (prefixWord ++ tailWord_1772831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772831).length < 2 ^ (prefixWord ++ tailWord_1772831).sum := by decide
  have hdescent : baseEnd_1772831 < baseStart_1772831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772845 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1772845 : Nat := 118140960795 + 1772845 * 2 ^ 59
def prefixEnd_1772845 : Nat := 4983230072969 + 3 ^ 40 * 1772845 * 2
def baseEnd_1772845 : Nat := 910321610920221469484341

theorem tailTrace_1772845 : CollatzResearch.WordTrace tailWord_1772845 prefixEnd_1772845 910321610920221469484341 := by
  unfold tailWord_1772845
  simp only [CollatzResearch.WordTrace]
  refine ⟨64660969262292817665735989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43107312841528545110490659 64660969262292817665735989)
  ·
    refine ⟨6061965868339951656162749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64660969262292817665735989 6061965868339951656162749)
    ·
      refine ⟨2273237200627481871061031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6061965868339951656162749 2273237200627481871061031)
      ·
        refine ⟨3409855800941222806591547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273237200627481871061031 3409855800941222806591547)
        ·
          refine ⟨5114783701411834209887321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409855800941222806591547 5114783701411834209887321)
          ·
            refine ⟨3836087776058875657415491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114783701411834209887321 3836087776058875657415491)
            ·
              refine ⟨5754131664088313486123237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836087776058875657415491 5754131664088313486123237)
              ·
                refine ⟨1078899687016558778648107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5754131664088313486123237 1078899687016558778648107)
                ·
                  refine ⟨1618349530524838167972161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078899687016558778648107 1618349530524838167972161)
                  ·
                    refine ⟨1213762147893628625979121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618349530524838167972161 1213762147893628625979121)
                    ·
                      refine ⟨910321610920221469484341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213762147893628625979121 910321610920221469484341)
                      ·
                        rfl

theorem cell23_1772845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1772845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772845 prefixEnd_1772845 := by exact prefixLift 1772845
  have htrace : WordTrace (prefixWord ++ tailWord_1772845) baseStart_1772845 baseEnd_1772845 := by
    simpa [prefixWord, tailWord_1772845, baseEnd_1772845] using wordTrace_append hprefix tailTrace_1772845
  have hstable : (prefixWord ++ tailWord_1772845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772845).length < 2 ^ (prefixWord ++ tailWord_1772845).sum := by decide
  have hdescent : baseEnd_1772845 < baseStart_1772845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772860 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1772860 : Nat := 118140960795 + 1772860 * 2 ^ 59
def prefixEnd_1772860 : Nat := 4983230072969 + 3 ^ 40 * 1772860 * 2
def baseEnd_1772860 : Nat := 303443104376679636932257

theorem tailTrace_1772860 : CollatzResearch.WordTrace tailWord_1772860 prefixEnd_1772860 303443104376679636932257 := by
  unfold tailWord_1772860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32330758178619237613766017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43107677571492316818354689 32330758178619237613766017)
  ·
    refine ⟨24248068633964428210324513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32330758178619237613766017 24248068633964428210324513)
    ·
      refine ⟨18186051475473321157743385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24248068633964428210324513 18186051475473321157743385)
      ·
        refine ⟨13639538606604990868307539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18186051475473321157743385 13639538606604990868307539)
        ·
          refine ⟨20459307909907486302461309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639538606604990868307539 20459307909907486302461309)
          ·
            refine ⟨7672240466215307363422991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20459307909907486302461309 7672240466215307363422991)
            ·
              refine ⟨11508360699322961045134487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7672240466215307363422991 11508360699322961045134487)
              ·
                refine ⟨17262541048984441567701731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11508360699322961045134487 17262541048984441567701731)
                ·
                  refine ⟨25893811573476662351552597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17262541048984441567701731 25893811573476662351552597)
                  ·
                    refine ⟨303443104376679636932257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25893811573476662351552597 303443104376679636932257)
                    ·
                      rfl

theorem cell23_1772860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1772860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772860 prefixEnd_1772860 := by exact prefixLift 1772860
  have htrace : WordTrace (prefixWord ++ tailWord_1772860) baseStart_1772860 baseEnd_1772860 := by
    simpa [prefixWord, tailWord_1772860, baseEnd_1772860] using wordTrace_append hprefix tailTrace_1772860
  have hstable : (prefixWord ++ tailWord_1772860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772860).length < 2 ^ (prefixWord ++ tailWord_1772860).sum := by decide
  have hdescent : baseEnd_1772860 < baseStart_1772860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772861 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1772861 : Nat := 118140960795 + 1772861 * 2 ^ 59
def prefixEnd_1772861 : Nat := 4983230072969 + 3 ^ 40 * 1772861 * 2
def baseEnd_1772861 : Nat := 910329826610693406884267

theorem tailTrace_1772861 : CollatzResearch.WordTrace tailWord_1772861 prefixEnd_1772861 910329826610693406884267 := by
  unfold tailWord_1772861
  simp only [CollatzResearch.WordTrace]
  refine ⟨64661552830234852398318437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43107701886823234932212291 64661552830234852398318437)
  ·
    refine ⟨12124041155669034824684707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64661552830234852398318437 12124041155669034824684707)
    ·
      refine ⟨18186061733503552237027061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12124041155669034824684707 18186061733503552237027061)
      ·
        refine ⟨1704943287515958022221287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18186061733503552237027061 1704943287515958022221287)
        ·
          refine ⟨2557414931273937033331931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704943287515958022221287 2557414931273937033331931)
          ·
            refine ⟨3836122396910905549997897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557414931273937033331931 3836122396910905549997897)
            ·
              refine ⟨2877091797683179162498423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836122396910905549997897 2877091797683179162498423)
              ·
                refine ⟨4315637696524768743747635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877091797683179162498423 4315637696524768743747635)
                ·
                  refine ⟨6473456544787153115621453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315637696524768743747635 6473456544787153115621453)
                  ·
                    refine ⟨2427546204295182418358045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6473456544787153115621453 2427546204295182418358045)
                    ·
                      refine ⟨910329826610693406884267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427546204295182418358045 910329826610693406884267)
                      ·
                        rfl

theorem cell23_1772861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1772861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772861 prefixEnd_1772861 := by exact prefixLift 1772861
  have htrace : WordTrace (prefixWord ++ tailWord_1772861) baseStart_1772861 baseEnd_1772861 := by
    simpa [prefixWord, tailWord_1772861, baseEnd_1772861] using wordTrace_append hprefix tailTrace_1772861
  have hstable : (prefixWord ++ tailWord_1772861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772861).length < 2 ^ (prefixWord ++ tailWord_1772861).sum := by decide
  have hdescent : baseEnd_1772861 < baseStart_1772861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772880 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1772880 : Nat := 118140960795 + 1772880 * 2 ^ 59
def prefixEnd_1772880 : Nat := 4983230072969 + 3 ^ 40 * 1772880 * 2
def baseEnd_1772880 : Nat := 910339582743128832546679

theorem tailTrace_1772880 : CollatzResearch.WordTrace tailWord_1772880 prefixEnd_1772880 910339582743128832546679 := by
  unfold tailWord_1772880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331122908583009321630047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43108163878110679095506729 32331122908583009321630047)
  ·
    refine ⟨48496684362874513982445071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32331122908583009321630047 48496684362874513982445071)
    ·
      refine ⟨72745026544311770973667607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48496684362874513982445071 72745026544311770973667607)
      ·
        refine ⟨109117539816467656460501411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72745026544311770973667607 109117539816467656460501411)
        ·
          refine ⟨163676309724701484690752117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109117539816467656460501411 163676309724701484690752117)
          ·
            refine ⟨15344654036690764189758011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163676309724701484690752117 15344654036690764189758011)
            ·
              refine ⟨23016981055036146284637017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15344654036690764189758011 23016981055036146284637017)
              ·
                refine ⟨17262735791277109713477763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23016981055036146284637017 17262735791277109713477763)
                ·
                  refine ⟨25894103686915664570216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17262735791277109713477763 25894103686915664570216645)
                  ·
                    refine ⟨4855144441296687106915621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25894103686915664570216645 4855144441296687106915621)
                    ·
                      refine ⟨910339582743128832546679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4855144441296687106915621 910339582743128832546679)
                      ·
                        rfl

theorem cell23_1772880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1772880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772880 prefixEnd_1772880 := by exact prefixLift 1772880
  have htrace : WordTrace (prefixWord ++ tailWord_1772880) baseStart_1772880 baseEnd_1772880 := by
    simpa [prefixWord, tailWord_1772880, baseEnd_1772880] using wordTrace_append hprefix tailTrace_1772880
  have hstable : (prefixWord ++ tailWord_1772880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772880).length < 2 ^ (prefixWord ++ tailWord_1772880).sum := by decide
  have hdescent : baseEnd_1772880 < baseStart_1772880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772884 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_1772884 : Nat := 118140960795 + 1772884 * 2 ^ 59
def prefixEnd_1772884 : Nat := 4983230072969 + 3 ^ 40 * 1772884 * 2
def baseEnd_1772884 : Nat := 910341636665746816896661

theorem tailTrace_1772884 : CollatzResearch.WordTrace tailWord_1772884 prefixEnd_1772884 910341636665746816896661 := by
  unfold tailWord_1772884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331195854575763663202853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43108261139434351550937137 32331195854575763663202853)
  ·
    refine ⟨6062099222732955686850535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32331195854575763663202853 6062099222732955686850535)
    ·
      refine ⟨9093148834099433530275803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062099222732955686850535 9093148834099433530275803)
      ·
        refine ⟨13639723251149150295413705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9093148834099433530275803 13639723251149150295413705)
        ·
          refine ⟨10229792438361862721560279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13639723251149150295413705 10229792438361862721560279)
          ·
            refine ⟨15344688657542794082340419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229792438361862721560279 15344688657542794082340419)
            ·
              refine ⟨23017032986314191123510629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15344688657542794082340419 23017032986314191123510629)
              ·
                refine ⟨4315693684933910835658243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23017032986314191123510629 4315693684933910835658243)
                ·
                  refine ⟨6473540527400866253487365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315693684933910835658243 6473540527400866253487365)
                  ·
                    refine ⟨1213788848887662422528881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473540527400866253487365 1213788848887662422528881)
                    ·
                      refine ⟨910341636665746816896661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213788848887662422528881 910341636665746816896661)
                      ·
                        rfl

theorem cell23_1772884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_1772884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772884 prefixEnd_1772884 := by exact prefixLift 1772884
  have htrace : WordTrace (prefixWord ++ tailWord_1772884) baseStart_1772884 baseEnd_1772884 := by
    simpa [prefixWord, tailWord_1772884, baseEnd_1772884] using wordTrace_append hprefix tailTrace_1772884
  have hstable : (prefixWord ++ tailWord_1772884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772884).length < 2 ^ (prefixWord ++ tailWord_1772884).sum := by decide
  have hdescent : baseEnd_1772884 < baseStart_1772884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1772958 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1772958 : Nat := 118140960795 + 1772958 * 2 ^ 59
def prefixEnd_1772958 : Nat := 4983230072969 + 3 ^ 40 * 1772958 * 2
def baseEnd_1772958 : Nat := 101153292692686614152369

theorem tailTrace_1772958 : CollatzResearch.WordTrace tailWord_1772958 prefixEnd_1772958 101153292692686614152369 := by
  unfold tailWord_1772958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8083136338860429745574941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43110060473922291976399685 8083136338860429745574941)
  ·
    refine ⟨3031176127072661154590603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8083136338860429745574941 3031176127072661154590603)
    ·
      refine ⟨4546764190608991731885905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031176127072661154590603 4546764190608991731885905)
      ·
        refine ⟨3410073142956743798914429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546764190608991731885905 3410073142956743798914429)
        ·
          refine ⟨1278777428608778924592911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3410073142956743798914429 1278777428608778924592911)
          ·
            refine ⟨1918166142913168386889367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278777428608778924592911 1918166142913168386889367)
            ·
              refine ⟨2877249214369752580334051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918166142913168386889367 2877249214369752580334051)
              ·
                refine ⟨4315873821554628870501077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877249214369752580334051 4315873821554628870501077)
                ·
                  refine ⟨101153292692686614152369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4315873821554628870501077 101153292692686614152369)
                  ·
                    rfl

theorem cell23_1772958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1772958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1772958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1772958 prefixEnd_1772958 := by exact prefixLift 1772958
  have htrace : WordTrace (prefixWord ++ tailWord_1772958) baseStart_1772958 baseEnd_1772958 := by
    simpa [prefixWord, tailWord_1772958, baseEnd_1772958] using wordTrace_append hprefix tailTrace_1772958
  have hstable : (prefixWord ++ tailWord_1772958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1772958).length < 2 ^ (prefixWord ++ tailWord_1772958).sum := by decide
  have hdescent : baseEnd_1772958 < baseStart_1772958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1772958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773018 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_1773018 : Nat := 118140960795 + 1773018 * 2 ^ 59
def prefixEnd_1773018 : Nat := 4983230072969 + 3 ^ 40 * 1773018 * 2
def baseEnd_1773018 : Nat := 303470147691149764207015

theorem tailTrace_1773018 : CollatzResearch.WordTrace tailWord_1773018 prefixEnd_1773018 303470147691149764207015 := by
  unfold tailWord_1773018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16166819772666517052945927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43111519393777378807855805 16166819772666517052945927)
  ·
    refine ⟨24250229658999775579418891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16166819772666517052945927 24250229658999775579418891)
    ·
      refine ⟨36375344488499663369128337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24250229658999775579418891 36375344488499663369128337)
      ·
        refine ⟨27281508366374747526846253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36375344488499663369128337 27281508366374747526846253)
        ·
          refine ⟨10230565637390530322567345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27281508366374747526846253 10230565637390530322567345)
          ·
            refine ⟨7672924228042897741925509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10230565637390530322567345 7672924228042897741925509)
            ·
              refine ⟨1438673292758043326611033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7672924228042897741925509 1438673292758043326611033)
              ·
                refine ⟨1079004969568532494958275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438673292758043326611033 1079004969568532494958275)
                ·
                  refine ⟨1618507454352798742437413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079004969568532494958275 1618507454352798742437413)
                  ·
                    refine ⟨303470147691149764207015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618507454352798742437413 303470147691149764207015)
                    ·
                      rfl

theorem cell23_1773018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_1773018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773018 prefixEnd_1773018 := by exact prefixLift 1773018
  have htrace : WordTrace (prefixWord ++ tailWord_1773018) baseStart_1773018 baseEnd_1773018 := by
    simpa [prefixWord, tailWord_1773018, baseEnd_1773018] using wordTrace_append hprefix tailTrace_1773018
  have hstable : (prefixWord ++ tailWord_1773018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773018).length < 2 ^ (prefixWord ++ tailWord_1773018).sum := by decide
  have hdescent : baseEnd_1773018 < baseStart_1773018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773041 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_1773041 : Nat := 118140960795 + 1773041 * 2 ^ 59
def prefixEnd_1773041 : Nat := 4983230072969 + 3 ^ 40 * 1773041 * 2
def baseEnd_1773041 : Nat := 910422253128502702633439

theorem tailTrace_1773041 : CollatzResearch.WordTrace tailWord_1773041 prefixEnd_1773041 910422253128502702633439 := by
  unfold tailWord_1773041
  simp only [CollatzResearch.WordTrace]
  refine ⟨64668117969582743139870977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43112078646388495426580651 64668117969582743139870977)
  ·
    refine ⟨48501088477187057354903233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64668117969582743139870977 48501088477187057354903233)
    ·
      refine ⟨36375816357890293016177425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48501088477187057354903233 36375816357890293016177425)
      ·
        refine ⟨27281862268417719762133069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36375816357890293016177425 27281862268417719762133069)
        ·
          refine ⟨10230698350656644910799901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27281862268417719762133069 10230698350656644910799901)
          ·
            refine ⟨3836511881496241841549963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10230698350656644910799901 3836511881496241841549963)
            ·
              refine ⟨5754767822244362762324945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836511881496241841549963 5754767822244362762324945)
              ·
                refine ⟨4316075866683272071743709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5754767822244362762324945 4316075866683272071743709)
                ·
                  refine ⟨1618528450006227026903891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4316075866683272071743709 1618528450006227026903891)
                  ·
                    refine ⟨2427792675009340540355837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618528450006227026903891 2427792675009340540355837)
                    ·
                      refine ⟨910422253128502702633439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427792675009340540355837 910422253128502702633439)
                      ·
                        rfl

theorem cell23_1773041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_1773041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773041 prefixEnd_1773041 := by exact prefixLift 1773041
  have htrace : WordTrace (prefixWord ++ tailWord_1773041) baseStart_1773041 baseEnd_1773041 := by
    simpa [prefixWord, tailWord_1773041, baseEnd_1773041] using wordTrace_append hprefix tailTrace_1773041
  have hstable : (prefixWord ++ tailWord_1773041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773041).length < 2 ^ (prefixWord ++ tailWord_1773041).sum := by decide
  have hdescent : baseEnd_1773041 < baseStart_1773041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773084 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1773084 : Nat := 118140960795 + 1773084 * 2 ^ 59
def prefixEnd_1773084 : Nat := 4983230072969 + 3 ^ 40 * 1773084 * 2
def baseEnd_1773084 : Nat := 910444332796646034395741

theorem tailTrace_1773084 : CollatzResearch.WordTrace tailWord_1773084 prefixEnd_1773084 910444332796646034395741 := by
  unfold tailWord_1773084
  simp only [CollatzResearch.WordTrace]
  refine ⟨32334843154213480741843153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43113124205617974322457537 32334843154213480741843153)
  ·
    refine ⟨24251132365660110556382365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32334843154213480741843153 24251132365660110556382365)
    ·
      refine ⟨9094174637122541458643387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24251132365660110556382365 9094174637122541458643387)
      ·
        refine ⟨13641261955683812187965081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9094174637122541458643387 13641261955683812187965081)
        ·
          refine ⟨10230946466762859140973811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13641261955683812187965081 10230946466762859140973811)
          ·
            refine ⟨15346419700144288711460717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10230946466762859140973811 15346419700144288711460717)
            ·
              refine ⟨5754907387554108266797769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15346419700144288711460717 5754907387554108266797769)
              ·
                refine ⟨4316180540665581200098327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5754907387554108266797769 4316180540665581200098327)
                ·
                  refine ⟨6474270810998371800147491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316180540665581200098327 6474270810998371800147491)
                  ·
                    refine ⟨9711406216497557700221237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6474270810998371800147491 9711406216497557700221237)
                    ·
                      refine ⟨910444332796646034395741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9711406216497557700221237 910444332796646034395741)
                      ·
                        rfl

theorem cell23_1773084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1773084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773084 prefixEnd_1773084 := by exact prefixLift 1773084
  have htrace : WordTrace (prefixWord ++ tailWord_1773084) baseStart_1773084 baseEnd_1773084 := by
    simpa [prefixWord, tailWord_1773084, baseEnd_1773084] using wordTrace_append hprefix tailTrace_1773084
  have hstable : (prefixWord ++ tailWord_1773084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773084).length < 2 ^ (prefixWord ++ tailWord_1773084).sum := by decide
  have hdescent : baseEnd_1773084 < baseStart_1773084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773091 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 6]
def baseStart_1773091 : Nat := 118140960795 + 1773091 * 2 ^ 59
def prefixEnd_1773091 : Nat := 4983230072969 + 3 ^ 40 * 1773091 * 2
def baseEnd_1773091 : Nat := 303482642387075835669403

theorem tailTrace_1773091 : CollatzResearch.WordTrace tailWord_1773091 prefixEnd_1773091 303482642387075835669403 := by
  unfold tailWord_1773091
  simp only [CollatzResearch.WordTrace]
  refine ⟨64669941619401601679191127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43113294412934401119460751 64669941619401601679191127)
  ·
    refine ⟨97004912429102402518786691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64669941619401601679191127 97004912429102402518786691)
    ·
      refine ⟨145507368643653603778180037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97004912429102402518786691 145507368643653603778180037)
      ·
        refine ⟨27282631620685050708408757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145507368643653603778180037 27282631620685050708408757)
        ·
          refine ⟨2557746714439223503913321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27282631620685050708408757 2557746714439223503913321)
          ·
            refine ⟨1918310035829417627934991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2557746714439223503913321 1918310035829417627934991)
            ·
              refine ⟨2877465053744126441902487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918310035829417627934991 2877465053744126441902487)
              ·
                refine ⟨4316197580616189662853731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877465053744126441902487 4316197580616189662853731)
                ·
                  refine ⟨6474296370924284494280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316197580616189662853731 6474296370924284494280597)
                  ·
                    refine ⟨303482642387075835669403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6474296370924284494280597 303482642387075835669403)
                    ·
                      rfl

theorem cell23_1773091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 6].length) (baseStart_1773091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773091 prefixEnd_1773091 := by exact prefixLift 1773091
  have htrace : WordTrace (prefixWord ++ tailWord_1773091) baseStart_1773091 baseEnd_1773091 := by
    simpa [prefixWord, tailWord_1773091, baseEnd_1773091] using wordTrace_append hprefix tailTrace_1773091
  have hstable : (prefixWord ++ tailWord_1773091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773091).length < 2 ^ (prefixWord ++ tailWord_1773091).sum := by decide
  have hdescent : baseEnd_1773091 < baseStart_1773091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773098 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1773098 : Nat := 118140960795 + 1773098 * 2 ^ 59
def prefixEnd_1773098 : Nat := 4983230072969 + 3 ^ 40 * 1773098 * 2
def baseEnd_1773098 : Nat := 910451521525808979620677

theorem tailTrace_1773098 : CollatzResearch.WordTrace tailWord_1773098 prefixEnd_1773098 910451521525808979620677 := by
  unfold tailWord_1773098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167549232594060468673987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43113464620250827916463965 16167549232594060468673987)
  ·
    refine ⟨24251323848891090703010981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16167549232594060468673987 24251323848891090703010981)
    ·
      refine ⟨4547123221667079506814559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24251323848891090703010981 4547123221667079506814559)
      ·
        refine ⟨6820684832500619260221839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547123221667079506814559 6820684832500619260221839)
        ·
          refine ⟨10231027248750928890332759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6820684832500619260221839 10231027248750928890332759)
          ·
            refine ⟨15346540873126393335499139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10231027248750928890332759 15346540873126393335499139)
            ·
              refine ⟨23019811309689590003248709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15346540873126393335499139 23019811309689590003248709)
              ·
                refine ⟨4316214620566798125609133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23019811309689590003248709 4316214620566798125609133)
                ·
                  refine ⟨1618580482712549297103425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4316214620566798125609133 1618580482712549297103425)
                  ·
                    refine ⟨1213935362034411972827569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618580482712549297103425 1213935362034411972827569)
                    ·
                      refine ⟨910451521525808979620677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213935362034411972827569 910451521525808979620677)
                      ·
                        rfl

theorem cell23_1773098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1773098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773098 prefixEnd_1773098 := by exact prefixLift 1773098
  have htrace : WordTrace (prefixWord ++ tailWord_1773098) baseStart_1773098 baseEnd_1773098 := by
    simpa [prefixWord, tailWord_1773098, baseEnd_1773098] using wordTrace_append hprefix tailTrace_1773098
  have hstable : (prefixWord ++ tailWord_1773098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773098).length < 2 ^ (prefixWord ++ tailWord_1773098).sum := by decide
  have hdescent : baseEnd_1773098 < baseStart_1773098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773114 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_1773114 : Nat := 118140960795 + 1773114 * 2 ^ 59
def prefixEnd_1773114 : Nat := 4983230072969 + 3 ^ 40 * 1773114 * 2
def baseEnd_1773114 : Nat := 910459737216280917020603

theorem tailTrace_1773114 : CollatzResearch.WordTrace tailWord_1773114 prefixEnd_1773114 910459737216280917020603 := by
  unfold tailWord_1773114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16167695124579569151819599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43113853665545517738185597 16167695124579569151819599)
  ·
    refine ⟨24251542686869353727729399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16167695124579569151819599 24251542686869353727729399)
    ·
      refine ⟨36377314030304030591594099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24251542686869353727729399 36377314030304030591594099)
      ·
        refine ⟨54565971045456045887391149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36377314030304030591594099 54565971045456045887391149)
        ·
          refine ⟨20462239142046017207771681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54565971045456045887391149 20462239142046017207771681)
          ·
            refine ⟨15346679356534512905828761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20462239142046017207771681 15346679356534512905828761)
            ·
              refine ⟨11510009517400884679371571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15346679356534512905828761 11510009517400884679371571)
              ·
                refine ⟨17265014276101327019057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11510009517400884679371571 17265014276101327019057357)
                ·
                  refine ⟨6474380353537997632146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17265014276101327019057357 6474380353537997632146509)
                  ·
                    refine ⟨2427892632576749112054941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6474380353537997632146509 2427892632576749112054941)
                    ·
                      refine ⟨910459737216280917020603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427892632576749112054941 910459737216280917020603)
                      ·
                        rfl

theorem cell23_1773114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_1773114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773114 prefixEnd_1773114 := by exact prefixLift 1773114
  have htrace : WordTrace (prefixWord ++ tailWord_1773114) baseStart_1773114 baseEnd_1773114 := by
    simpa [prefixWord, tailWord_1773114, baseEnd_1773114] using wordTrace_append hprefix tailTrace_1773114
  have hstable : (prefixWord ++ tailWord_1773114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773114).length < 2 ^ (prefixWord ++ tailWord_1773114).sum := by decide
  have hdescent : baseEnd_1773114 < baseStart_1773114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773131 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 3]
def baseStart_1773131 : Nat := 118140960795 + 1773131 * 2 ^ 59
def prefixEnd_1773131 : Nat := 4983230072969 + 3 ^ 40 * 1773131 * 2
def baseEnd_1773131 : Nat := 910468466387407350508025

theorem tailTrace_1773131 : CollatzResearch.WordTrace tailWord_1773131 prefixEnd_1773131 910468466387407350508025 := by
  unfold tailWord_1773131
  simp only [CollatzResearch.WordTrace]
  refine ⟨64671400539256688510647247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43114267026171125673764831 64671400539256688510647247)
  ·
    refine ⟨97007100808885032765970871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64671400539256688510647247 97007100808885032765970871)
    ·
      refine ⟨145510651213327549148956307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97007100808885032765970871 145510651213327549148956307)
      ·
        refine ⟨218265976819991323723434461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145510651213327549148956307 218265976819991323723434461)
        ·
          refine ⟨81849741307496746396287923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218265976819991323723434461 81849741307496746396287923)
          ·
            refine ⟨122774611961245119594431885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81849741307496746396287923 122774611961245119594431885)
            ·
              refine ⟨46040479485466919847911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122774611961245119594431885 46040479485466919847911957)
              ·
                refine ⟨2158147475881261867870873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46040479485466919847911957 2158147475881261867870873)
                ·
                  refine ⟨1618610606910946400903155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158147475881261867870873 1618610606910946400903155)
                  ·
                    refine ⟨2427915910366419601354733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618610606910946400903155 2427915910366419601354733)
                    ·
                      refine ⟨910468466387407350508025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2427915910366419601354733 910468466387407350508025)
                      ·
                        rfl

theorem cell23_1773131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 3].length) (baseStart_1773131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773131 prefixEnd_1773131 := by exact prefixLift 1773131
  have htrace : WordTrace (prefixWord ++ tailWord_1773131) baseStart_1773131 baseEnd_1773131 := by
    simpa [prefixWord, tailWord_1773131, baseEnd_1773131] using wordTrace_append hprefix tailTrace_1773131
  have hstable : (prefixWord ++ tailWord_1773131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773131).length < 2 ^ (prefixWord ++ tailWord_1773131).sum := by decide
  have hdescent : baseEnd_1773131 < baseStart_1773131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773132 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_1773132 : Nat := 118140960795 + 1773132 * 2 ^ 59
def prefixEnd_1773132 : Nat := 4983230072969 + 3 ^ 40 * 1773132 * 2
def baseEnd_1773132 : Nat := 910468979868061846595521

theorem tailTrace_1773132 : CollatzResearch.WordTrace tailWord_1773132 prefixEnd_1773132 910468979868061846595521 := by
  unfold tailWord_1773132
  simp only [CollatzResearch.WordTrace]
  refine ⟨32335718506126532840716825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43114291341502043787622433 32335718506126532840716825)
  ·
    refine ⟨24251788879594899630537619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32335718506126532840716825 24251788879594899630537619)
    ·
      refine ⟨36377683319392349445806429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24251788879594899630537619 36377683319392349445806429)
      ·
        refine ⟨13641631244772131042177411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36377683319392349445806429 13641631244772131042177411)
        ·
          refine ⟨20462446867158196563266117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13641631244772131042177411 20462446867158196563266117)
          ·
            refine ⟨3836708787592161855612397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20462446867158196563266117 3836708787592161855612397)
            ·
              refine ⟨1438765795347060695854649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3836708787592161855612397 1438765795347060695854649)
              ·
                refine ⟨1079074346510295521890987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438765795347060695854649 1079074346510295521890987)
                ·
                  refine ⟨1618611519765443282836481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079074346510295521890987 1618611519765443282836481)
                  ·
                    refine ⟨1213958639824082462127361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618611519765443282836481 1213958639824082462127361)
                    ·
                      refine ⟨910468979868061846595521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213958639824082462127361 910468979868061846595521)
                      ·
                        rfl

theorem cell23_1773132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_1773132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773132 prefixEnd_1773132 := by exact prefixLift 1773132
  have htrace : WordTrace (prefixWord ++ tailWord_1773132) baseStart_1773132 baseEnd_1773132 := by
    simpa [prefixWord, tailWord_1773132, baseEnd_1773132] using wordTrace_append hprefix tailTrace_1773132
  have hstable : (prefixWord ++ tailWord_1773132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773132).length < 2 ^ (prefixWord ++ tailWord_1773132).sum := by decide
  have hdescent : baseEnd_1773132 < baseStart_1773132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1773141 : Nat := 118140960795 + 1773141 * 2 ^ 59
def prefixEnd_1773141 : Nat := 4983230072969 + 3 ^ 40 * 1773141 * 2
def baseEnd_1773141 : Nat := 910473601193952311382979

theorem tailTrace_1773141 : CollatzResearch.WordTrace tailWord_1773141 prefixEnd_1773141 910473601193952311382979 := by
  unfold tailWord_1773141
  simp only [CollatzResearch.WordTrace]
  refine ⟨64671765269220460218511277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43114510179480306812340851 64671765269220460218511277)
  ·
    refine ⟨24251911975957672581941729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64671765269220460218511277 24251911975957672581941729)
    ·
      refine ⟨18188933981968254436456297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24251911975957672581941729 18188933981968254436456297)
      ·
        refine ⟨13641700486476190827342223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18188933981968254436456297 13641700486476190827342223)
        ·
          refine ⟨20462550729714286241013335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13641700486476190827342223 20462550729714286241013335)
          ·
            refine ⟨30693826094571429361520003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20462550729714286241013335 30693826094571429361520003)
            ·
              refine ⟨46040739141857144042280005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30693826094571429361520003 46040739141857144042280005)
              ·
                refine ⟨8632638589098214507927501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46040739141857144042280005 8632638589098214507927501)
                ·
                  refine ⟨3237239470911830440472813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8632638589098214507927501 3237239470911830440472813)
                  ·
                    refine ⟨1213964801591936415177305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237239470911830440472813 1213964801591936415177305)
                    ·
                      refine ⟨910473601193952311382979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1213964801591936415177305 910473601193952311382979)
                      ·
                        rfl

theorem cell23_1773141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1773141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773141 prefixEnd_1773141 := by exact prefixLift 1773141
  have htrace : WordTrace (prefixWord ++ tailWord_1773141) baseStart_1773141 baseEnd_1773141 := by
    simpa [prefixWord, tailWord_1773141, baseEnd_1773141] using wordTrace_append hprefix tailTrace_1773141
  have hstable : (prefixWord ++ tailWord_1773141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773141).length < 2 ^ (prefixWord ++ tailWord_1773141).sum := by decide
  have hdescent : baseEnd_1773141 < baseStart_1773141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773142 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1773142 : Nat := 118140960795 + 1773142 * 2 ^ 59
def prefixEnd_1773142 : Nat := 4983230072969 + 3 ^ 40 * 1773142 * 2
def baseEnd_1773142 : Nat := 303491371558202269156825

theorem tailTrace_1773142 : CollatzResearch.WordTrace tailWord_1773142 prefixEnd_1773142 303491371558202269156825 := by
  unfold tailWord_1773142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041987608888552336831105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43114534494811224926198453 4041987608888552336831105)
  ·
    refine ⟨3031490706666414252623329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4041987608888552336831105 3031490706666414252623329)
    ·
      refine ⟨2273618029999810689467497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3031490706666414252623329 2273618029999810689467497)
      ·
        refine ⟨1705213522499858017100623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273618029999810689467497 1705213522499858017100623)
        ·
          refine ⟨2557820283749787025650935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705213522499858017100623 2557820283749787025650935)
          ·
            refine ⟨3836730425624680538476403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557820283749787025650935 3836730425624680538476403)
            ·
              refine ⟨5755095638437020807714605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836730425624680538476403 5755095638437020807714605)
              ·
                refine ⟨2158160864413882802892977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5755095638437020807714605 2158160864413882802892977)
                ·
                  refine ⟨1618620648310412102169733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158160864413882802892977 1618620648310412102169733)
                  ·
                    refine ⟨303491371558202269156825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618620648310412102169733 303491371558202269156825)
                    ·
                      rfl

theorem cell23_1773142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1773142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773142 prefixEnd_1773142 := by exact prefixLift 1773142
  have htrace : WordTrace (prefixWord ++ tailWord_1773142) baseStart_1773142 baseEnd_1773142 := by
    simpa [prefixWord, tailWord_1773142, baseEnd_1773142] using wordTrace_append hprefix tailTrace_1773142
  have hstable : (prefixWord ++ tailWord_1773142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773142).length < 2 ^ (prefixWord ++ tailWord_1773142).sum := by decide
  have hdescent : baseEnd_1773142 < baseStart_1773142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773184 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1773184 : Nat := 118140960795 + 1773184 * 2 ^ 59
def prefixEnd_1773184 : Nat := 4983230072969 + 3 ^ 40 * 1773184 * 2
def baseEnd_1773184 : Nat := 910495680862095643145281

theorem tailTrace_1773184 : CollatzResearch.WordTrace tailWord_1773184 prefixEnd_1773184 910495680862095643145281 := by
  unfold tailWord_1773184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32336666804032339281163303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43115555738709785708217737 32336666804032339281163303)
  ·
    refine ⟨48505000206048508921744955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32336666804032339281163303 48505000206048508921744955)
    ·
      refine ⟨72757500309072763382617433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48505000206048508921744955 72757500309072763382617433)
      ·
        refine ⟨54568125231804572536963075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72757500309072763382617433 54568125231804572536963075)
        ·
          refine ⟨81852187847706858805444613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54568125231804572536963075 81852187847706858805444613)
          ·
            refine ⟨15347285221445036026020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81852187847706858805444613 15347285221445036026020865)
            ·
              refine ⟨11510463916083777019515649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15347285221445036026020865 11510463916083777019515649)
              ·
                refine ⟨8632847937062832764636737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11510463916083777019515649 8632847937062832764636737)
                ·
                  refine ⟨6474635952797124573477553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8632847937062832764636737 6474635952797124573477553)
                  ·
                    refine ⟨4855976964597843430108165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6474635952797124573477553 4855976964597843430108165)
                    ·
                      refine ⟨910495680862095643145281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4855976964597843430108165 910495680862095643145281)
                      ·
                        rfl

theorem cell23_1773184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1773184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773184 prefixEnd_1773184 := by exact prefixLift 1773184
  have htrace : WordTrace (prefixWord ++ tailWord_1773184) baseStart_1773184 baseEnd_1773184 := by
    simpa [prefixWord, tailWord_1773184, baseEnd_1773184] using wordTrace_append hprefix tailTrace_1773184
  have hstable : (prefixWord ++ tailWord_1773184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773184).length < 2 ^ (prefixWord ++ tailWord_1773184).sum := by decide
  have hdescent : baseEnd_1773184 < baseStart_1773184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773234 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1773234 : Nat := 118140960795 + 1773234 * 2 ^ 59
def prefixEnd_1773234 : Nat := 4983230072969 + 3 ^ 40 * 1773234 * 2
def baseEnd_1773234 : Nat := 910521354894820447520051

theorem tailTrace_1773234 : CollatzResearch.WordTrace tailWord_1773234 prefixEnd_1773234 910521354894820447520051 := by
  unfold tailWord_1773234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168789314470884275411689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43116771505255691401097837 16168789314470884275411689)
  ·
    refine ⟨12126591985853163206558767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16168789314470884275411689 12126591985853163206558767)
    ·
      refine ⟨18189887978779744809838151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12126591985853163206558767 18189887978779744809838151)
      ·
        refine ⟨27284831968169617214757227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18189887978779744809838151 27284831968169617214757227)
        ·
          refine ⟨40927247952254425822135841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27284831968169617214757227 40927247952254425822135841)
          ·
            refine ⟨30695435964190819366601881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40927247952254425822135841 30695435964190819366601881)
            ·
              refine ⟨23021576973143114524951411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30695435964190819366601881 23021576973143114524951411)
              ·
                refine ⟨34532365459714671787427117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23021576973143114524951411 34532365459714671787427117)
                ·
                  refine ⟨12949637047393001920285169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34532365459714671787427117 12949637047393001920285169)
                  ·
                    refine ⟨9712227785544751440213877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12949637047393001920285169 9712227785544751440213877)
                    ·
                      refine ⟨910521354894820447520051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9712227785544751440213877 910521354894820447520051)
                      ·
                        rfl

theorem cell23_1773234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1773234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773234 prefixEnd_1773234 := by exact prefixLift 1773234
  have htrace : WordTrace (prefixWord ++ tailWord_1773234) baseStart_1773234 baseEnd_1773234 := by
    simpa [prefixWord, tailWord_1773234, baseEnd_1773234] using wordTrace_append hprefix tailTrace_1773234
  have hstable : (prefixWord ++ tailWord_1773234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773234).length < 2 ^ (prefixWord ++ tailWord_1773234).sum := by decide
  have hdescent : baseEnd_1773234 < baseStart_1773234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773271 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 3, 4]
def baseStart_1773271 : Nat := 118140960795 + 1773271 * 2 ^ 59
def prefixEnd_1773271 : Nat := 4983230072969 + 3 ^ 40 * 1773271 * 2
def baseEnd_1773271 : Nat := 303513451226345600919127

theorem tailTrace_1773271 : CollatzResearch.WordTrace tailWord_1773271 prefixEnd_1773271 303513451226345600919127 := by
  unfold tailWord_1773271
  simp only [CollatzResearch.WordTrace]
  refine ⟨64676506758749492420743667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43117671172499661613829111 64676506758749492420743667)
  ·
    refine ⟨97014760138124238631115501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64676506758749492420743667 97014760138124238631115501)
    ·
      refine ⟨36380535051796589486668313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97014760138124238631115501 36380535051796589486668313)
      ·
        refine ⟨27285401288847442115001235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36380535051796589486668313 27285401288847442115001235)
        ·
          refine ⟨40928101933271163172501853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27285401288847442115001235 40928101933271163172501853)
          ·
            refine ⟨15348038224976686189688195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40928101933271163172501853 15348038224976686189688195)
            ·
              refine ⟨23022057337465029284532293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15348038224976686189688195 23022057337465029284532293)
              ·
                refine ⟨4316635750774692990849805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23022057337465029284532293 4316635750774692990849805)
                ·
                  refine ⟨1618738406540509871568677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4316635750774692990849805 1618738406540509871568677)
                  ·
                    refine ⟨303513451226345600919127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618738406540509871568677 303513451226345600919127)
                    ·
                      rfl

theorem cell23_1773271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_1773271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773271 prefixEnd_1773271 := by exact prefixLift 1773271
  have htrace : WordTrace (prefixWord ++ tailWord_1773271) baseStart_1773271 baseEnd_1773271 := by
    simpa [prefixWord, tailWord_1773271, baseEnd_1773271] using wordTrace_append hprefix tailTrace_1773271
  have hstable : (prefixWord ++ tailWord_1773271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773271).length < 2 ^ (prefixWord ++ tailWord_1773271).sum := by decide
  have hdescent : baseEnd_1773271 < baseStart_1773271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773284 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 10]
def baseStart_1773284 : Nat := 118140960795 + 1773284 * 2 ^ 59
def prefixEnd_1773284 : Nat := 4983230072969 + 3 ^ 40 * 1773284 * 2
def baseEnd_1773284 : Nat := 101171892103060583543869

theorem tailTrace_1773284 : CollatzResearch.WordTrace tailWord_1773284 prefixEnd_1773284 101171892103060583543869 := by
  unfold tailWord_1773284
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338490453851197820483453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43117987271801597093977937 32338490453851197820483453)
  ·
    refine ⟨12126933920194199182681295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32338490453851197820483453 12126933920194199182681295)
    ·
      refine ⟨18190400880291298774021943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12126933920194199182681295 18190400880291298774021943)
      ·
        refine ⟨27285601320436948161032915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18190400880291298774021943 27285601320436948161032915)
        ·
          refine ⟨40928401980655422241549373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27285601320436948161032915 40928401980655422241549373)
          ·
            refine ⟨15348150742745783340581015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40928401980655422241549373 15348150742745783340581015)
            ·
              refine ⟨23022226114118675010871523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15348150742745783340581015 23022226114118675010871523)
              ·
                refine ⟨34533339171178012516307285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23022226114118675010871523 34533339171178012516307285)
                ·
                  refine ⟨101171892103060583543869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34533339171178012516307285 101171892103060583543869)
                  ·
                    rfl

theorem cell23_1773284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_1773284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773284 prefixEnd_1773284 := by exact prefixLift 1773284
  have htrace : WordTrace (prefixWord ++ tailWord_1773284) baseStart_1773284 baseEnd_1773284 := by
    simpa [prefixWord, tailWord_1773284, baseEnd_1773284] using wordTrace_append hprefix tailTrace_1773284
  have hstable : (prefixWord ++ tailWord_1773284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773284).length < 2 ^ (prefixWord ++ tailWord_1773284).sum := by decide
  have hdescent : baseEnd_1773284 < baseStart_1773284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773298 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1773298 : Nat := 118140960795 + 1773298 * 2 ^ 59
def prefixEnd_1773298 : Nat := 4983230072969 + 3 ^ 40 * 1773298 * 2
def baseEnd_1773298 : Nat := 910554217656708197119757

theorem tailTrace_1773298 : CollatzResearch.WordTrace tailWord_1773298 prefixEnd_1773298 910554217656708197119757 := by
  unfold tailWord_1773298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169372882412919007994137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43118327686434450687984365 16169372882412919007994137)
  ·
    refine ⟨12127029661809689255995603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16169372882412919007994137 12127029661809689255995603)
    ·
      refine ⟨18190544492714533883993405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127029661809689255995603 18190544492714533883993405)
      ·
        refine ⟨6821454184767950206497527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18190544492714533883993405 6821454184767950206497527)
        ·
          refine ⟨10232181277151925309746291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821454184767950206497527 10232181277151925309746291)
          ·
            refine ⟨15348271915727887964619437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232181277151925309746291 15348271915727887964619437)
            ·
              refine ⟨5755601968397957986732289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15348271915727887964619437 5755601968397957986732289)
              ·
                refine ⟨4316701476298468490049217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755601968397957986732289 4316701476298468490049217)
                ·
                  refine ⟨3237526107223851367536913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316701476298468490049217 3237526107223851367536913)
                  ·
                    refine ⟨2428144580417888525652685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3237526107223851367536913 2428144580417888525652685)
                    ·
                      refine ⟨910554217656708197119757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428144580417888525652685 910554217656708197119757)
                      ·
                        rfl

theorem cell23_1773298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1773298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773298 prefixEnd_1773298 := by exact prefixLift 1773298
  have htrace : WordTrace (prefixWord ++ tailWord_1773298) baseStart_1773298 baseEnd_1773298 := by
    simpa [prefixWord, tailWord_1773298, baseEnd_1773298] using wordTrace_append hprefix tailTrace_1773298
  have hstable : (prefixWord ++ tailWord_1773298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773298).length < 2 ^ (prefixWord ++ tailWord_1773298).sum := by decide
  have hdescent : baseEnd_1773298 < baseStart_1773298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773304 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1773304 : Nat := 118140960795 + 1773304 * 2 ^ 59
def prefixEnd_1773304 : Nat := 4983230072969 + 3 ^ 40 * 1773304 * 2
def baseEnd_1773304 : Nat := 910557298540635173644729

theorem tailTrace_1773304 : CollatzResearch.WordTrace tailWord_1773304 prefixEnd_1773304 910557298540635173644729 := by
  unfold tailWord_1773304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338855183814969528347483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43118473578419959371129977 32338855183814969528347483)
  ·
    refine ⟨48508282775722454292521225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338855183814969528347483 48508282775722454292521225)
    ·
      refine ⟨36381212081791840719390919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48508282775722454292521225 36381212081791840719390919)
      ·
        refine ⟨54571818122687761079086379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36381212081791840719390919 54571818122687761079086379)
        ·
          refine ⟨81857727184031641618629569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54571818122687761079086379 81857727184031641618629569)
          ·
            refine ⟨61393295388023731213972177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81857727184031641618629569 61393295388023731213972177)
            ·
              refine ⟨46044971541017798410479133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61393295388023731213972177 46044971541017798410479133)
              ·
                refine ⟨17266864327881674403929675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46044971541017798410479133 17266864327881674403929675)
                ·
                  refine ⟨25900296491822511605894513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17266864327881674403929675 25900296491822511605894513)
                  ·
                    refine ⟨19425222368866883704420885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25900296491822511605894513 19425222368866883704420885)
                    ·
                      refine ⟨910557298540635173644729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19425222368866883704420885 910557298540635173644729)
                      ·
                        rfl

theorem cell23_1773304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1773304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773304 prefixEnd_1773304 := by exact prefixLift 1773304
  have htrace : WordTrace (prefixWord ++ tailWord_1773304) baseStart_1773304 baseEnd_1773304 := by
    simpa [prefixWord, tailWord_1773304, baseEnd_1773304] using wordTrace_append hprefix tailTrace_1773304
  have hstable : (prefixWord ++ tailWord_1773304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773304).length < 2 ^ (prefixWord ++ tailWord_1773304).sum := by decide
  have hdescent : baseEnd_1773304 < baseStart_1773304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773331 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 1, 5]
def baseStart_1773331 : Nat := 118140960795 + 1773331 * 2 ^ 59
def prefixEnd_1773331 : Nat := 4983230072969 + 3 ^ 40 * 1773331 * 2
def baseEnd_1773331 : Nat := 303523720839435522669035

theorem tailTrace_1773331 : CollatzResearch.WordTrace tailWord_1773331 prefixEnd_1773331 303523720839435522669035 := by
  unfold tailWord_1773331
  simp only [CollatzResearch.WordTrace]
  refine ⟨64678695138532122667927847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43119130092354748445285231 64678695138532122667927847)
  ·
    refine ⟨97018042707798184001891771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64678695138532122667927847 97018042707798184001891771)
    ·
      refine ⟨145527064061697276002837657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97018042707798184001891771 145527064061697276002837657)
      ·
        refine ⟨109145298046272957002128243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145527064061697276002837657 109145298046272957002128243)
        ·
          refine ⟨163717947069409435503192365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109145298046272957002128243 163717947069409435503192365)
          ·
            refine ⟨61394230151028538313697137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163717947069409435503192365 61394230151028538313697137)
            ·
              refine ⟨46045672613271403735272853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61394230151028538313697137 46045672613271403735272853)
              ·
                refine ⟨2158390903747097050090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46045672613271403735272853 2158390903747097050090915)
                ·
                  refine ⟨3237586355620645575136373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158390903747097050090915 3237586355620645575136373)
                  ·
                    refine ⟨303523720839435522669035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3237586355620645575136373 303523720839435522669035)
                    ·
                      rfl

theorem cell23_1773331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 5].length) (baseStart_1773331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773331 prefixEnd_1773331 := by exact prefixLift 1773331
  have htrace : WordTrace (prefixWord ++ tailWord_1773331) baseStart_1773331 baseEnd_1773331 := by
    simpa [prefixWord, tailWord_1773331, baseEnd_1773331] using wordTrace_append hprefix tailTrace_1773331
  have hstable : (prefixWord ++ tailWord_1773331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773331).length < 2 ^ (prefixWord ++ tailWord_1773331).sum := by decide
  have hdescent : baseEnd_1773331 < baseStart_1773331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773362 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_1773362 : Nat := 118140960795 + 1773362 * 2 ^ 59
def prefixEnd_1773362 : Nat := 4983230072969 + 3 ^ 40 * 1773362 * 2
def baseEnd_1773362 : Nat := 910587080418595946719463

theorem tailTrace_1773362 : CollatzResearch.WordTrace tailWord_1773362 prefixEnd_1773362 910587080418595946719463 := by
  unfold tailWord_1773362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169956450354953740576585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43119883867613209974870893 16169956450354953740576585)
  ·
    refine ⟨12127467337766215305432439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16169956450354953740576585 12127467337766215305432439)
    ·
      refine ⟨18191201006649322958148659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127467337766215305432439 18191201006649322958148659)
      ·
        refine ⟨27286801509973984437222989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191201006649322958148659 27286801509973984437222989)
        ·
          refine ⟨10232550566240244163958621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27286801509973984437222989 10232550566240244163958621)
          ·
            refine ⟨3837206462340091561484483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10232550566240244163958621 3837206462340091561484483)
            ·
              refine ⟨5755809693510137342226725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837206462340091561484483 5755809693510137342226725)
              ·
                refine ⟨1079214317533150751667511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5755809693510137342226725 1079214317533150751667511)
                ·
                  refine ⟨1618821476299726127501267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079214317533150751667511 1618821476299726127501267)
                  ·
                    refine ⟨2428232214449589191251901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1618821476299726127501267 2428232214449589191251901)
                    ·
                      refine ⟨910587080418595946719463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428232214449589191251901 910587080418595946719463)
                      ·
                        rfl

theorem cell23_1773362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_1773362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773362 prefixEnd_1773362 := by exact prefixLift 1773362
  have htrace : WordTrace (prefixWord ++ tailWord_1773362) baseStart_1773362 baseEnd_1773362 := by
    simpa [prefixWord, tailWord_1773362, baseEnd_1773362] using wordTrace_append hprefix tailTrace_1773362
  have hstable : (prefixWord ++ tailWord_1773362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773362).length < 2 ^ (prefixWord ++ tailWord_1773362).sum := by decide
  have hdescent : baseEnd_1773362 < baseStart_1773362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773385 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 3, 2, 2]
def baseStart_1773385 : Nat := 118140960795 + 1773385 * 2 ^ 59
def prefixEnd_1773385 : Nat := 4983230072969 + 3 ^ 40 * 1773385 * 2
def baseEnd_1773385 : Nat := 910598890473649356731857

theorem tailTrace_1773385 : CollatzResearch.WordTrace tailWord_1773385 prefixEnd_1773385 910598890473649356731857 := by
  unfold tailWord_1773385
  simp only [CollatzResearch.WordTrace]
  refine ⟨64680664680336489890393609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43120443120224326593595739 64680664680336489890393609)
  ·
    refine ⟨48510498510252367417795207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64680664680336489890393609 48510498510252367417795207)
    ·
      refine ⟨72765747765378551126692811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48510498510252367417795207 72765747765378551126692811)
      ·
        refine ⟨109148621648067826690039217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72765747765378551126692811 109148621648067826690039217)
        ·
          refine ⟨81861466236050870017529413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109148621648067826690039217 81861466236050870017529413)
          ·
            refine ⟨15349024919259538128286765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81861466236050870017529413 15349024919259538128286765)
            ·
              refine ⟨5755884344722326798107537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15349024919259538128286765 5755884344722326798107537)
              ·
                refine ⟨4316913258541745098580653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755884344722326798107537 4316913258541745098580653)
                ·
                  refine ⟨1618842471953154411967745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4316913258541745098580653 1618842471953154411967745)
                  ·
                    refine ⟨1214131853964865808975809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618842471953154411967745 1214131853964865808975809)
                    ·
                      refine ⟨910598890473649356731857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214131853964865808975809 910598890473649356731857)
                      ·
                        rfl

theorem cell23_1773385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2, 2].length) (baseStart_1773385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773385 prefixEnd_1773385 := by exact prefixLift 1773385
  have htrace : WordTrace (prefixWord ++ tailWord_1773385) baseStart_1773385 baseEnd_1773385 := by
    simpa [prefixWord, tailWord_1773385, baseEnd_1773385] using wordTrace_append hprefix tailTrace_1773385
  have hstable : (prefixWord ++ tailWord_1773385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773385).length < 2 ^ (prefixWord ++ tailWord_1773385).sum := by decide
  have hdescent : baseEnd_1773385 < baseStart_1773385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773389 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1773389 : Nat := 118140960795 + 1773389 * 2 ^ 59
def prefixEnd_1773389 : Nat := 4983230072969 + 3 ^ 40 * 1773389 * 2
def baseEnd_1773389 : Nat := 910600944396267341081839

theorem tailTrace_1773389 : CollatzResearch.WordTrace tailWord_1773389 prefixEnd_1773389 910600944396267341081839 := by
  unfold tailWord_1773389
  simp only [CollatzResearch.WordTrace]
  refine ⟨64680810572321998573539221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43120540381547999049026147 64680810572321998573539221)
  ·
    refine ⟨3031912995577593683134651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64680810572321998573539221 3031912995577593683134651)
    ·
      refine ⟨4547869493366390524701977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031912995577593683134651 4547869493366390524701977)
      ·
        refine ⟨3410902120024792893526483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4547869493366390524701977 3410902120024792893526483)
        ·
          refine ⟨5116353180037189340289725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410902120024792893526483 5116353180037189340289725)
          ·
            refine ⟨1918632442513946002608647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5116353180037189340289725 1918632442513946002608647)
            ·
              refine ⟨2877948663770919003912971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918632442513946002608647 2877948663770919003912971)
              ·
                refine ⟨4316922995656378505869457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877948663770919003912971 4316922995656378505869457)
                ·
                  refine ⟨3237692246742283879402093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316922995656378505869457 3237692246742283879402093)
                  ·
                    refine ⟨1214134592528356454775785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3237692246742283879402093 1214134592528356454775785)
                    ·
                      refine ⟨910600944396267341081839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214134592528356454775785 910600944396267341081839)
                      ·
                        rfl

theorem cell23_1773389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1773389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773389 prefixEnd_1773389 := by exact prefixLift 1773389
  have htrace : WordTrace (prefixWord ++ tailWord_1773389) baseStart_1773389 baseEnd_1773389 := by
    simpa [prefixWord, tailWord_1773389, baseEnd_1773389] using wordTrace_append hprefix tailTrace_1773389
  have hstable : (prefixWord ++ tailWord_1773389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773389).length < 2 ^ (prefixWord ++ tailWord_1773389).sum := by decide
  have hdescent : baseEnd_1773389 < baseStart_1773389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773412 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1773412 : Nat := 118140960795 + 1773412 * 2 ^ 59
def prefixEnd_1773412 : Nat := 4983230072969 + 3 ^ 40 * 1773412 * 2
def baseEnd_1773412 : Nat := 303537584817106917031411

theorem tailTrace_1773412 : CollatzResearch.WordTrace tailWord_1773412 prefixEnd_1773412 303537584817106917031411 := by
  unfold tailWord_1773412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32340824725619336750813245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43121099634159115667750993 32340824725619336750813245)
  ·
    refine ⟨12127809272107251281554967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32340824725619336750813245 12127809272107251281554967)
    ·
      refine ⟨18191713908160876922332451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127809272107251281554967 18191713908160876922332451)
      ·
        refine ⟨27287570862241315383498677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191713908160876922332451 27287570862241315383498677)
        ·
          refine ⟨2558209768335123317203001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27287570862241315383498677 2558209768335123317203001)
          ·
            refine ⟨1918657326251342487902251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558209768335123317203001 1918657326251342487902251)
            ·
              refine ⟨2877985989377013731853377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918657326251342487902251 2877985989377013731853377)
              ·
                refine ⟨2158489492032760298890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877985989377013731853377 2158489492032760298890033)
                ·
                  refine ⟨1618867119024570224167525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2158489492032760298890033 1618867119024570224167525)
                  ·
                    refine ⟨303537584817106917031411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618867119024570224167525 303537584817106917031411)
                    ·
                      rfl

theorem cell23_1773412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1773412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773412 prefixEnd_1773412 := by exact prefixLift 1773412
  have htrace : WordTrace (prefixWord ++ tailWord_1773412) baseStart_1773412 baseEnd_1773412 := by
    simpa [prefixWord, tailWord_1773412, baseEnd_1773412] using wordTrace_append hprefix tailTrace_1773412
  have hstable : (prefixWord ++ tailWord_1773412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773412).length < 2 ^ (prefixWord ++ tailWord_1773412).sum := by decide
  have hdescent : baseEnd_1773412 < baseStart_1773412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773421 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1773421 : Nat := 118140960795 + 1773421 * 2 ^ 59
def prefixEnd_1773421 : Nat := 4983230072969 + 3 ^ 40 * 1773421 * 2
def baseEnd_1773421 : Nat := 303539125259070405293897

theorem tailTrace_1773421 : CollatzResearch.WordTrace tailWord_1773421 prefixEnd_1773421 303539125259070405293897 := by
  unfold tailWord_1773421
  simp only [CollatzResearch.WordTrace]
  refine ⟨64681977708206068038704117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43121318472137378692469411 64681977708206068038704117)
  ·
    refine ⟨6063935410144318878628511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64681977708206068038704117 6063935410144318878628511)
    ·
      refine ⟨9095903115216478317942767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063935410144318878628511 9095903115216478317942767)
      ·
        refine ⟨13643854672824717476914151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9095903115216478317942767 13643854672824717476914151)
        ·
          refine ⟨20465782009237076215371227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13643854672824717476914151 20465782009237076215371227)
          ·
            refine ⟨30698673013855614323056841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20465782009237076215371227 30698673013855614323056841)
            ·
              refine ⟨23024004760391710742292631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30698673013855614323056841 23024004760391710742292631)
              ·
                refine ⟨34536007140587566113438947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23024004760391710742292631 34536007140587566113438947)
                ·
                  refine ⟨51804010710881349170158421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34536007140587566113438947 51804010710881349170158421)
                  ·
                    refine ⟨303539125259070405293897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51804010710881349170158421 303539125259070405293897)
                    ·
                      rfl

theorem cell23_1773421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1773421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773421 prefixEnd_1773421 := by exact prefixLift 1773421
  have htrace : WordTrace (prefixWord ++ tailWord_1773421) baseStart_1773421 baseEnd_1773421 := by
    simpa [prefixWord, tailWord_1773421, baseEnd_1773421] using wordTrace_append hprefix tailTrace_1773421
  have hstable : (prefixWord ++ tailWord_1773421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773421).length < 2 ^ (prefixWord ++ tailWord_1773421).sum := by decide
  have hdescent : baseEnd_1773421 < baseStart_1773421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773470 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1773470 : Nat := 118140960795 + 1773470 * 2 ^ 59
def prefixEnd_1773470 : Nat := 4983230072969 + 3 ^ 40 * 1773470 * 2
def baseEnd_1773470 : Nat := 910642536329281524168967

theorem tailTrace_1773470 : CollatzResearch.WordTrace tailWord_1773470 prefixEnd_1773470 910642536329281524168967 := by
  unfold tailWord_1773470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085470610628568675904733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43122509923352366271491909 8085470610628568675904733)
  ·
    refine ⟨3032051478985713253464275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8085470610628568675904733 3032051478985713253464275)
    ·
      refine ⟨4548077218478569880196413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032051478985713253464275 4548077218478569880196413)
      ·
        refine ⟨1705528956929463705073655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4548077218478569880196413 1705528956929463705073655)
        ·
          refine ⟨2558293435394195557610483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705528956929463705073655 2558293435394195557610483)
          ·
            refine ⟨3837440153091293336415725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558293435394195557610483 3837440153091293336415725)
            ·
              refine ⟨1439040057409235001155897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837440153091293336415725 1439040057409235001155897)
              ·
                refine ⟨1079280043056926250866923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439040057409235001155897 1079280043056926250866923)
                ·
                  refine ⟨1618920064585389376300385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079280043056926250866923 1618920064585389376300385)
                  ·
                    refine ⟨1214190048439042032225289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1618920064585389376300385 1214190048439042032225289)
                    ·
                      refine ⟨910642536329281524168967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214190048439042032225289 910642536329281524168967)
                      ·
                        rfl

theorem cell23_1773470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1773470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773470 prefixEnd_1773470 := by exact prefixLift 1773470
  have htrace : WordTrace (prefixWord ++ tailWord_1773470) baseStart_1773470 baseEnd_1773470 := by
    simpa [prefixWord, tailWord_1773470, baseEnd_1773470] using wordTrace_append hprefix tailTrace_1773470
  have hstable : (prefixWord ++ tailWord_1773470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773470).length < 2 ^ (prefixWord ++ tailWord_1773470).sum := by decide
  have hdescent : baseEnd_1773470 < baseStart_1773470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773481 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 7]
def baseStart_1773481 : Nat := 118140960795 + 1773481 * 2 ^ 59
def prefixEnd_1773481 : Nat := 4983230072969 + 3 ^ 40 * 1773481 * 2
def baseEnd_1773481 : Nat := 101183131624053442347935

theorem tailTrace_1773481 : CollatzResearch.WordTrace tailWord_1773481 prefixEnd_1773481 101183131624053442347935 := by
  unfold tailWord_1773481
  simp only [CollatzResearch.WordTrace]
  refine ⟨64684166087988698285888297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43122777391992465523925531 64684166087988698285888297)
  ·
    refine ⟨48513124565991523714416223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64684166087988698285888297 48513124565991523714416223)
    ·
      refine ⟨72769686848987285571624335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48513124565991523714416223 72769686848987285571624335)
      ·
        refine ⟨109154530273480928357436503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72769686848987285571624335 109154530273480928357436503)
        ·
          refine ⟨163731795410221392536154755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109154530273480928357436503 163731795410221392536154755)
          ·
            refine ⟨245597693115332088804232133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163731795410221392536154755 245597693115332088804232133)
            ·
              refine ⟨46049567459124766650793525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245597693115332088804232133 46049567459124766650793525)
              ·
                refine ⟨4317146949292946873511893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46049567459124766650793525 4317146949292946873511893)
                ·
                  refine ⟨101183131624053442347935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4317146949292946873511893 101183131624053442347935)
                  ·
                    rfl

theorem cell23_1773481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_1773481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773481 prefixEnd_1773481 := by exact prefixLift 1773481
  have htrace : WordTrace (prefixWord ++ tailWord_1773481) baseStart_1773481 baseEnd_1773481 := by
    simpa [prefixWord, tailWord_1773481, baseEnd_1773481] using wordTrace_append hprefix tailTrace_1773481
  have hstable : (prefixWord ++ tailWord_1773481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773481).length < 2 ^ (prefixWord ++ tailWord_1773481).sum := by decide
  have hdescent : baseEnd_1773481 < baseStart_1773481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773528 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1773528 : Nat := 118140960795 + 1773528 * 2 ^ 59
def prefixEnd_1773528 : Nat := 4983230072969 + 3 ^ 40 * 1773528 * 2
def baseEnd_1773528 : Nat := 303557439402414099081233

theorem tailTrace_1773528 : CollatzResearch.WordTrace tailWord_1773528 prefixEnd_1773528 303557439402414099081233 := by
  unfold tailWord_1773528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32342940159409212656424619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43123920212545616875232825 32342940159409212656424619)
  ·
    refine ⟨48514410239113818984636929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32342940159409212656424619 48514410239113818984636929)
    ·
      refine ⟨36385807679335364238477697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48514410239113818984636929 36385807679335364238477697)
      ·
        refine ⟨27289355759501523178858273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36385807679335364238477697 27289355759501523178858273)
        ·
          refine ⟨20467016819626142384143705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27289355759501523178858273 20467016819626142384143705)
          ·
            refine ⟨15350262614719606788107779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20467016819626142384143705 15350262614719606788107779)
            ·
              refine ⟨23025393922079410182161669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350262614719606788107779 23025393922079410182161669)
              ·
                refine ⟨4317261360389889409155313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23025393922079410182161669 4317261360389889409155313)
                ·
                  refine ⟨3237946020292417056866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317261360389889409155313 3237946020292417056866485)
                  ·
                    refine ⟨303557439402414099081233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3237946020292417056866485 303557439402414099081233)
                    ·
                      rfl

theorem cell23_1773528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1773528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773528 prefixEnd_1773528 := by exact prefixLift 1773528
  have htrace : WordTrace (prefixWord ++ tailWord_1773528) baseStart_1773528 baseEnd_1773528 := by
    simpa [prefixWord, tailWord_1773528, baseEnd_1773528] using wordTrace_append hprefix tailTrace_1773528
  have hstable : (prefixWord ++ tailWord_1773528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773528).length < 2 ^ (prefixWord ++ tailWord_1773528).sum := by decide
  have hdescent : baseEnd_1773528 < baseStart_1773528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773535 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 5, 2]
def baseStart_1773535 : Nat := 118140960795 + 1773535 * 2 ^ 59
def prefixEnd_1773535 : Nat := 4983230072969 + 3 ^ 40 * 1773535 * 2
def baseEnd_1773535 : Nat := 910675912571823769856167

theorem tailTrace_1773535 : CollatzResearch.WordTrace tailWord_1773535 prefixEnd_1773535 910675912571823769856167 := by
  unfold tailWord_1773535
  simp only [CollatzResearch.WordTrace]
  refine ⟨64686135629793065508354059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43124090419862043672236039 64686135629793065508354059)
  ·
    refine ⟨97029203444689598262531089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64686135629793065508354059 97029203444689598262531089)
    ·
      refine ⟨72771902583517198696898317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97029203444689598262531089 72771902583517198696898317)
      ·
        refine ⟨27289463468818949511336869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72771902583517198696898317 27289463468818949511336869)
        ·
          refine ⟨5116774400403553033375663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27289463468818949511336869 5116774400403553033375663)
          ·
            refine ⟨7675161600605329550063495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116774400403553033375663 7675161600605329550063495)
            ·
              refine ⟨11512742400907994325095243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675161600605329550063495 11512742400907994325095243)
              ·
                refine ⟨17269113601361991487642865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11512742400907994325095243 17269113601361991487642865)
                ·
                  refine ⟨12951835201021493615732149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17269113601361991487642865 12951835201021493615732149)
                  ·
                    refine ⟨1214234550095765026474889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12951835201021493615732149 1214234550095765026474889)
                    ·
                      refine ⟨910675912571823769856167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214234550095765026474889 910675912571823769856167)
                      ·
                        rfl

theorem cell23_1773535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_1773535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773535 prefixEnd_1773535 := by exact prefixLift 1773535
  have htrace : WordTrace (prefixWord ++ tailWord_1773535) baseStart_1773535 baseEnd_1773535 := by
    simpa [prefixWord, tailWord_1773535, baseEnd_1773535] using wordTrace_append hprefix tailTrace_1773535
  have hstable : (prefixWord ++ tailWord_1773535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773535).length < 2 ^ (prefixWord ++ tailWord_1773535).sum := by decide
  have hdescent : baseEnd_1773535 < baseStart_1773535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773548 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1773548 : Nat := 118140960795 + 1773548 * 2 ^ 59
def prefixEnd_1773548 : Nat := 4983230072969 + 3 ^ 40 * 1773548 * 2
def baseEnd_1773548 : Nat := 910682587820332218993607

theorem tailTrace_1773548 : CollatzResearch.WordTrace tailWord_1773548 prefixEnd_1773548 910682587820332218993607 := by
  unfold tailWord_1773548
  simp only [CollatzResearch.WordTrace]
  refine ⟨32343304889372984364288649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43124406519163979152384865 32343304889372984364288649)
  ·
    refine ⟨24257478667029738273216487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32343304889372984364288649 24257478667029738273216487)
    ·
      refine ⟨36386218000544607409824731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257478667029738273216487 36386218000544607409824731)
      ·
        refine ⟨54579327000816911114737097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36386218000544607409824731 54579327000816911114737097)
        ·
          refine ⟨40934495250612683336052823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54579327000816911114737097 40934495250612683336052823)
          ·
            refine ⟨61401742875919025004079235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40934495250612683336052823 61401742875919025004079235)
            ·
              refine ⟨92102614313878537506118853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61401742875919025004079235 92102614313878537506118853)
              ·
                refine ⟨17269240183852225782397285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92102614313878537506118853 17269240183852225782397285)
                ·
                  refine ⟨3237982534472292334199491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17269240183852225782397285 3237982534472292334199491)
                  ·
                    refine ⟨4856973801708438501299237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237982534472292334199491 4856973801708438501299237)
                    ·
                      refine ⟨910682587820332218993607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4856973801708438501299237 910682587820332218993607)
                      ·
                        rfl

theorem cell23_1773548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1773548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773548 prefixEnd_1773548 := by exact prefixLift 1773548
  have htrace : WordTrace (prefixWord ++ tailWord_1773548) baseStart_1773548 baseEnd_1773548 := by
    simpa [prefixWord, tailWord_1773548, baseEnd_1773548] using wordTrace_append hprefix tailTrace_1773548
  have hstable : (prefixWord ++ tailWord_1773548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773548).length < 2 ^ (prefixWord ++ tailWord_1773548).sum := by decide
  have hdescent : baseEnd_1773548 < baseStart_1773548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773565 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1773565 : Nat := 118140960795 + 1773565 * 2 ^ 59
def prefixEnd_1773565 : Nat := 4983230072969 + 3 ^ 40 * 1773565 * 2
def baseEnd_1773565 : Nat := 910691316991458652481029

theorem tailTrace_1773565 : CollatzResearch.WordTrace tailWord_1773565 prefixEnd_1773565 910691316991458652481029 := by
  unfold tailWord_1773565
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687229819684380631946149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43124819879789587087964099 64687229819684380631946149)
  ·
    refine ⟨12128855591190821368489903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64687229819684380631946149 12128855591190821368489903)
    ·
      refine ⟨18193283386786232052734855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12128855591190821368489903 18193283386786232052734855)
      ·
        refine ⟨27289925080179348079102283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18193283386786232052734855 27289925080179348079102283)
        ·
          refine ⟨40934887620269022118653425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289925080179348079102283 40934887620269022118653425)
          ·
            refine ⟨30701165715201766588990069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40934887620269022118653425 30701165715201766588990069)
            ·
              refine ⟨2878234285800165617717819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30701165715201766588990069 2878234285800165617717819)
              ·
                refine ⟨4317351428700248426576729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878234285800165617717819 4317351428700248426576729)
                ·
                  refine ⟨3238013571525186319932547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317351428700248426576729 3238013571525186319932547)
                  ·
                    refine ⟨4857020357287779479898821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238013571525186319932547 4857020357287779479898821)
                    ·
                      refine ⟨910691316991458652481029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4857020357287779479898821 910691316991458652481029)
                      ·
                        rfl

theorem cell23_1773565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1773565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773565 prefixEnd_1773565 := by exact prefixLift 1773565
  have htrace : WordTrace (prefixWord ++ tailWord_1773565) baseStart_1773565 baseEnd_1773565 := by
    simpa [prefixWord, tailWord_1773565, baseEnd_1773565] using wordTrace_append hprefix tailTrace_1773565
  have hstable : (prefixWord ++ tailWord_1773565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773565).length < 2 ^ (prefixWord ++ tailWord_1773565).sum := by decide
  have hdescent : baseEnd_1773565 < baseStart_1773565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773592 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 1, 4]
def baseStart_1773592 : Nat := 118140960795 + 1773592 * 2 ^ 59
def prefixEnd_1773592 : Nat := 4983230072969 + 3 ^ 40 * 1773592 * 2
def baseEnd_1773592 : Nat := 303568393656376682281135

theorem tailTrace_1773592 : CollatzResearch.WordTrace tailWord_1773592 prefixEnd_1773592 303568393656376682281135 := by
  unfold tailWord_1773592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32344107295293282121589515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43125476393724376162119353 32344107295293282121589515)
  ·
    refine ⟨48516160942939923182384273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32344107295293282121589515 48516160942939923182384273)
    ·
      refine ⟨36387120707204942386788205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48516160942939923182384273 36387120707204942386788205)
      ·
        refine ⟨13645170265201853395045577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36387120707204942386788205 13645170265201853395045577)
        ·
          refine ⟨10233877698901390046284183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13645170265201853395045577 10233877698901390046284183)
          ·
            refine ⟨15350816548352085069426275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10233877698901390046284183 15350816548352085069426275)
            ·
              refine ⟨23026224822528127604139413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15350816548352085069426275 23026224822528127604139413)
              ·
                refine ⟨1079354288556005981444035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23026224822528127604139413 1079354288556005981444035)
                ·
                  refine ⟨1619031432834008972166053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079354288556005981444035 1619031432834008972166053)
                  ·
                    refine ⟨303568393656376682281135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619031432834008972166053 303568393656376682281135)
                    ·
                      rfl

theorem cell23_1773592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_1773592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773592 prefixEnd_1773592 := by exact prefixLift 1773592
  have htrace : WordTrace (prefixWord ++ tailWord_1773592) baseStart_1773592 baseEnd_1773592 := by
    simpa [prefixWord, tailWord_1773592, baseEnd_1773592] using wordTrace_append hprefix tailTrace_1773592
  have hstable : (prefixWord ++ tailWord_1773592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773592).length < 2 ^ (prefixWord ++ tailWord_1773592).sum := by decide
  have hdescent : baseEnd_1773592 < baseStart_1773592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773615 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_1773615 : Nat := 118140960795 + 1773615 * 2 ^ 59
def prefixEnd_1773615 : Nat := 4983230072969 + 3 ^ 40 * 1773615 * 2
def baseEnd_1773615 : Nat := 910716991024183456855799

theorem tailTrace_1773615 : CollatzResearch.WordTrace tailWord_1773615 prefixEnd_1773615 910716991024183456855799 := by
  unfold tailWord_1773615
  simp only [CollatzResearch.WordTrace]
  refine ⟨64689053469503239171266299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43126035646335492780844199 64689053469503239171266299)
  ·
    refine ⟨97033580204254858756899449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64689053469503239171266299 97033580204254858756899449)
    ·
      refine ⟨72775185153191144067674587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97033580204254858756899449 72775185153191144067674587)
      ·
        refine ⟨109162777729786716101511881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72775185153191144067674587 109162777729786716101511881)
        ·
          refine ⟨81872083297340037076133911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109162777729786716101511881 81872083297340037076133911)
          ·
            refine ⟨122808124946010055614200867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81872083297340037076133911 122808124946010055614200867)
            ·
              refine ⟨184212187419015083421301301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122808124946010055614200867 184212187419015083421301301)
              ·
                refine ⟨17269892570532664070746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184212187419015083421301301 17269892570532664070746997)
                ·
                  refine ⟨1619052428487437256632531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17269892570532664070746997 1619052428487437256632531)
                  ·
                    refine ⟨2428578642731155884948797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619052428487437256632531 2428578642731155884948797)
                    ·
                      refine ⟨910716991024183456855799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428578642731155884948797 910716991024183456855799)
                      ·
                        rfl

theorem cell23_1773615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_1773615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773615 prefixEnd_1773615 := by exact prefixLift 1773615
  have htrace : WordTrace (prefixWord ++ tailWord_1773615) baseStart_1773615 baseEnd_1773615 := by
    simpa [prefixWord, tailWord_1773615, baseEnd_1773615] using wordTrace_append hprefix tailTrace_1773615
  have hstable : (prefixWord ++ tailWord_1773615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773615).length < 2 ^ (prefixWord ++ tailWord_1773615).sum := by decide
  have hdescent : baseEnd_1773615 < baseStart_1773615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773689 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 1, 1, 4]
def baseStart_1773689 : Nat := 118140960795 + 1773689 * 2 ^ 59
def prefixEnd_1773689 : Nat := 4983230072969 + 3 ^ 40 * 1773689 * 2
def baseEnd_1773689 : Nat := 910754988592616167330459

theorem tailTrace_1773689 : CollatzResearch.WordTrace tailWord_1773689 prefixEnd_1773689 910754988592616167330459 := by
  unfold tailWord_1773689
  simp only [CollatzResearch.WordTrace]
  refine ⟨64691752471235149809460121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43127834980823433206306747 64691752471235149809460121)
  ·
    refine ⟨48518814353426362357095091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64691752471235149809460121 48518814353426362357095091)
    ·
      refine ⟨72778221530139543535642637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48518814353426362357095091 72778221530139543535642637)
      ·
        refine ⟨27291833073802328825865989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72778221530139543535642637 27291833073802328825865989)
        ·
          refine ⟨5117218701337936654849873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27291833073802328825865989 5117218701337936654849873)
          ·
            refine ⟨3837914026003452491137405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5117218701337936654849873 3837914026003452491137405)
            ·
              refine ⟨1439217759751294684176527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837914026003452491137405 1439217759751294684176527)
              ·
                refine ⟨2158826639626942026264791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439217759751294684176527 2158826639626942026264791)
                ·
                  refine ⟨3238239959440413039397187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158826639626942026264791 3238239959440413039397187)
                  ·
                    refine ⟨4857359939160619559095781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238239959440413039397187 4857359939160619559095781)
                    ·
                      refine ⟨910754988592616167330459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4857359939160619559095781 910754988592616167330459)
                      ·
                        rfl

theorem cell23_1773689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_1773689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773689 prefixEnd_1773689 := by exact prefixLift 1773689
  have htrace : WordTrace (prefixWord ++ tailWord_1773689) baseStart_1773689 baseEnd_1773689 := by
    simpa [prefixWord, tailWord_1773689, baseEnd_1773689] using wordTrace_append hprefix tailTrace_1773689
  have hstable : (prefixWord ++ tailWord_1773689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773689).length < 2 ^ (prefixWord ++ tailWord_1773689).sum := by decide
  have hdescent : baseEnd_1773689 < baseStart_1773689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773692 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_1773692 : Nat := 118140960795 + 1773692 * 2 ^ 59
def prefixEnd_1773692 : Nat := 4983230072969 + 3 ^ 40 * 1773692 * 2
def baseEnd_1773692 : Nat := 910756529034579655592945

theorem tailTrace_1773692 : CollatzResearch.WordTrace tailWord_1773692 prefixEnd_1773692 910756529034579655592945 := by
  unfold tailWord_1773692
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345930945112140660909665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43127907926816187547879553 32345930945112140660909665)
  ·
    refine ⟨24259448208834105495682249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32345930945112140660909665 24259448208834105495682249)
    ·
      refine ⟨18194586156625579121761687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24259448208834105495682249 18194586156625579121761687)
      ·
        refine ⟨27291879234938368682642531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18194586156625579121761687 27291879234938368682642531)
        ·
          refine ⟨40937818852407553023963797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27291879234938368682642531 40937818852407553023963797)
          ·
            refine ⟨1918960258706604047998303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40937818852407553023963797 1918960258706604047998303)
            ·
              refine ⟨2878440388059906071997455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918960258706604047998303 2878440388059906071997455)
              ·
                refine ⟨4317660582089859107996183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878440388059906071997455 4317660582089859107996183)
                ·
                  refine ⟨6476490873134788661994275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317660582089859107996183 6476490873134788661994275)
                  ·
                    refine ⟨9714736309702182992991413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476490873134788661994275 9714736309702182992991413)
                    ·
                      refine ⟨910756529034579655592945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9714736309702182992991413 910756529034579655592945)
                      ·
                        rfl

theorem cell23_1773692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_1773692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773692 prefixEnd_1773692 := by exact prefixLift 1773692
  have htrace : WordTrace (prefixWord ++ tailWord_1773692) baseStart_1773692 baseEnd_1773692 := by
    simpa [prefixWord, tailWord_1773692, baseEnd_1773692] using wordTrace_append hprefix tailTrace_1773692
  have hstable : (prefixWord ++ tailWord_1773692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773692).length < 2 ^ (prefixWord ++ tailWord_1773692).sum := by decide
  have hdescent : baseEnd_1773692 < baseStart_1773692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773705 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_1773705 : Nat := 118140960795 + 1773705 * 2 ^ 59
def prefixEnd_1773705 : Nat := 4983230072969 + 3 ^ 40 * 1773705 * 2
def baseEnd_1773705 : Nat := 910763204283088104730385

theorem tailTrace_1773705 : CollatzResearch.WordTrace tailWord_1773705 prefixEnd_1773705 910763204283088104730385 := by
  unfold tailWord_1773705
  simp only [CollatzResearch.WordTrace]
  refine ⟨64692336039177184542042569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43128224026118123028028379 64692336039177184542042569)
  ·
    refine ⟨48519252029382888406531927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64692336039177184542042569 48519252029382888406531927)
    ·
      refine ⟨72778878044074332609797891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48519252029382888406531927 72778878044074332609797891)
      ·
        refine ⟨109168317066111498914696837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72778878044074332609797891 109168317066111498914696837)
        ·
          refine ⟨20469059449895906046505657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109168317066111498914696837 20469059449895906046505657)
          ·
            refine ⟨15351794587421929534879243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20469059449895906046505657 15351794587421929534879243)
            ·
              refine ⟨23027691881132894302318865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351794587421929534879243 23027691881132894302318865)
              ·
                refine ⟨17270768910849670726739149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23027691881132894302318865 17270768910849670726739149)
                ·
                  refine ⟨6476538341568626522527181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17270768910849670726739149 6476538341568626522527181)
                  ·
                    refine ⟨2428701878088234945947693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6476538341568626522527181 2428701878088234945947693)
                    ·
                      refine ⟨910763204283088104730385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428701878088234945947693 910763204283088104730385)
                      ·
                        rfl

theorem cell23_1773705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_1773705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773705 prefixEnd_1773705 := by exact prefixLift 1773705
  have htrace : WordTrace (prefixWord ++ tailWord_1773705) baseStart_1773705 baseEnd_1773705 := by
    simpa [prefixWord, tailWord_1773705, baseEnd_1773705] using wordTrace_append hprefix tailTrace_1773705
  have hstable : (prefixWord ++ tailWord_1773705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773705).length < 2 ^ (prefixWord ++ tailWord_1773705).sum := by decide
  have hdescent : baseEnd_1773705 < baseStart_1773705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773765 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1773765 : Nat := 118140960795 + 1773765 * 2 ^ 59
def prefixEnd_1773765 : Nat := 4983230072969 + 3 ^ 40 * 1773765 * 2
def baseEnd_1773765 : Nat := 910794013122357869980109

theorem tailTrace_1773765 : CollatzResearch.WordTrace tailWord_1773765 prefixEnd_1773765 910794013122357869980109 := by
  unfold tailWord_1773765
  simp only [CollatzResearch.WordTrace]
  refine ⟨64694524418959814789226749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43129682945973209859484499 64694524418959814789226749)
  ·
    refine ⟨24260446657109930545960031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64694524418959814789226749 24260446657109930545960031)
    ·
      refine ⟨36390669985664895818940047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24260446657109930545960031 36390669985664895818940047)
      ·
        refine ⟨54586004978497343728410071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36390669985664895818940047 54586004978497343728410071)
        ·
          refine ⟨81879007467746015592615107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54586004978497343728410071 81879007467746015592615107)
          ·
            refine ⟨122818511201619023388922661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81879007467746015592615107 122818511201619023388922661)
            ·
              refine ⟨23028470850303566885422999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122818511201619023388922661 23028470850303566885422999)
              ·
                refine ⟨34542706275455350328134499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23028470850303566885422999 34542706275455350328134499)
                ·
                  refine ⟨51814059413183025492201749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34542706275455350328134499 51814059413183025492201749)
                  ·
                    refine ⟨2428784034992954319946957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51814059413183025492201749 2428784034992954319946957)
                    ·
                      refine ⟨910794013122357869980109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428784034992954319946957 910794013122357869980109)
                      ·
                        rfl

theorem cell23_1773765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1773765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773765 prefixEnd_1773765 := by exact prefixLift 1773765
  have htrace : WordTrace (prefixWord ++ tailWord_1773765) baseStart_1773765 baseEnd_1773765 := by
    simpa [prefixWord, tailWord_1773765, baseEnd_1773765] using wordTrace_append hprefix tailTrace_1773765
  have hstable : (prefixWord ++ tailWord_1773765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773765).length < 2 ^ (prefixWord ++ tailWord_1773765).sum := by decide
  have hdescent : baseEnd_1773765 < baseStart_1773765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773775 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_1773775 : Nat := 118140960795 + 1773775 * 2 ^ 59
def prefixEnd_1773775 : Nat := 4983230072969 + 3 ^ 40 * 1773775 * 2
def baseEnd_1773775 : Nat := 910799147928902830855063

theorem tailTrace_1773775 : CollatzResearch.WordTrace tailWord_1773775 prefixEnd_1773775 910799147928902830855063 := by
  unfold tailWord_1773775
  simp only [CollatzResearch.WordTrace]
  refine ⟨64694889148923586497090779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43129926099282390998060519 64694889148923586497090779)
  ·
    refine ⟨97042333723385379745636169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64694889148923586497090779 97042333723385379745636169)
    ·
      refine ⟨72781750292539034809227127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97042333723385379745636169 72781750292539034809227127)
      ·
        refine ⟨109172625438808552213840691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72781750292539034809227127 109172625438808552213840691)
        ·
          refine ⟨163758938158212828320761037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109172625438808552213840691 163758938158212828320761037)
          ·
            refine ⟨61409601809329810620285389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163758938158212828320761037 61409601809329810620285389)
            ·
              refine ⟨23028600678498678982607021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61409601809329810620285389 23028600678498678982607021)
              ·
                refine ⟨8635725254437004618477633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23028600678498678982607021 8635725254437004618477633)
                ·
                  refine ⟨6476793940827753463858225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635725254437004618477633 6476793940827753463858225)
                  ·
                    refine ⟨4857595455620815097893669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6476793940827753463858225 4857595455620815097893669)
                    ·
                      refine ⟨910799147928902830855063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4857595455620815097893669 910799147928902830855063)
                      ·
                        rfl

theorem cell23_1773775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_1773775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773775 prefixEnd_1773775 := by exact prefixLift 1773775
  have htrace : WordTrace (prefixWord ++ tailWord_1773775) baseStart_1773775 baseEnd_1773775 := by
    simpa [prefixWord, tailWord_1773775, baseEnd_1773775] using wordTrace_append hprefix tailTrace_1773775
  have hstable : (prefixWord ++ tailWord_1773775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773775).length < 2 ^ (prefixWord ++ tailWord_1773775).sum := by decide
  have hdescent : baseEnd_1773775 < baseStart_1773775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773785 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 7]
def baseStart_1773785 : Nat := 118140960795 + 1773785 * 2 ^ 59
def prefixEnd_1773785 : Nat := 4983230072969 + 3 ^ 40 * 1773785 * 2
def baseEnd_1773785 : Nat := 101200475859494199081113

theorem tailTrace_1773785 : CollatzResearch.WordTrace tailWord_1773785 prefixEnd_1773785 101200475859494199081113 := by
  unfold tailWord_1773785
  simp only [CollatzResearch.WordTrace]
  refine ⟨64695253878887358204954809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43130169252591572136636539 64695253878887358204954809)
  ·
    refine ⟨48521440409165518653716107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64695253878887358204954809 48521440409165518653716107)
    ·
      refine ⟨72782160613748277980574161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48521440409165518653716107 72782160613748277980574161)
      ·
        refine ⟨54586620460311208485430621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72782160613748277980574161 54586620460311208485430621)
        ·
          refine ⟨20469982672616703182036483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54586620460311208485430621 20469982672616703182036483)
          ·
            refine ⟨30704974008925054773054725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20469982672616703182036483 30704974008925054773054725)
            ·
              refine ⟨5757182626673447769947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30704974008925054773054725 5757182626673447769947761)
              ·
                refine ⟨4317886970005085827460821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757182626673447769947761 4317886970005085827460821)
                ·
                  refine ⟨101200475859494199081113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4317886970005085827460821 101200475859494199081113)
                  ·
                    rfl

theorem cell23_1773785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_1773785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773785 prefixEnd_1773785 := by exact prefixLift 1773785
  have htrace : WordTrace (prefixWord ++ tailWord_1773785) baseStart_1773785 baseEnd_1773785 := by
    simpa [prefixWord, tailWord_1773785, baseEnd_1773785] using wordTrace_append hprefix tailTrace_1773785
  have hstable : (prefixWord ++ tailWord_1773785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773785).length < 2 ^ (prefixWord ++ tailWord_1773785).sum := by decide
  have hdescent : baseEnd_1773785 < baseStart_1773785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773845 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1773845 : Nat := 118140960795 + 1773845 * 2 ^ 59
def prefixEnd_1773845 : Nat := 4983230072969 + 3 ^ 40 * 1773845 * 2
def baseEnd_1773845 : Nat := 303611697191572518993247

theorem tailTrace_1773845 : CollatzResearch.WordTrace tailWord_1773845 prefixEnd_1773845 303611697191572518993247 := by
  unfold tailWord_1773845
  simp only [CollatzResearch.WordTrace]
  refine ⟨64697442258669988452138989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43131628172446658968092659 64697442258669988452138989)
  ·
    refine ⟨24261540847001245669552121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64697442258669988452138989 24261540847001245669552121)
    ·
      refine ⟨18196155635250934252164091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24261540847001245669552121 18196155635250934252164091)
      ·
        refine ⟨27294233452876401378246137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18196155635250934252164091 27294233452876401378246137)
        ·
          refine ⟨20470675089657301033684603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27294233452876401378246137 20470675089657301033684603)
          ·
            refine ⟨30706012634485951550526905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20470675089657301033684603 30706012634485951550526905)
            ·
              refine ⟨23029509475864463662895179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30706012634485951550526905 23029509475864463662895179)
              ·
                refine ⟨34544264213796695494342769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23029509475864463662895179 34544264213796695494342769)
                ·
                  refine ⟨25908198160347521620757077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34544264213796695494342769 25908198160347521620757077)
                  ·
                    refine ⟨303611697191572518993247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25908198160347521620757077 303611697191572518993247)
                    ·
                      rfl

theorem cell23_1773845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1773845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773845 prefixEnd_1773845 := by exact prefixLift 1773845
  have htrace : WordTrace (prefixWord ++ tailWord_1773845) baseStart_1773845 baseEnd_1773845 := by
    simpa [prefixWord, tailWord_1773845, baseEnd_1773845] using wordTrace_append hprefix tailTrace_1773845
  have hstable : (prefixWord ++ tailWord_1773845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773845).length < 2 ^ (prefixWord ++ tailWord_1773845).sum := by decide
  have hdescent : baseEnd_1773845 < baseStart_1773845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773870 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_1773870 : Nat := 118140960795 + 1773870 * 2 ^ 59
def prefixEnd_1773870 : Nat := 4983230072969 + 3 ^ 40 * 1773870 * 2
def baseEnd_1773870 : Nat := 101205325399008884351903

theorem tailTrace_1773870 : CollatzResearch.WordTrace tailWord_1773870 prefixEnd_1773870 101205325399008884351903 := by
  unfold tailWord_1773870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087294260447427215224883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43132236055719611814532709 8087294260447427215224883)
  ·
    refine ⟨12130941390671140822837325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8087294260447427215224883 12130941390671140822837325)
    ·
      refine ⟨4549103021501677808563997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12130941390671140822837325 4549103021501677808563997)
      ·
        refine ⟨1705913633063129178211499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4549103021501677808563997 1705913633063129178211499)
        ·
          refine ⟨2558870449594693767317249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705913633063129178211499 2558870449594693767317249)
          ·
            refine ⟨1919152837196020325487937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558870449594693767317249 1919152837196020325487937)
            ·
              refine ⟨1439364627897015244115953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919152837196020325487937 1439364627897015244115953)
              ·
                refine ⟨1079523470922761433086965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439364627897015244115953 1079523470922761433086965)
                ·
                  refine ⟨101205325399008884351903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1079523470922761433086965 101205325399008884351903)
                  ·
                    rfl

theorem cell23_1773870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_1773870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773870 prefixEnd_1773870 := by exact prefixLift 1773870
  have htrace : WordTrace (prefixWord ++ tailWord_1773870) baseStart_1773870 baseEnd_1773870 := by
    simpa [prefixWord, tailWord_1773870, baseEnd_1773870] using wordTrace_append hprefix tailTrace_1773870
  have hstable : (prefixWord ++ tailWord_1773870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773870).length < 2 ^ (prefixWord ++ tailWord_1773870).sum := by decide
  have hdescent : baseEnd_1773870 < baseStart_1773870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773872 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_1773872 : Nat := 118140960795 + 1773872 * 2 ^ 59
def prefixEnd_1773872 : Nat := 4983230072969 + 3 ^ 40 * 1773872 * 2
def baseEnd_1773872 : Nat := 910848955552388951342117

theorem tailTrace_1773872 : CollatzResearch.WordTrace tailWord_1773872 prefixEnd_1773872 910848955552388951342117 := by
  unfold tailWord_1773872
  simp only [CollatzResearch.WordTrace]
  refine ⟨32349213514786086031685935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43132284686381448042247913 32349213514786086031685935)
  ·
    refine ⟨48523820272179129047528903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32349213514786086031685935 48523820272179129047528903)
    ·
      refine ⟨72785730408268693571293355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48523820272179129047528903 72785730408268693571293355)
      ·
        refine ⟨109178595612403040356940033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72785730408268693571293355 109178595612403040356940033)
        ·
          refine ⟨81883946709302280267705025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109178595612403040356940033 81883946709302280267705025)
          ·
            refine ⟨61412960031976710200778769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81883946709302280267705025 61412960031976710200778769)
            ·
              refine ⟨46059720023982532650584077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61412960031976710200778769 46059720023982532650584077)
              ·
                refine ⟨17272395008993449743969029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46059720023982532650584077 17272395008993449743969029)
                ·
                  refine ⟨3238574064186271826994193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17272395008993449743969029 3238574064186271826994193)
                  ·
                    refine ⟨2428930548139703870245645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3238574064186271826994193 2428930548139703870245645)
                    ·
                      refine ⟨910848955552388951342117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428930548139703870245645 910848955552388951342117)
                      ·
                        rfl

theorem cell23_1773872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_1773872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773872 prefixEnd_1773872 := by exact prefixLift 1773872
  have htrace : WordTrace (prefixWord ++ tailWord_1773872) baseStart_1773872 baseEnd_1773872 := by
    simpa [prefixWord, tailWord_1773872, baseEnd_1773872] using wordTrace_append hprefix tailTrace_1773872
  have hstable : (prefixWord ++ tailWord_1773872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773872).length < 2 ^ (prefixWord ++ tailWord_1773872).sum := by decide
  have hdescent : baseEnd_1773872 < baseStart_1773872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773886 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1773886 : Nat := 118140960795 + 1773886 * 2 ^ 59
def prefixEnd_1773886 : Nat := 4983230072969 + 3 ^ 40 * 1773886 * 2
def baseEnd_1773886 : Nat := 910856144281551896567053

theorem tailTrace_1773886 : CollatzResearch.WordTrace tailWord_1773886 prefixEnd_1773886 910856144281551896567053 := by
  unfold tailWord_1773886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087367206440181556797689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43132625101014301636254341 8087367206440181556797689)
  ·
    refine ⟨6065525404830136167598267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8087367206440181556797689 6065525404830136167598267)
    ·
      refine ⟨9098288107245204251397401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065525404830136167598267 9098288107245204251397401)
      ·
        refine ⟨6823716080433903188548051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098288107245204251397401 6823716080433903188548051)
        ·
          refine ⟨10235574120650854782822077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6823716080433903188548051 10235574120650854782822077)
          ·
            refine ⟨3838340295244070543558279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10235574120650854782822077 3838340295244070543558279)
            ·
              refine ⟨5757510442866105815337419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838340295244070543558279 5757510442866105815337419)
              ·
                refine ⟨8636265664299158723006129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757510442866105815337419 8636265664299158723006129)
                ·
                  refine ⟨6477199248224369042254597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636265664299158723006129 6477199248224369042254597)
                  ·
                    refine ⟨1214474859042069195422737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6477199248224369042254597 1214474859042069195422737)
                    ·
                      refine ⟨910856144281551896567053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214474859042069195422737 910856144281551896567053)
                      ·
                        rfl

theorem cell23_1773886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1773886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773886 prefixEnd_1773886 := by exact prefixLift 1773886
  have htrace : WordTrace (prefixWord ++ tailWord_1773886) baseStart_1773886 baseEnd_1773886 := by
    simpa [prefixWord, tailWord_1773886, baseEnd_1773886] using wordTrace_append hprefix tailTrace_1773886
  have hstable : (prefixWord ++ tailWord_1773886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773886).length < 2 ^ (prefixWord ++ tailWord_1773886).sum := by decide
  have hdescent : baseEnd_1773886 < baseStart_1773886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773902 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1773902 : Nat := 118140960795 + 1773902 * 2 ^ 59
def prefixEnd_1773902 : Nat := 4983230072969 + 3 ^ 40 * 1773902 * 2
def baseEnd_1773902 : Nat := 910864359972023833966979

theorem tailTrace_1773902 : CollatzResearch.WordTrace tailWord_1773902 prefixEnd_1773902 910864359972023833966979 := by
  unfold tailWord_1773902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087440152432935898370495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43133014146308991457975973 8087440152432935898370495)
  ·
    refine ⟨12131160228649403847555743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8087440152432935898370495 12131160228649403847555743)
    ·
      refine ⟨18196740342974105771333615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12131160228649403847555743 18196740342974105771333615)
      ·
        refine ⟨27295110514461158657000423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18196740342974105771333615 27295110514461158657000423)
        ·
          refine ⟨40942665771691737985500635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27295110514461158657000423 40942665771691737985500635)
          ·
            refine ⟨61413998657537606978250953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40942665771691737985500635 61413998657537606978250953)
            ·
              refine ⟨46060498993153205233688215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61413998657537606978250953 46060498993153205233688215)
              ·
                refine ⟨69090748489729807850532323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46060498993153205233688215 69090748489729807850532323)
                ·
                  refine ⟨103636122734594711775798485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69090748489729807850532323 103636122734594711775798485)
                  ·
                    refine ⟨2428971626592063557245277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103636122734594711775798485 2428971626592063557245277)
                    ·
                      refine ⟨910864359972023833966979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2428971626592063557245277 910864359972023833966979)
                      ·
                        rfl

theorem cell23_1773902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1773902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773902 prefixEnd_1773902 := by exact prefixLift 1773902
  have htrace : WordTrace (prefixWord ++ tailWord_1773902) baseStart_1773902 baseEnd_1773902 := by
    simpa [prefixWord, tailWord_1773902, baseEnd_1773902] using wordTrace_append hprefix tailTrace_1773902
  have hstable : (prefixWord ++ tailWord_1773902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773902).length < 2 ^ (prefixWord ++ tailWord_1773902).sum := by decide
  have hdescent : baseEnd_1773902 < baseStart_1773902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773929 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 4, 3, 2]
def baseStart_1773929 : Nat := 118140960795 + 1773929 * 2 ^ 59
def prefixEnd_1773929 : Nat := 4983230072969 + 3 ^ 40 * 1773929 * 2
def baseEnd_1773929 : Nat := 910878223949695228329355

theorem tailTrace_1773929 : CollatzResearch.WordTrace tailWord_1773929 prefixEnd_1773929 910878223949695228329355 := by
  unfold tailWord_1773929
  simp only [CollatzResearch.WordTrace]
  refine ⟨64700505990365670798196841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43133670660243780532131227 64700505990365670798196841)
  ·
    refine ⟨48525379492774253098647631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64700505990365670798196841 48525379492774253098647631)
    ·
      refine ⟨72788069239161379647971447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48525379492774253098647631 72788069239161379647971447)
      ·
        refine ⟨109182103858742069471957171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72788069239161379647971447 109182103858742069471957171)
        ·
          refine ⟨163773155788113104207935757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109182103858742069471957171 163773155788113104207935757)
          ·
            refine ⟨61414933420542414077975909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163773155788113104207935757 61414933420542414077975909)
            ·
              refine ⟨11515300016351702639620483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61414933420542414077975909 11515300016351702639620483)
              ·
                refine ⟨17272950024527553959430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11515300016351702639620483 17272950024527553959430725)
                ·
                  refine ⟨3238678129598916367393261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17272950024527553959430725 3238678129598916367393261)
                  ·
                    refine ⟨1214504298599593637772473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238678129598916367393261 1214504298599593637772473)
                    ·
                      refine ⟨910878223949695228329355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214504298599593637772473 910878223949695228329355)
                      ·
                        rfl

theorem cell23_1773929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3, 2].length) (baseStart_1773929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773929 prefixEnd_1773929 := by exact prefixLift 1773929
  have htrace : WordTrace (prefixWord ++ tailWord_1773929) baseStart_1773929 baseEnd_1773929 := by
    simpa [prefixWord, tailWord_1773929, baseEnd_1773929] using wordTrace_append hprefix tailTrace_1773929
  have hstable : (prefixWord ++ tailWord_1773929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773929).length < 2 ^ (prefixWord ++ tailWord_1773929).sum := by decide
  have hdescent : baseEnd_1773929 < baseStart_1773929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773936 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_1773936 : Nat := 118140960795 + 1773936 * 2 ^ 59
def prefixEnd_1773936 : Nat := 4983230072969 + 3 ^ 40 * 1773936 * 2
def baseEnd_1773936 : Nat := 910881818314276700941823

theorem tailTrace_1773936 : CollatzResearch.WordTrace tailWord_1773936 prefixEnd_1773936 910881818314276700941823 := by
  unfold tailWord_1773936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32350380650670155496850831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43133840867560207329134441 32350380650670155496850831)
  ·
    refine ⟨48525570976005233245276247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32350380650670155496850831 48525570976005233245276247)
    ·
      refine ⟨72788356464007849867914371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48525570976005233245276247 72788356464007849867914371)
      ·
        refine ⟨109182534696011774801871557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72788356464007849867914371 109182534696011774801871557)
        ·
          refine ⟨20471725255502207775350917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109182534696011774801871557 20471725255502207775350917)
          ·
            refine ⟨3838448485406663957878297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20471725255502207775350917 3838448485406663957878297)
            ·
              refine ⟨2878836364054997968408723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838448485406663957878297 2878836364054997968408723)
              ·
                refine ⟨4318254546082496952613085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878836364054997968408723 4318254546082496952613085)
                ·
                  refine ⟨1619345454780936357229907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4318254546082496952613085 1619345454780936357229907)
                  ·
                    refine ⟨2429018182171404535844861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619345454780936357229907 2429018182171404535844861)
                    ·
                      refine ⟨910881818314276700941823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429018182171404535844861 910881818314276700941823)
                      ·
                        rfl

theorem cell23_1773936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_1773936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773936 prefixEnd_1773936 := by exact prefixLift 1773936
  have htrace : WordTrace (prefixWord ++ tailWord_1773936) baseStart_1773936 baseEnd_1773936 := by
    simpa [prefixWord, tailWord_1773936, baseEnd_1773936] using wordTrace_append hprefix tailTrace_1773936
  have hstable : (prefixWord ++ tailWord_1773936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773936).length < 2 ^ (prefixWord ++ tailWord_1773936).sum := by decide
  have hdescent : baseEnd_1773936 < baseStart_1773936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773959 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_1773959 : Nat := 118140960795 + 1773959 * 2 ^ 59
def prefixEnd_1773959 : Nat := 4983230072969 + 3 ^ 40 * 1773959 * 2
def baseEnd_1773959 : Nat := 910893628369330110954217

theorem tailTrace_1773959 : CollatzResearch.WordTrace tailWord_1773959 prefixEnd_1773959 910893628369330110954217 := by
  unfold tailWord_1773959
  simp only [CollatzResearch.WordTrace]
  refine ⟨64701600180256985921788931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43134400120171323947859287 64701600180256985921788931)
  ·
    refine ⟨97052400270385478882683397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64701600180256985921788931 97052400270385478882683397)
    ·
      refine ⟨18197325050697277290503137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97052400270385478882683397 18197325050697277290503137)
      ·
        refine ⟨13647993788022957967877353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18197325050697277290503137 13647993788022957967877353)
        ·
          refine ⟨10235995341017218475908015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13647993788022957967877353 10235995341017218475908015)
          ·
            refine ⟨15353993011525827713862023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235995341017218475908015 15353993011525827713862023)
            ·
              refine ⟨23030989517288741570793035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15353993011525827713862023 23030989517288741570793035)
              ·
                refine ⟨34546484275933112356189553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23030989517288741570793035 34546484275933112356189553)
                ·
                  refine ⟨25909863206949834267142165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34546484275933112356189553 25909863206949834267142165)
                  ·
                    refine ⟨1214524837825773481272289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25909863206949834267142165 1214524837825773481272289)
                    ·
                      refine ⟨910893628369330110954217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214524837825773481272289 910893628369330110954217)
                      ·
                        rfl

theorem cell23_1773959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_1773959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773959 prefixEnd_1773959 := by exact prefixLift 1773959
  have htrace : WordTrace (prefixWord ++ tailWord_1773959) baseStart_1773959 baseEnd_1773959 := by
    simpa [prefixWord, tailWord_1773959, baseEnd_1773959] using wordTrace_append hprefix tailTrace_1773959
  have hstable : (prefixWord ++ tailWord_1773959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773959).length < 2 ^ (prefixWord ++ tailWord_1773959).sum := by decide
  have hdescent : baseEnd_1773959 < baseStart_1773959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773976 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1773976 : Nat := 118140960795 + 1773976 * 2 ^ 59
def prefixEnd_1773976 : Nat := 4983230072969 + 3 ^ 40 * 1773976 * 2
def baseEnd_1773976 : Nat := 910902357540456544441639

theorem tailTrace_1773976 : CollatzResearch.WordTrace tailWord_1773976 prefixEnd_1773976 910902357540456544441639 := by
  unfold tailWord_1773976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32351110110597698912578891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43134813480796931883438521 32351110110597698912578891)
  ·
    refine ⟨48526665165896548368868337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32351110110597698912578891 48526665165896548368868337)
    ·
      refine ⟨36394998874422411276651253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48526665165896548368868337 36394998874422411276651253)
      ·
        refine ⟨3412031144477101057186055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36394998874422411276651253 3412031144477101057186055)
        ·
          refine ⟨5118046716715651585779083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412031144477101057186055 5118046716715651585779083)
          ·
            refine ⟨7677070075073477378668625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118046716715651585779083 7677070075073477378668625)
            ·
              refine ⟨5757802556305108034001469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677070075073477378668625 5757802556305108034001469)
              ·
                refine ⟨2159175958614415512750551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5757802556305108034001469 2159175958614415512750551)
                ·
                  refine ⟨3238763937921623269125827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159175958614415512750551 3238763937921623269125827)
                  ·
                    refine ⟨4858145906882434903688741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238763937921623269125827 4858145906882434903688741)
                    ·
                      refine ⟨910902357540456544441639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4858145906882434903688741 910902357540456544441639)
                      ·
                        rfl

theorem cell23_1773976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1773976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773976 prefixEnd_1773976 := by exact prefixLift 1773976
  have htrace : WordTrace (prefixWord ++ tailWord_1773976) baseStart_1773976 baseEnd_1773976 := by
    simpa [prefixWord, tailWord_1773976, baseEnd_1773976] using wordTrace_append hprefix tailTrace_1773976
  have hstable : (prefixWord ++ tailWord_1773976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773976).length < 2 ^ (prefixWord ++ tailWord_1773976).sum := by decide
  have hdescent : baseEnd_1773976 < baseStart_1773976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773986 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1773986 : Nat := 118140960795 + 1773986 * 2 ^ 59
def prefixEnd_1773986 : Nat := 4983230072969 + 3 ^ 40 * 1773986 * 2
def baseEnd_1773986 : Nat := 303635830782333835105531

theorem tailTrace_1773986 : CollatzResearch.WordTrace tailWord_1773986 prefixEnd_1773986 303635830782333835105531 := by
  unfold tailWord_1773986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175646237789792383255453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43135056634106113022014541 16175646237789792383255453)
  ·
    refine ⟨6065867339171172143720795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16175646237789792383255453 6065867339171172143720795)
    ·
      refine ⟨9098801008756758215581193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065867339171172143720795 9098801008756758215581193)
      ·
        refine ⟨6824100756567568661685895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098801008756758215581193 6824100756567568661685895)
        ·
          refine ⟨10236151134851352992528843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824100756567568661685895 10236151134851352992528843)
          ·
            refine ⟨15354226702277029488793265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236151134851352992528843 15354226702277029488793265)
            ·
              refine ⟨11515670026707772116594949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15354226702277029488793265 11515670026707772116594949)
              ·
                refine ⟨2159188130007707271861553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11515670026707772116594949 2159188130007707271861553)
                ·
                  refine ⟨1619391097505780453896165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159188130007707271861553 1619391097505780453896165)
                  ·
                    refine ⟨303635830782333835105531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619391097505780453896165 303635830782333835105531)
                    ·
                      rfl

theorem cell23_1773986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1773986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773986 prefixEnd_1773986 := by exact prefixLift 1773986
  have htrace : WordTrace (prefixWord ++ tailWord_1773986) baseStart_1773986 baseEnd_1773986 := by
    simpa [prefixWord, tailWord_1773986, baseEnd_1773986] using wordTrace_append hprefix tailTrace_1773986
  have hstable : (prefixWord ++ tailWord_1773986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773986).length < 2 ^ (prefixWord ++ tailWord_1773986).sum := by decide
  have hdescent : baseEnd_1773986 < baseStart_1773986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1773993 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 1, 2, 2]
def baseStart_1773993 : Nat := 118140960795 + 1773993 * 2 ^ 59
def prefixEnd_1773993 : Nat := 4983230072969 + 3 ^ 40 * 1773993 * 2
def baseEnd_1773993 : Nat := 910911086711582977929061

theorem tailTrace_1773993 : CollatzResearch.WordTrace tailWord_1773993 prefixEnd_1773993 910911086711582977929061 := by
  unfold tailWord_1773993
  simp only [CollatzResearch.WordTrace]
  refine ⟨64702840262133809728526633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43135226841422539819017755 64702840262133809728526633)
  ·
    refine ⟨48527130196600357296394975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64702840262133809728526633 48527130196600357296394975)
    ·
      refine ⟨72790695294900535944592463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48527130196600357296394975 72790695294900535944592463)
      ·
        refine ⟨109186042942350803916888695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72790695294900535944592463 109186042942350803916888695)
        ·
          refine ⟨163779064413526205875333043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109186042942350803916888695 163779064413526205875333043)
          ·
            refine ⟨245668596620289308812999565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163779064413526205875333043 245668596620289308812999565)
            ·
              refine ⟨92125723732608490804874837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245668596620289308812999565 92125723732608490804874837)
              ·
                refine ⟨1079598324991505751619627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 92125723732608490804874837 1079598324991505751619627)
                ·
                  refine ⟨1619397487487258627429441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079598324991505751619627 1619397487487258627429441)
                  ·
                    refine ⟨1214548115615443970572081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1619397487487258627429441 1214548115615443970572081)
                    ·
                      refine ⟨910911086711582977929061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214548115615443970572081 910911086711582977929061)
                      ·
                        rfl

theorem cell23_1773993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 2, 2].length) (baseStart_1773993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1773993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1773993 prefixEnd_1773993 := by exact prefixLift 1773993
  have htrace : WordTrace (prefixWord ++ tailWord_1773993) baseStart_1773993 baseEnd_1773993 := by
    simpa [prefixWord, tailWord_1773993, baseEnd_1773993] using wordTrace_append hprefix tailTrace_1773993
  have hstable : (prefixWord ++ tailWord_1773993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1773993).length < 2 ^ (prefixWord ++ tailWord_1773993).sum := by decide
  have hdescent : baseEnd_1773993 < baseStart_1773993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1773993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774002 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1774002 : Nat := 118140960795 + 1774002 * 2 ^ 59
def prefixEnd_1774002 : Nat := 4983230072969 + 3 ^ 40 * 1774002 * 2
def baseEnd_1774002 : Nat := 910915708037473442716519

theorem tailTrace_1774002 : CollatzResearch.WordTrace tailWord_1774002 prefixEnd_1774002 910915708037473442716519 := by
  unfold tailWord_1774002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175792129775301066401065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43135445679400802843736173 16175792129775301066401065)
  ·
    refine ⟨12131844097331475799800799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16175792129775301066401065 12131844097331475799800799)
    ·
      refine ⟨18197766145997213699701199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12131844097331475799800799 18197766145997213699701199)
      ·
        refine ⟨27296649218995820549551799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18197766145997213699701199 27296649218995820549551799)
        ·
          refine ⟨40944973828493730824327699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27296649218995820549551799 40944973828493730824327699)
          ·
            refine ⟨61417460742740596236491549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40944973828493730824327699 61417460742740596236491549)
            ·
              refine ⟨23031547778527723588684331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61417460742740596236491549 23031547778527723588684331)
              ·
                refine ⟨34547321667791585383026497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23031547778527723588684331 34547321667791585383026497)
                ·
                  refine ⟨25910491250843689037269873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34547321667791585383026497 25910491250843689037269873)
                  ·
                    refine ⟨19432868438132766777952405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25910491250843689037269873 19432868438132766777952405)
                    ·
                      refine ⟨910915708037473442716519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19432868438132766777952405 910915708037473442716519)
                      ·
                        rfl

theorem cell23_1774002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1774002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774002 prefixEnd_1774002 := by exact prefixLift 1774002
  have htrace : WordTrace (prefixWord ++ tailWord_1774002) baseStart_1774002 baseEnd_1774002 := by
    simpa [prefixWord, tailWord_1774002, baseEnd_1774002] using wordTrace_append hprefix tailTrace_1774002
  have hstable : (prefixWord ++ tailWord_1774002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774002).length < 2 ^ (prefixWord ++ tailWord_1774002).sum := by decide
  have hdescent : baseEnd_1774002 < baseStart_1774002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774013 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1774013 : Nat := 118140960795 + 1774013 * 2 ^ 59
def prefixEnd_1774013 : Nat := 4983230072969 + 3 ^ 40 * 1774013 * 2
def baseEnd_1774013 : Nat := 910921356324672899678969

theorem tailTrace_1774013 : CollatzResearch.WordTrace tailWord_1774013 prefixEnd_1774013 910921356324672899678969 := by
  unfold tailWord_1774013
  simp only [CollatzResearch.WordTrace]
  refine ⟨64703569722061353144254693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43135713148040902096169795 64703569722061353144254693)
  ·
    refine ⟨12131919322886503714547755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64703569722061353144254693 12131919322886503714547755)
    ·
      refine ⟨18197878984329755571821633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12131919322886503714547755 18197878984329755571821633)
      ·
        refine ⟨13648409238247316678866225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18197878984329755571821633 13648409238247316678866225)
        ·
          refine ⟨10236306928685487509149669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13648409238247316678866225 10236306928685487509149669)
          ·
            refine ⟨1919307549128528907965563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10236306928685487509149669 1919307549128528907965563)
            ·
              refine ⟨2878961323692793361948345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919307549128528907965563 2878961323692793361948345)
              ·
                refine ⟨2159220992769595021461259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878961323692793361948345 2159220992769595021461259)
                ·
                  refine ⟨3238831489154392532191889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159220992769595021461259 3238831489154392532191889)
                  ·
                    refine ⟨2429123616865794399143917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3238831489154392532191889 2429123616865794399143917)
                    ·
                      refine ⟨910921356324672899678969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429123616865794399143917 910921356324672899678969)
                      ·
                        rfl

theorem cell23_1774013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1774013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774013 prefixEnd_1774013 := by exact prefixLift 1774013
  have htrace : WordTrace (prefixWord ++ tailWord_1774013) baseStart_1774013 baseEnd_1774013 := by
    simpa [prefixWord, tailWord_1774013, baseEnd_1774013] using wordTrace_append hprefix tailTrace_1774013
  have hstable : (prefixWord ++ tailWord_1774013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774013).length < 2 ^ (prefixWord ++ tailWord_1774013).sum := by decide
  have hdescent : baseEnd_1774013 < baseStart_1774013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774032 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1774032 : Nat := 118140960795 + 1774032 * 2 ^ 59
def prefixEnd_1774032 : Nat := 4983230072969 + 3 ^ 40 * 1774032 * 2
def baseEnd_1774032 : Nat := 910931112457108325341381

theorem tailTrace_1774032 : CollatzResearch.WordTrace tailWord_1774032 prefixEnd_1774032 910931112457108325341381 := by
  unfold tailWord_1774032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352131354496259694598175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43136175139328346259464233 32352131354496259694598175)
  ·
    refine ⟨48528197031744389541897263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32352131354496259694598175 48528197031744389541897263)
    ·
      refine ⟨72792295547616584312845895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48528197031744389541897263 72792295547616584312845895)
      ·
        refine ⟨109188443321424876469268843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72792295547616584312845895 109188443321424876469268843)
        ·
          refine ⟨163782664982137314703903265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109188443321424876469268843 163782664982137314703903265)
          ·
            refine ⟨122836998736602986027927449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163782664982137314703903265 122836998736602986027927449)
            ·
              refine ⟨92127749052452239520945587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122836998736602986027927449 92127749052452239520945587)
              ·
                refine ⟨138191623578678359281418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92127749052452239520945587 138191623578678359281418381)
                ·
                  refine ⟨51821858842004384730531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138191623578678359281418381 51821858842004384730531893)
                  ·
                    refine ⟨4858299266437911068487365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51821858842004384730531893 4858299266437911068487365)
                    ·
                      refine ⟨910931112457108325341381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4858299266437911068487365 910931112457108325341381)
                      ·
                        rfl

theorem cell23_1774032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1774032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774032 prefixEnd_1774032 := by exact prefixLift 1774032
  have htrace : WordTrace (prefixWord ++ tailWord_1774032) baseStart_1774032 baseEnd_1774032 := by
    simpa [prefixWord, tailWord_1774032, baseEnd_1774032] using wordTrace_append hprefix tailTrace_1774032
  have hstable : (prefixWord ++ tailWord_1774032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774032).length < 2 ^ (prefixWord ++ tailWord_1774032).sum := by decide
  have hdescent : baseEnd_1774032 < baseStart_1774032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774050 : List Nat := [3, 3, 3, 2, 2, 1, 1, 8]
def baseStart_1774050 : Nat := 118140960795 + 1774050 * 2 ^ 59
def prefixEnd_1774050 : Nat := 4983230072969 + 3 ^ 40 * 1774050 * 2
def baseEnd_1774050 : Nat := 33738531670699602033937

theorem tailTrace_1774050 : CollatzResearch.WordTrace tailWord_1774050 prefixEnd_1774050 33738531670699602033937 := by
  unfold tailWord_1774050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176229805731827115837901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43136612815284872308901069 16176229805731827115837901)
  ·
    refine ⟨6066086177149435168439213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16176229805731827115837901 6066086177149435168439213)
    ·
      refine ⟨2274782316431038188164705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6066086177149435168439213 2274782316431038188164705)
      ·
        refine ⟨1706086737323278641123529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2274782316431038188164705 1706086737323278641123529)
        ·
          refine ⟨1279565052992458980842647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706086737323278641123529 1279565052992458980842647)
          ·
            refine ⟨1919347579488688471263971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279565052992458980842647 1919347579488688471263971)
            ·
              refine ⟨2879021369233032706895957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919347579488688471263971 2879021369233032706895957)
              ·
                refine ⟨33738531670699602033937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2879021369233032706895957 33738531670699602033937)
                ·
                  rfl

theorem cell23_1774050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_1774050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774050 prefixEnd_1774050 := by exact prefixLift 1774050
  have htrace : WordTrace (prefixWord ++ tailWord_1774050) baseStart_1774050 baseEnd_1774050 := by
    simpa [prefixWord, tailWord_1774050, baseEnd_1774050] using wordTrace_append hprefix tailTrace_1774050
  have hstable : (prefixWord ++ tailWord_1774050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774050).length < 2 ^ (prefixWord ++ tailWord_1774050).sum := by decide
  have hdescent : baseEnd_1774050 < baseStart_1774050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774087 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1774087 : Nat := 118140960795 + 1774087 * 2 ^ 59
def prefixEnd_1774087 : Nat := 4983230072969 + 3 ^ 40 * 1774087 * 2
def baseEnd_1774087 : Nat := 910959353893105610153629

theorem tailTrace_1774087 : CollatzResearch.WordTrace tailWord_1774087 prefixEnd_1774087 910959353893105610153629 := by
  unfold tailWord_1774087
  simp only [CollatzResearch.WordTrace]
  refine ⟨64706268723793263782448515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43137512482528842521632343 64706268723793263782448515)
  ·
    refine ⟨97059403085689895673672773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64706268723793263782448515 97059403085689895673672773)
    ·
      refine ⟨18198638078566855438813645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97059403085689895673672773 18198638078566855438813645)
      ·
        refine ⟨6824489279462570789555117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18198638078566855438813645 6824489279462570789555117)
        ·
          refine ⟨2559183479798464046083169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6824489279462570789555117 2559183479798464046083169)
          ·
            refine ⟨1919387609848848034562377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559183479798464046083169 1919387609848848034562377)
            ·
              refine ⟨1439540707386636025921783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919387609848848034562377 1439540707386636025921783)
              ·
                refine ⟨2159311061079954038882675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439540707386636025921783 2159311061079954038882675)
                ·
                  refine ⟨3238966591619931058324013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159311061079954038882675 3238966591619931058324013)
                  ·
                    refine ⟨1214612471857474146871505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3238966591619931058324013 1214612471857474146871505)
                    ·
                      refine ⟨910959353893105610153629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214612471857474146871505 910959353893105610153629)
                      ·
                        rfl

theorem cell23_1774087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1774087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774087 prefixEnd_1774087 := by exact prefixLift 1774087
  have htrace : WordTrace (prefixWord ++ tailWord_1774087) baseStart_1774087 baseEnd_1774087 := by
    simpa [prefixWord, tailWord_1774087, baseEnd_1774087] using wordTrace_append hprefix tailTrace_1774087
  have hstable : (prefixWord ++ tailWord_1774087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774087).length < 2 ^ (prefixWord ++ tailWord_1774087).sum := by decide
  have hdescent : baseEnd_1774087 < baseStart_1774087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774093 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1774093 : Nat := 118140960795 + 1774093 * 2 ^ 59
def prefixEnd_1774093 : Nat := 4983230072969 + 3 ^ 40 * 1774093 * 2
def baseEnd_1774093 : Nat := 303654144925677528892867

theorem tailTrace_1774093 : CollatzResearch.WordTrace tailWord_1774093 prefixEnd_1774093 303654144925677528892867 := by
  unfold tailWord_1774093
  simp only [CollatzResearch.WordTrace]
  refine ⟨64706487561771526807166933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43137658374514351204777955 64706487561771526807166933)
  ·
    refine ⟨1516558302229020159542975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64706487561771526807166933 1516558302229020159542975)
    ·
      refine ⟨2274837453343530239314463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516558302229020159542975 2274837453343530239314463)
      ·
        refine ⟨3412256180015295358971695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274837453343530239314463 3412256180015295358971695)
        ·
          refine ⟨5118384270022943038457543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412256180015295358971695 5118384270022943038457543)
          ·
            refine ⟨7677576405034414557686315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118384270022943038457543 7677576405034414557686315)
            ·
              refine ⟨11516364607551621836529473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677576405034414557686315 11516364607551621836529473)
              ·
                refine ⟨8637273455663716377397105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11516364607551621836529473 8637273455663716377397105)
                ·
                  refine ⟨6477955091747787283047829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637273455663716377397105 6477955091747787283047829)
                  ·
                    refine ⟨303654144925677528892867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6477955091747787283047829 303654144925677528892867)
                    ·
                      rfl

theorem cell23_1774093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1774093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774093 prefixEnd_1774093 := by exact prefixLift 1774093
  have htrace : WordTrace (prefixWord ++ tailWord_1774093) baseStart_1774093 baseEnd_1774093 := by
    simpa [prefixWord, tailWord_1774093, baseEnd_1774093] using wordTrace_append hprefix tailTrace_1774093
  have hstable : (prefixWord ++ tailWord_1774093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774093).length < 2 ^ (prefixWord ++ tailWord_1774093).sum := by decide
  have hdescent : baseEnd_1774093 < baseStart_1774093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774099 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3]
def baseStart_1774099 : Nat := 118140960795 + 1774099 * 2 ^ 59
def prefixEnd_1774099 : Nat := 4983230072969 + 3 ^ 40 * 1774099 * 2
def baseEnd_1774099 : Nat := 910965515660959563203573

theorem tailTrace_1774099 : CollatzResearch.WordTrace tailWord_1774099 prefixEnd_1774099 910965515660959563203573 := by
  unfold tailWord_1774099
  simp only [CollatzResearch.WordTrace]
  refine ⟨64706706399749789831885351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43137804266499859887923567 64706706399749789831885351)
  ·
    refine ⟨97060059599624684747828027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64706706399749789831885351 97060059599624684747828027)
    ·
      refine ⟨145590089399437027121742041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97060059599624684747828027 145590089399437027121742041)
      ·
        refine ⟨109192567049577770341306531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145590089399437027121742041 109192567049577770341306531)
        ·
          refine ⟨163788850574366655511959797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109192567049577770341306531 163788850574366655511959797)
          ·
            refine ⟨15355204741346873954246231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163788850574366655511959797 15355204741346873954246231)
            ·
              refine ⟨23032807112020310931369347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15355204741346873954246231 23032807112020310931369347)
              ·
                refine ⟨34549210668030466397054021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23032807112020310931369347 34549210668030466397054021)
                ·
                  refine ⟨6477977000255712449447629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34549210668030466397054021 6477977000255712449447629)
                  ·
                    refine ⟨2429241375095892168542861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6477977000255712449447629 2429241375095892168542861)
                    ·
                      refine ⟨910965515660959563203573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429241375095892168542861 910965515660959563203573)
                      ·
                        rfl

theorem cell23_1774099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_1774099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774099 prefixEnd_1774099 := by exact prefixLift 1774099
  have htrace : WordTrace (prefixWord ++ tailWord_1774099) baseStart_1774099 baseEnd_1774099 := by
    simpa [prefixWord, tailWord_1774099, baseEnd_1774099] using wordTrace_append hprefix tailTrace_1774099
  have hstable : (prefixWord ++ tailWord_1774099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774099).length < 2 ^ (prefixWord ++ tailWord_1774099).sum := by decide
  have hdescent : baseEnd_1774099 < baseStart_1774099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774106 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_1774106 : Nat := 118140960795 + 1774106 * 2 ^ 59
def prefixEnd_1774106 : Nat := 4983230072969 + 3 ^ 40 * 1774106 * 2
def baseEnd_1774106 : Nat := 101218790002837892868449

theorem tailTrace_1774106 : CollatzResearch.WordTrace tailWord_1774106 prefixEnd_1774106 101218790002837892868449 := by
  unfold tailWord_1774106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176740427681107506847543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43137974473816286684926781 16176740427681107506847543)
  ·
    refine ⟨24265110641521661260271315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16176740427681107506847543 24265110641521661260271315)
    ·
      refine ⟨36397665962282491890406973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24265110641521661260271315 36397665962282491890406973)
      ·
        refine ⟨13649124735855934458902615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36397665962282491890406973 13649124735855934458902615)
        ·
          refine ⟨20473687103783901688353923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649124735855934458902615 20473687103783901688353923)
          ·
            refine ⟨30710530655675852532530885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20473687103783901688353923 30710530655675852532530885)
            ·
              refine ⟨5758224497939222349849541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30710530655675852532530885 5758224497939222349849541)
              ·
                refine ⟨1079667093363604190596789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5758224497939222349849541 1079667093363604190596789)
                ·
                  refine ⟨101218790002837892868449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1079667093363604190596789 101218790002837892868449)
                  ·
                    rfl

theorem cell23_1774106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_1774106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774106 prefixEnd_1774106 := by exact prefixLift 1774106
  have htrace : WordTrace (prefixWord ++ tailWord_1774106) baseStart_1774106 baseEnd_1774106 := by
    simpa [prefixWord, tailWord_1774106, baseEnd_1774106] using wordTrace_append hprefix tailTrace_1774106
  have hstable : (prefixWord ++ tailWord_1774106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774106).length < 2 ^ (prefixWord ++ tailWord_1774106).sum := by decide
  have hdescent : baseEnd_1774106 < baseStart_1774106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774156 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1774156 : Nat := 118140960795 + 1774156 * 2 ^ 59
def prefixEnd_1774156 : Nat := 4983230072969 + 3 ^ 40 * 1774156 * 2
def baseEnd_1774156 : Nat := 910994784058265840190811

theorem tailTrace_1774156 : CollatzResearch.WordTrace tailWord_1774156 prefixEnd_1774156 910994784058265840190811 := by
  unfold tailWord_1774156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32354392680271644283355161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43139190240362192377806881 32354392680271644283355161)
  ·
    refine ⟨24265794510203733212516371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32354392680271644283355161 24265794510203733212516371)
    ·
      refine ⟨36398691765305599818774557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24265794510203733212516371 36398691765305599818774557)
      ·
        refine ⟨13649509411989599932040459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36398691765305599818774557 13649509411989599932040459)
        ·
          refine ⟨20474264117984399898060689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649509411989599932040459 20474264117984399898060689)
          ·
            refine ⟨15355698088488299923545517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20474264117984399898060689 15355698088488299923545517)
            ·
              refine ⟨5758386783183112471329569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15355698088488299923545517 5758386783183112471329569)
              ·
                refine ⟨4318790087387334353497177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758386783183112471329569 4318790087387334353497177)
                ·
                  refine ⟨3239092565540500765122883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318790087387334353497177 3239092565540500765122883)
                  ·
                    refine ⟨4858638848310751147684325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239092565540500765122883 4858638848310751147684325)
                    ·
                      refine ⟨910994784058265840190811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4858638848310751147684325 910994784058265840190811)
                      ·
                        rfl

theorem cell23_1774156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1774156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774156 prefixEnd_1774156 := by exact prefixLift 1774156
  have htrace : WordTrace (prefixWord ++ tailWord_1774156) baseStart_1774156 baseEnd_1774156 := by
    simpa [prefixWord, tailWord_1774156, baseEnd_1774156] using wordTrace_append hprefix tailTrace_1774156
  have hstable : (prefixWord ++ tailWord_1774156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774156).length < 2 ^ (prefixWord ++ tailWord_1774156).sum := by decide
  have hdescent : baseEnd_1774156 < baseStart_1774156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774240 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1774240 : Nat := 118140960795 + 1774240 * 2 ^ 59
def prefixEnd_1774240 : Nat := 4983230072969 + 3 ^ 40 * 1774240 * 2
def baseEnd_1774240 : Nat := 911037916433243511540425

theorem tailTrace_1774240 : CollatzResearch.WordTrace tailWord_1774240 prefixEnd_1774240 911037916433243511540425 := by
  unfold tailWord_1774240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32355924546119485456384087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43141232728159313941845449 32355924546119485456384087)
  ·
    refine ⟨48533886819179228184576131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32355924546119485456384087 48533886819179228184576131)
    ·
      refine ⟨72800830228768842276864197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48533886819179228184576131 72800830228768842276864197)
      ·
        refine ⟨13650155667894157926912037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72800830228768842276864197 13650155667894157926912037)
        ·
          refine ⟨2559404187730154611296007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13650155667894157926912037 2559404187730154611296007)
          ·
            refine ⟨3839106281595231916944011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559404187730154611296007 3839106281595231916944011)
            ·
              refine ⟨5758659422392847875416017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839106281595231916944011 5758659422392847875416017)
              ·
                refine ⟨4318994566794635906562013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758659422392847875416017 4318994566794635906562013)
                ·
                  refine ⟨1619622962547988464960755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4318994566794635906562013 1619622962547988464960755)
                  ·
                    refine ⟨2429434443821982697441133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619622962547988464960755 2429434443821982697441133)
                    ·
                      refine ⟨911037916433243511540425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429434443821982697441133 911037916433243511540425)
                      ·
                        rfl

theorem cell23_1774240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1774240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774240 prefixEnd_1774240 := by exact prefixLift 1774240
  have htrace : WordTrace (prefixWord ++ tailWord_1774240) baseStart_1774240 baseEnd_1774240 := by
    simpa [prefixWord, tailWord_1774240, baseEnd_1774240] using wordTrace_append hprefix tailTrace_1774240
  have hstable : (prefixWord ++ tailWord_1774240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774240).length < 2 ^ (prefixWord ++ tailWord_1774240).sum := by decide
  have hdescent : baseEnd_1774240 < baseStart_1774240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774256 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_1774256 : Nat := 118140960795 + 1774256 * 2 ^ 59
def prefixEnd_1774256 : Nat := 4983230072969 + 3 ^ 40 * 1774256 * 2
def baseEnd_1774256 : Nat := 303682044041238482980117

theorem tailTrace_1774256 : CollatzResearch.WordTrace tailWord_1774256 prefixEnd_1774256 303682044041238482980117 := by
  unfold tailWord_1774256
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356216330090502822675311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43141621773454003763567081 32356216330090502822675311)
  ·
    refine ⟨48534324495135754234012967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32356216330090502822675311 48534324495135754234012967)
    ·
      refine ⟨72801486742703631351019451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48534324495135754234012967 72801486742703631351019451)
      ·
        refine ⟨109202230114055447026529177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72801486742703631351019451 109202230114055447026529177)
        ·
          refine ⟨81901672585541585269896883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109202230114055447026529177 81901672585541585269896883)
          ·
            refine ⟨122852508878312377904845325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81901672585541585269896883 122852508878312377904845325)
            ·
              refine ⟨46069690829367141714316997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122852508878312377904845325 46069690829367141714316997)
              ·
                refine ⟨8638067030506339071434437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46069690829367141714316997 8638067030506339071434437)
                ·
                  refine ⟨1619637568219938575893957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8638067030506339071434437 1619637568219938575893957)
                  ·
                    refine ⟨303682044041238482980117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619637568219938575893957 303682044041238482980117)
                    ·
                      rfl

theorem cell23_1774256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_1774256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774256 prefixEnd_1774256 := by exact prefixLift 1774256
  have htrace : WordTrace (prefixWord ++ tailWord_1774256) baseStart_1774256 baseEnd_1774256 := by
    simpa [prefixWord, tailWord_1774256, baseEnd_1774256] using wordTrace_append hprefix tailTrace_1774256
  have hstable : (prefixWord ++ tailWord_1774256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774256).length < 2 ^ (prefixWord ++ tailWord_1774256).sum := by decide
  have hdescent : baseEnd_1774256 < baseStart_1774256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774266 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1774266 : Nat := 118140960795 + 1774266 * 2 ^ 59
def prefixEnd_1774266 : Nat := 4983230072969 + 3 ^ 40 * 1774266 * 2
def baseEnd_1774266 : Nat := 911051266930260409815305

theorem tailTrace_1774266 : CollatzResearch.WordTrace tailWord_1774266 prefixEnd_1774266 911051266930260409815305 := by
  unfold tailWord_1774266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16178199347536194338303663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43141864926763184902143101 16178199347536194338303663)
  ·
    refine ⟨24267299021304291507455495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16178199347536194338303663 24267299021304291507455495)
    ·
      refine ⟨36400948531956437261183243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24267299021304291507455495 36400948531956437261183243)
      ·
        refine ⟨54601422797934655891774865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36400948531956437261183243 54601422797934655891774865)
        ·
          refine ⟨40951067098450991918831149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54601422797934655891774865 40951067098450991918831149)
          ·
            refine ⟨15356650161919121969561681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40951067098450991918831149 15356650161919121969561681)
            ·
              refine ⟨11517487621439341477171261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15356650161919121969561681 11517487621439341477171261)
              ·
                refine ⟨4319057858039753053939223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11517487621439341477171261 4319057858039753053939223)
                ·
                  refine ⟨6478586787059629580908835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319057858039753053939223 6478586787059629580908835)
                  ·
                    refine ⟨9717880180589444371363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478586787059629580908835 9717880180589444371363253)
                    ·
                      refine ⟨911051266930260409815305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9717880180589444371363253 911051266930260409815305)
                      ·
                        rfl

theorem cell23_1774266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1774266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774266 prefixEnd_1774266 := by exact prefixLift 1774266
  have htrace : WordTrace (prefixWord ++ tailWord_1774266) baseStart_1774266 baseEnd_1774266 := by
    simpa [prefixWord, tailWord_1774266, baseEnd_1774266] using wordTrace_append hprefix tailTrace_1774266
  have hstable : (prefixWord ++ tailWord_1774266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774266).length < 2 ^ (prefixWord ++ tailWord_1774266).sum := by decide
  have hdescent : baseEnd_1774266 < baseStart_1774266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774280 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_1774280 : Nat := 118140960795 + 1774280 * 2 ^ 59
def prefixEnd_1774280 : Nat := 4983230072969 + 3 ^ 40 * 1774280 * 2
def baseEnd_1774280 : Nat := 911058455659423355040241

theorem tailTrace_1774280 : CollatzResearch.WordTrace tailWord_1774280 prefixEnd_1774280 911058455659423355040241 := by
  unfold tailWord_1774280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356654006047028872112147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43142205341396038496149529 32356654006047028872112147)
  ·
    refine ⟨48534981009070543308168221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32356654006047028872112147 48534981009070543308168221)
    ·
      refine ⟨18200617878401453740563083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48534981009070543308168221 18200617878401453740563083)
      ·
        refine ⟨27300926817602180610844625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18200617878401453740563083 27300926817602180610844625)
        ·
          refine ⟨20475695113201635458133469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27300926817602180610844625 20475695113201635458133469)
          ·
            refine ⟨7678385667450613296800051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20475695113201635458133469 7678385667450613296800051)
            ·
              refine ⟨11517578501175919945200077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678385667450613296800051 11517578501175919945200077)
              ·
                refine ⟨4319091937940969979450029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11517578501175919945200077 4319091937940969979450029)
                ·
                  refine ⟨1619659476727863742293761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4319091937940969979450029 1619659476727863742293761)
                  ·
                    refine ⟨1214744607545897806720321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1619659476727863742293761 1214744607545897806720321)
                    ·
                      refine ⟨911058455659423355040241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214744607545897806720321 911058455659423355040241)
                      ·
                        rfl

theorem cell23_1774280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_1774280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774280 prefixEnd_1774280 := by exact prefixLift 1774280
  have htrace : WordTrace (prefixWord ++ tailWord_1774280) baseStart_1774280 baseEnd_1774280 := by
    simpa [prefixWord, tailWord_1774280, baseEnd_1774280] using wordTrace_append hprefix tailTrace_1774280
  have hstable : (prefixWord ++ tailWord_1774280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774280).length < 2 ^ (prefixWord ++ tailWord_1774280).sum := by decide
  have hdescent : baseEnd_1774280 < baseStart_1774280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774290 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1774290 : Nat := 118140960795 + 1774290 * 2 ^ 59
def prefixEnd_1774290 : Nat := 4983230072969 + 3 ^ 40 * 1774290 * 2
def baseEnd_1774290 : Nat := 303687863488656105305065

theorem tailTrace_1774290 : CollatzResearch.WordTrace tailWord_1774290 prefixEnd_1774290 303687863488656105305065 := by
  unfold tailWord_1774290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16178418185514457363022081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43142448494705219634725549 16178418185514457363022081)
  ·
    refine ⟨12133813639135843022266561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16178418185514457363022081 12133813639135843022266561)
    ·
      refine ⟨9100360229351882266699921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12133813639135843022266561 9100360229351882266699921)
      ·
        refine ⟨6825270172013911700024941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100360229351882266699921 6825270172013911700024941)
        ·
          refine ⟨2559476314505216887509353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6825270172013911700024941 2559476314505216887509353)
          ·
            refine ⟨1919607235878912665632015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559476314505216887509353 1919607235878912665632015)
            ·
              refine ⟨2879410853818368998448023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919607235878912665632015 2879410853818368998448023)
              ·
                refine ⟨4319116280727553497672035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879410853818368998448023 4319116280727553497672035)
                ·
                  refine ⟨6478674421091330246508053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319116280727553497672035 6478674421091330246508053)
                  ·
                    refine ⟨303687863488656105305065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6478674421091330246508053 303687863488656105305065)
                    ·
                      rfl

theorem cell23_1774290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1774290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774290 prefixEnd_1774290 := by exact prefixLift 1774290
  have htrace : WordTrace (prefixWord ++ tailWord_1774290) baseStart_1774290 baseEnd_1774290 := by
    simpa [prefixWord, tailWord_1774290, baseEnd_1774290] using wordTrace_append hprefix tailTrace_1774290
  have hstable : (prefixWord ++ tailWord_1774290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774290).length < 2 ^ (prefixWord ++ tailWord_1774290).sum := by decide
  have hdescent : baseEnd_1774290 < baseStart_1774290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774303 : List Nat := [1, 1, 2, 3, 2, 5, 2, 7]
def baseStart_1774303 : Nat := 118140960795 + 1774303 * 2 ^ 59
def prefixEnd_1774303 : Nat := 4983230072969 + 3 ^ 40 * 1774303 * 2
def baseEnd_1774303 : Nat := 33743343174610250557505

theorem tailTrace_1774303 : CollatzResearch.WordTrace tailWord_1774303 prefixEnd_1774303 33743343174610250557505 := by
  unfold tailWord_1774303
  simp only [CollatzResearch.WordTrace]
  refine ⟨64714146891010732672311563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43142764594007155114874375 64714146891010732672311563)
  ·
    refine ⟨97071220336516099008467345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64714146891010732672311563 97071220336516099008467345)
    ·
      refine ⟨72803415252387074256350509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97071220336516099008467345 72803415252387074256350509)
      ·
        refine ⟨27301280719645152846131441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72803415252387074256350509 27301280719645152846131441)
        ·
          refine ⟨20475960539733864634598581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27301280719645152846131441 20475960539733864634598581)
          ·
            refine ⟨1919621300600049809493617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20475960539733864634598581 1919621300600049809493617)
            ·
              refine ⟨1439715975450037357120213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919621300600049809493617 1439715975450037357120213)
              ·
                refine ⟨33743343174610250557505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1439715975450037357120213 33743343174610250557505)
                ·
                  rfl

theorem cell23_1774303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 7].length) (baseStart_1774303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774303 prefixEnd_1774303 := by exact prefixLift 1774303
  have htrace : WordTrace (prefixWord ++ tailWord_1774303) baseStart_1774303 baseEnd_1774303 := by
    simpa [prefixWord, tailWord_1774303, baseEnd_1774303] using wordTrace_append hprefix tailTrace_1774303
  have hstable : (prefixWord ++ tailWord_1774303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774303).length < 2 ^ (prefixWord ++ tailWord_1774303).sum := by decide
  have hdescent : baseEnd_1774303 < baseStart_1774303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
