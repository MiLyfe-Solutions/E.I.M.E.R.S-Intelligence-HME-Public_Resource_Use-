import V185TrunkScan22Chunk163

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1465721 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_1465721 : Nat := 118140960795 + 1465721 * 2 ^ 59
def prefixEnd_1465721 : Nat := 4983230072969 + 3 ^ 40 * 1465721 * 2
def baseEnd_1465721 : Nat := 501746252259176729031185

theorem tailTrace_1465721 : CollatzResearch.WordTrace tailWord_1465721 prefixEnd_1465721 501746252259176729031185 := by
  unfold tailWord_1465721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53459236722950617062501017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35639491148633744708334011 53459236722950617062501017)
  ·
    refine ⟨40094427542212962796875763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53459236722950617062501017 40094427542212962796875763)
    ·
      refine ⟨60141641313319444195313645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40094427542212962796875763 60141641313319444195313645)
      ·
        refine ⟨22553115492494791573242617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60141641313319444195313645 22553115492494791573242617)
        ·
          refine ⟨16914836619371093679931963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22553115492494791573242617 16914836619371093679931963)
          ·
            refine ⟨25372254929056640519897945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16914836619371093679931963 25372254929056640519897945)
            ·
              refine ⟨19029191196792480389923459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25372254929056640519897945 19029191196792480389923459)
              ·
                refine ⟨28543786795188720584885189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19029191196792480389923459 28543786795188720584885189)
                ·
                  refine ⟨5351960024097885109665973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28543786795188720584885189 5351960024097885109665973)
                  ·
                    refine ⟨501746252259176729031185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5351960024097885109665973 501746252259176729031185)
                    ·
                      rfl

theorem cell22_1465721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_1465721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465721 prefixEnd_1465721 := by exact prefixLift 1465721
  have htrace : WordTrace (prefixWord ++ tailWord_1465721) baseStart_1465721 baseEnd_1465721 := by
    simpa [prefixWord, tailWord_1465721, baseEnd_1465721] using wordTrace_append hprefix tailTrace_1465721
  have hstable : (prefixWord ++ tailWord_1465721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465721).length < 2 ^ (prefixWord ++ tailWord_1465721).sum := by decide
  have hdescent : baseEnd_1465721 < baseStart_1465721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465751 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 8]
def baseStart_1465751 : Nat := 118140960795 + 1465751 * 2 ^ 59
def prefixEnd_1465751 : Nat := 4983230072969 + 3 ^ 40 * 1465751 * 2
def baseEnd_1465751 : Nat := 167252173957422216927031

theorem tailTrace_1465751 : CollatzResearch.WordTrace tailWord_1465751 prefixEnd_1465751 167252173957422216927031 := by
  unfold tailWord_1465751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53460330912841932186093107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35640220608561288124062071 53460330912841932186093107)
  ·
    refine ⟨80190496369262898279139661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53460330912841932186093107 80190496369262898279139661)
    ·
      refine ⟨30071436138473586854677373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80190496369262898279139661 30071436138473586854677373)
      ·
        refine ⟨11276788551927595070504015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30071436138473586854677373 11276788551927595070504015)
        ·
          refine ⟨16915182827891392605756023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11276788551927595070504015 16915182827891392605756023)
          ·
            refine ⟨25372774241837088908634035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16915182827891392605756023 25372774241837088908634035)
            ·
              refine ⟨38059161362755633362951053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25372774241837088908634035 38059161362755633362951053)
              ·
                refine ⟨14272185511033362511106645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38059161362755633362951053 14272185511033362511106645)
                ·
                  refine ⟨167252173957422216927031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14272185511033362511106645 167252173957422216927031)
                  ·
                    rfl

theorem cell22_1465751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_1465751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465751 prefixEnd_1465751 := by exact prefixLift 1465751
  have htrace : WordTrace (prefixWord ++ tailWord_1465751) baseStart_1465751 baseEnd_1465751 := by
    simpa [prefixWord, tailWord_1465751, baseEnd_1465751] using wordTrace_append hprefix tailTrace_1465751
  have hstable : (prefixWord ++ tailWord_1465751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465751).length < 2 ^ (prefixWord ++ tailWord_1465751).sum := by decide
  have hdescent : baseEnd_1465751 < baseStart_1465751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465753 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_1465753 : Nat := 118140960795 + 1465753 * 2 ^ 59
def prefixEnd_1465753 : Nat := 4983230072969 + 3 ^ 40 * 1465753 * 2
def baseEnd_1465753 : Nat := 501757206513139312231087

theorem tailTrace_1465753 : CollatzResearch.WordTrace tailWord_1465753 prefixEnd_1465753 501757206513139312231087 := by
  unfold tailWord_1465753
  simp only [CollatzResearch.WordTrace]
  refine ⟨53460403858834686527665913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35640269239223124351777275 53460403858834686527665913)
  ·
    refine ⟨40095302894126014895749435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53460403858834686527665913 40095302894126014895749435)
    ·
      refine ⟨60142954341189022343624153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40095302894126014895749435 60142954341189022343624153)
      ·
        refine ⟨45107215755891766757718115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60142954341189022343624153 45107215755891766757718115)
        ·
          refine ⟨67660823633837650136577173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45107215755891766757718115 67660823633837650136577173)
          ·
            refine ⟨3171601107836139850152055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67660823633837650136577173 3171601107836139850152055)
            ·
              refine ⟨4757401661754209775228083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171601107836139850152055 4757401661754209775228083)
              ·
                refine ⟨7136102492631314662842125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757401661754209775228083 7136102492631314662842125)
                ·
                  refine ⟨2676038434736742998565797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7136102492631314662842125 2676038434736742998565797)
                  ·
                    refine ⟨501757206513139312231087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676038434736742998565797 501757206513139312231087)
                    ·
                      rfl

theorem cell22_1465753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_1465753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465753 prefixEnd_1465753 := by exact prefixLift 1465753
  have htrace : WordTrace (prefixWord ++ tailWord_1465753) baseStart_1465753 baseEnd_1465753 := by
    simpa [prefixWord, tailWord_1465753, baseEnd_1465753] using wordTrace_append hprefix tailTrace_1465753
  have hstable : (prefixWord ++ tailWord_1465753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465753).length < 2 ^ (prefixWord ++ tailWord_1465753).sum := by decide
  have hdescent : baseEnd_1465753 < baseStart_1465753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465800 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1465800 : Nat := 118140960795 + 1465800 * 2 ^ 59
def prefixEnd_1465800 : Nat := 4983230072969 + 3 ^ 40 * 1465800 * 2
def baseEnd_1465800 : Nat := 501773295573646856305943

theorem tailTrace_1465800 : CollatzResearch.WordTrace tailWord_1465800 prefixEnd_1465800 501773295573646856305943 := by
  unfold tailWord_1465800
  simp only [CollatzResearch.WordTrace]
  refine ⟨26731059044832206777313427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35641412059776275703084569 26731059044832206777313427)
  ·
    refine ⟨40096588567248310165970141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26731059044832206777313427 40096588567248310165970141)
    ·
      refine ⟨15036220712718116312238803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40096588567248310165970141 15036220712718116312238803)
      ·
        refine ⟨22554331069077174468358205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15036220712718116312238803 22554331069077174468358205)
        ·
          refine ⟨8457874150903940425634327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22554331069077174468358205 8457874150903940425634327)
          ·
            refine ⟨12686811226355910638451491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457874150903940425634327 12686811226355910638451491)
            ·
              refine ⟨19030216839533865957677237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686811226355910638451491 19030216839533865957677237)
              ·
                refine ⟨1784082828706299933532241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19030216839533865957677237 1784082828706299933532241)
                ·
                  refine ⟨1338062121529724950149181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784082828706299933532241 1338062121529724950149181)
                  ·
                    refine ⟨501773295573646856305943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338062121529724950149181 501773295573646856305943)
                    ·
                      rfl

theorem cell22_1465800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1465800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465800 prefixEnd_1465800 := by exact prefixLift 1465800
  have htrace : WordTrace (prefixWord ++ tailWord_1465800) baseStart_1465800 baseEnd_1465800 := by
    simpa [prefixWord, tailWord_1465800, baseEnd_1465800] using wordTrace_append hprefix tailTrace_1465800
  have hstable : (prefixWord ++ tailWord_1465800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465800).length < 2 ^ (prefixWord ++ tailWord_1465800).sum := by decide
  have hdescent : baseEnd_1465800 < baseStart_1465800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465834 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1465834 : Nat := 118140960795 + 1465834 * 2 ^ 59
def prefixEnd_1465834 : Nat := 4983230072969 + 3 ^ 40 * 1465834 * 2
def baseEnd_1465834 : Nat := 501784934468482100955839

theorem tailTrace_1465834 : CollatzResearch.WordTrace tailWord_1465834 prefixEnd_1465834 501784934468482100955839 := by
  unfold tailWord_1465834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13365839542885309340341139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35642238781027491574243037 13365839542885309340341139)
  ·
    refine ⟨20048759314327964010511709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13365839542885309340341139 20048759314327964010511709)
    ·
      refine ⟨7518284742872986503941891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20048759314327964010511709 7518284742872986503941891)
      ·
        refine ⟨11277427114309479755912837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518284742872986503941891 11277427114309479755912837)
        ·
          refine ⟨2114517583933027454233657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11277427114309479755912837 2114517583933027454233657)
          ·
            refine ⟨1585888187949770590675243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114517583933027454233657 1585888187949770590675243)
            ·
              refine ⟨2378832281924655886012865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585888187949770590675243 2378832281924655886012865)
              ·
                refine ⟨1784124211443491914509649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378832281924655886012865 1784124211443491914509649)
                ·
                  refine ⟨1338093158582618935882237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784124211443491914509649 1338093158582618935882237)
                  ·
                    refine ⟨501784934468482100955839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338093158582618935882237 501784934468482100955839)
                    ·
                      rfl

theorem cell22_1465834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1465834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465834 prefixEnd_1465834 := by exact prefixLift 1465834
  have htrace : WordTrace (prefixWord ++ tailWord_1465834) baseStart_1465834 baseEnd_1465834 := by
    simpa [prefixWord, tailWord_1465834, baseEnd_1465834] using wordTrace_append hprefix tailTrace_1465834
  have hstable : (prefixWord ++ tailWord_1465834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465834).length < 2 ^ (prefixWord ++ tailWord_1465834).sum := by decide
  have hdescent : baseEnd_1465834 < baseStart_1465834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465896 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1465896 : Nat := 118140960795 + 1465896 * 2 ^ 59
def prefixEnd_1465896 : Nat := 4983230072969 + 3 ^ 40 * 1465896 * 2
def baseEnd_1465896 : Nat := 501806158335534605905649

theorem tailTrace_1465896 : CollatzResearch.WordTrace tailWord_1465896 prefixEnd_1465896 501806158335534605905649 := by
  unfold tailWord_1465896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26732809748658310975060771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35643746331544414633414361 26732809748658310975060771)
  ·
    refine ⟨40099214622987466462591157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26732809748658310975060771 40099214622987466462591157)
    ·
      refine ⟨3759301370905074980867921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40099214622987466462591157 3759301370905074980867921)
      ·
        refine ⟨2819476028178806235650941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3759301370905074980867921 2819476028178806235650941)
        ·
          refine ⟨1057303510567052338369103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2819476028178806235650941 1057303510567052338369103)
          ·
            refine ⟨1585955265850578507553655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057303510567052338369103 1585955265850578507553655)
            ·
              refine ⟨2378932898775867761330483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585955265850578507553655 2378932898775867761330483)
              ·
                refine ⟨3568399348163801641995725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378932898775867761330483 3568399348163801641995725)
                ·
                  refine ⟨1338149755561425615748397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3568399348163801641995725 1338149755561425615748397)
                  ·
                    refine ⟨501806158335534605905649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338149755561425615748397 501806158335534605905649)
                    ·
                      rfl

theorem cell22_1465896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1465896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465896 prefixEnd_1465896 := by exact prefixLift 1465896
  have htrace : WordTrace (prefixWord ++ tailWord_1465896) baseStart_1465896 baseEnd_1465896 := by
    simpa [prefixWord, tailWord_1465896, baseEnd_1465896] using wordTrace_append hprefix tailTrace_1465896
  have hstable : (prefixWord ++ tailWord_1465896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465896).length < 2 ^ (prefixWord ++ tailWord_1465896).sum := by decide
  have hdescent : baseEnd_1465896 < baseStart_1465896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466014 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1466014 : Nat := 118140960795 + 1466014 * 2 ^ 59
def prefixEnd_1466014 : Nat := 4983230072969 + 3 ^ 40 * 1466014 * 2
def baseEnd_1466014 : Nat := 501846552147021631455287

theorem tailTrace_1466014 : CollatzResearch.WordTrace tailWord_1466014 prefixEnd_1466014 501846552147021631455287 := by
  unfold tailWord_1466014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683740413861141012864637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35646615540592752068611397 6683740413861141012864637)
  ·
    refine ⟨2506402655197927879824239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6683740413861141012864637 2506402655197927879824239)
    ·
      refine ⟨3759603982796891819736359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506402655197927879824239 3759603982796891819736359)
      ·
        refine ⟨5639405974195337729604539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759603982796891819736359 5639405974195337729604539)
        ·
          refine ⟨8459108961293006594406809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639405974195337729604539 8459108961293006594406809)
          ·
            refine ⟨6344331720969754945805107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8459108961293006594406809 6344331720969754945805107)
            ·
              refine ⟨9516497581454632418707661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344331720969754945805107 9516497581454632418707661)
              ·
                refine ⟨3568686593045487157015373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9516497581454632418707661 3568686593045487157015373)
                ·
                  refine ⟨1338257472392057683880765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3568686593045487157015373 1338257472392057683880765)
                  ·
                    refine ⟨501846552147021631455287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338257472392057683880765 501846552147021631455287)
                    ·
                      rfl

theorem cell22_1466014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1466014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466014 prefixEnd_1466014 := by exact prefixLift 1466014
  have htrace : WordTrace (prefixWord ++ tailWord_1466014) baseStart_1466014 baseEnd_1466014 := by
    simpa [prefixWord, tailWord_1466014, baseEnd_1466014] using wordTrace_append hprefix tailTrace_1466014
  have hstable : (prefixWord ++ tailWord_1466014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466014).length < 2 ^ (prefixWord ++ tailWord_1466014).sum := by decide
  have hdescent : baseEnd_1466014 < baseStart_1466014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466040 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1466040 : Nat := 118140960795 + 1466040 * 2 ^ 59
def prefixEnd_1466040 : Nat := 4983230072969 + 3 ^ 40 * 1466040 * 2
def baseEnd_1466040 : Nat := 501855452478366230305207

theorem tailTrace_1466040 : CollatzResearch.WordTrace tailWord_1466040 prefixEnd_1466040 501855452478366230305207 := by
  unfold tailWord_1466040
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735435804397467271681787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35647247739196623028909049 26735435804397467271681787)
  ·
    refine ⟨40103153706596200907522681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26735435804397467271681787 40103153706596200907522681)
    ·
      refine ⟨30077365279947150680642011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40103153706596200907522681 30077365279947150680642011)
      ·
        refine ⟨45116047919920726020963017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30077365279947150680642011 45116047919920726020963017)
        ·
          refine ⟨33837035939940544515722263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45116047919920726020963017 33837035939940544515722263)
          ·
            refine ⟨50755553909910816773583395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33837035939940544515722263 50755553909910816773583395)
            ·
              refine ⟨76133330864866225160375093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50755553909910816773583395 76133330864866225160375093)
              ·
                refine ⟨7137499768581208608785165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76133330864866225160375093 7137499768581208608785165)
                ·
                  refine ⟨2676562413217953228294437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7137499768581208608785165 2676562413217953228294437)
                  ·
                    refine ⟨501855452478366230305207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676562413217953228294437 501855452478366230305207)
                    ·
                      rfl

theorem cell22_1466040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1466040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466040 prefixEnd_1466040 := by exact prefixLift 1466040
  have htrace : WordTrace (prefixWord ++ tailWord_1466040) baseStart_1466040 baseEnd_1466040 := by
    simpa [prefixWord, tailWord_1466040, baseEnd_1466040] using wordTrace_append hprefix tailTrace_1466040
  have hstable : (prefixWord ++ tailWord_1466040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466040).length < 2 ^ (prefixWord ++ tailWord_1466040).sum := by decide
  have hdescent : baseEnd_1466040 < baseStart_1466040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466149 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1466149 : Nat := 118140960795 + 1466149 * 2 ^ 59
def prefixEnd_1466149 : Nat := 4983230072969 + 3 ^ 40 * 1466149 * 2
def baseEnd_1466149 : Nat := 501892765405926279329873

theorem tailTrace_1466149 : CollatzResearch.WordTrace tailWord_1466149 prefixEnd_1466149 501892765405926279329873 := by
  unfold tailWord_1466149
  simp only [CollatzResearch.WordTrace]
  refine ⟨53474847165400046159081501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35649898110266697439387667 53474847165400046159081501)
  ·
    refine ⟨20053067687025017309655563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53474847165400046159081501 20053067687025017309655563)
    ·
      refine ⟨30079601530537525964483345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20053067687025017309655563 30079601530537525964483345)
      ·
        refine ⟨22559701147903144473362509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30079601530537525964483345 22559701147903144473362509)
        ·
          refine ⟨8459887930463679177510941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22559701147903144473362509 8459887930463679177510941)
          ·
            refine ⟨3172457973923879691566603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8459887930463679177510941 3172457973923879691566603)
            ·
              refine ⟨4758686960885819537349905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172457973923879691566603 4758686960885819537349905)
              ·
                refine ⟨3569015220664364653012429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758686960885819537349905 3569015220664364653012429)
                ·
                  refine ⟨1338380707749136744879661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3569015220664364653012429 1338380707749136744879661)
                  ·
                    refine ⟨501892765405926279329873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338380707749136744879661 501892765405926279329873)
                    ·
                      rfl

theorem cell22_1466149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1466149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466149 prefixEnd_1466149 := by exact prefixLift 1466149
  have htrace : WordTrace (prefixWord ++ tailWord_1466149) baseStart_1466149 baseEnd_1466149 := by
    simpa [prefixWord, tailWord_1466149, baseEnd_1466149] using wordTrace_append hprefix tailTrace_1466149
  have hstable : (prefixWord ++ tailWord_1466149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466149).length < 2 ^ (prefixWord ++ tailWord_1466149).sum := by decide
  have hdescent : baseEnd_1466149 < baseStart_1466149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466179 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 5]
def baseStart_1466179 : Nat := 118140960795 + 1466179 * 2 ^ 59
def prefixEnd_1466179 : Nat := 4983230072969 + 3 ^ 40 * 1466179 * 2
def baseEnd_1466179 : Nat := 167301011673005400359927

theorem tailTrace_1466179 : CollatzResearch.WordTrace tailWord_1466179 prefixEnd_1466179 167301011673005400359927 := by
  unfold tailWord_1466179
  simp only [CollatzResearch.WordTrace]
  refine ⟨53475941355291361282673591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35650627570194240855115727 53475941355291361282673591)
  ·
    refine ⟨80213912032937041924010387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53475941355291361282673591 80213912032937041924010387)
    ·
      refine ⟨120320868049405562886015581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80213912032937041924010387 120320868049405562886015581)
      ·
        refine ⟨45120325518527086082255843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120320868049405562886015581 45120325518527086082255843)
        ·
          refine ⟨67680488277790629123383765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45120325518527086082255843 67680488277790629123383765)
          ·
            refine ⟨1586261444010717870079307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67680488277790629123383765 1586261444010717870079307)
            ·
              refine ⟨2379392166016076805118961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586261444010717870079307 2379392166016076805118961)
              ·
                refine ⟨1784544124512057603839221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379392166016076805118961 1784544124512057603839221)
                ·
                  refine ⟨167301011673005400359927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1784544124512057603839221 167301011673005400359927)
                  ·
                    rfl

theorem cell22_1466179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].length) (baseStart_1466179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466179 prefixEnd_1466179 := by exact prefixLift 1466179
  have htrace : WordTrace (prefixWord ++ tailWord_1466179) baseStart_1466179 baseEnd_1466179 := by
    simpa [prefixWord, tailWord_1466179, baseEnd_1466179] using wordTrace_append hprefix tailTrace_1466179
  have hstable : (prefixWord ++ tailWord_1466179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466179).length < 2 ^ (prefixWord ++ tailWord_1466179).sum := by decide
  have hdescent : baseEnd_1466179 < baseStart_1466179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466196 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1466196 : Nat := 118140960795 + 1466196 * 2 ^ 59
def prefixEnd_1466196 : Nat := 4983230072969 + 3 ^ 40 * 1466196 * 2
def baseEnd_1466196 : Nat := 167302951488811274468243

theorem tailTrace_1466196 : CollatzResearch.WordTrace tailWord_1466196 prefixEnd_1466196 167302951488811274468243 := by
  unfold tailWord_1466196
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738280698114886593021221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35651040930819848790694961 26738280698114886593021221)
  ·
    refine ⟨5013427630896541236191479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26738280698114886593021221 5013427630896541236191479)
    ·
      refine ⟨7520141446344811854287219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013427630896541236191479 7520141446344811854287219)
      ·
        refine ⟨11280212169517217781430829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7520141446344811854287219 11280212169517217781430829)
        ·
          refine ⟨4230079563568956668036561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11280212169517217781430829 4230079563568956668036561)
          ·
            refine ⟨3172559672676717501027421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4230079563568956668036561 3172559672676717501027421)
            ·
              refine ⟨1189709877253769062885283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3172559672676717501027421 1189709877253769062885283)
              ·
                refine ⟨1784564815880653594327925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189709877253769062885283 1784564815880653594327925)
                ·
                  refine ⟨167302951488811274468243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1784564815880653594327925 167302951488811274468243)
                  ·
                    rfl

theorem cell22_1466196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1466196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466196 prefixEnd_1466196 := by exact prefixLift 1466196
  have htrace : WordTrace (prefixWord ++ tailWord_1466196) baseStart_1466196 baseEnd_1466196 := by
    simpa [prefixWord, tailWord_1466196, baseEnd_1466196] using wordTrace_append hprefix tailTrace_1466196
  have hstable : (prefixWord ++ tailWord_1466196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466196).length < 2 ^ (prefixWord ++ tailWord_1466196).sum := by decide
  have hdescent : baseEnd_1466196 < baseStart_1466196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466207 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 6]
def baseStart_1466207 : Nat := 118140960795 + 1466207 * 2 ^ 59
def prefixEnd_1466207 : Nat := 4983230072969 + 3 ^ 40 * 1466207 * 2
def baseEnd_1466207 : Nat := 167304206663744487126565

theorem tailTrace_1466207 : CollatzResearch.WordTrace tailWord_1466207 prefixEnd_1466207 167304206663744487126565 := by
  unfold tailWord_1466207
  simp only [CollatzResearch.WordTrace]
  refine ⟨53476962599189922064692875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35651308399459948043128583 53476962599189922064692875)
  ·
    refine ⟨80215443898784883097039313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53476962599189922064692875 80215443898784883097039313)
    ·
      refine ⟨60161582924088662322779485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80215443898784883097039313 60161582924088662322779485)
      ·
        refine ⟨22560593596533248371042307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60161582924088662322779485 22560593596533248371042307)
        ·
          refine ⟨33840890394799872556563461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560593596533248371042307 33840890394799872556563461)
          ·
            refine ⟨6345166949024976104355649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33840890394799872556563461 6345166949024976104355649)
            ·
              refine ⟨4758875211768732078266737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6345166949024976104355649 4758875211768732078266737)
              ·
                refine ⟨3569156408826549058700053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758875211768732078266737 3569156408826549058700053)
                ·
                  refine ⟨167304206663744487126565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3569156408826549058700053 167304206663744487126565)
                  ·
                    rfl

theorem cell22_1466207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_1466207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466207 prefixEnd_1466207 := by exact prefixLift 1466207
  have htrace : WordTrace (prefixWord ++ tailWord_1466207) baseStart_1466207 baseEnd_1466207 := by
    simpa [prefixWord, tailWord_1466207, baseEnd_1466207] using wordTrace_append hprefix tailTrace_1466207
  have hstable : (prefixWord ++ tailWord_1466207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466207).length < 2 ^ (prefixWord ++ tailWord_1466207).sum := by decide
  have hdescent : baseEnd_1466207 < baseStart_1466207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466209 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1466209 : Nat := 118140960795 + 1466209 * 2 ^ 59
def prefixEnd_1466209 : Nat := 4983230072969 + 3 ^ 40 * 1466209 * 2
def baseEnd_1466209 : Nat := 501913304632106122829689

theorem tailTrace_1466209 : CollatzResearch.WordTrace tailWord_1466209 prefixEnd_1466209 501913304632106122829689 := by
  unfold tailWord_1466209
  simp only [CollatzResearch.WordTrace]
  refine ⟨53477035545182676406265681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35651357030121784270843787 53477035545182676406265681)
  ·
    refine ⟨40107776658887007304699261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53477035545182676406265681 40107776658887007304699261)
    ·
      refine ⟨15040416247082627739262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40107776658887007304699261 15040416247082627739262223)
      ·
        refine ⟨22560624370623941608893335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040416247082627739262223 22560624370623941608893335)
        ·
          refine ⟨33840936555935912413340003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560624370623941608893335 33840936555935912413340003)
          ·
            refine ⟨50761404833903868620010005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33840936555935912413340003 50761404833903868620010005)
            ·
              refine ⟨2379440851589243841562969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50761404833903868620010005 2379440851589243841562969)
              ·
                refine ⟨1784580638691932881172227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379440851589243841562969 1784580638691932881172227)
                ·
                  refine ⟨2676870958037899321758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784580638691932881172227 2676870958037899321758341)
                  ·
                    refine ⟨501913304632106122829689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676870958037899321758341 501913304632106122829689)
                    ·
                      rfl

theorem cell22_1466209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1466209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466209 prefixEnd_1466209 := by exact prefixLift 1466209
  have htrace : WordTrace (prefixWord ++ tailWord_1466209) baseStart_1466209 baseEnd_1466209 := by
    simpa [prefixWord, tailWord_1466209, baseEnd_1466209] using wordTrace_append hprefix tailTrace_1466209
  have hstable : (prefixWord ++ tailWord_1466209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466209).length < 2 ^ (prefixWord ++ tailWord_1466209).sum := by decide
  have hdescent : baseEnd_1466209 < baseStart_1466209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466239 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 2, 3]
def baseStart_1466239 : Nat := 118140960795 + 1466239 * 2 ^ 59
def prefixEnd_1466239 : Nat := 4983230072969 + 3 ^ 40 * 1466239 * 2
def baseEnd_1466239 : Nat := 501923574245196044579597

theorem tailTrace_1466239 : CollatzResearch.WordTrace tailWord_1466239 prefixEnd_1466239 501923574245196044579597 := by
  unfold tailWord_1466239
  simp only [CollatzResearch.WordTrace]
  refine ⟨53478129735073991529857771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35652086490049327686571847 53478129735073991529857771)
  ·
    refine ⟨80217194602610987294786657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53478129735073991529857771 80217194602610987294786657)
    ·
      refine ⟨60162895951958240471089993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80217194602610987294786657 60162895951958240471089993)
      ·
        refine ⟨45122171963968680353317495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60162895951958240471089993 45122171963968680353317495)
        ·
          refine ⟨67683257945953020529976243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45122171963968680353317495 67683257945953020529976243)
          ·
            refine ⟨101524886918929530794964365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67683257945953020529976243 101524886918929530794964365)
            ·
              refine ⟨38071832594598574048111637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101524886918929530794964365 38071832594598574048111637)
              ·
                refine ⟨1784617152871808158505233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38071832594598574048111637 1784617152871808158505233)
                ·
                  refine ⟨1338462864653856118878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784617152871808158505233 1338462864653856118878925)
                  ·
                    refine ⟨501923574245196044579597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338462864653856118878925 501923574245196044579597)
                    ·
                      rfl

theorem cell22_1466239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_1466239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466239 prefixEnd_1466239 := by exact prefixLift 1466239
  have htrace : WordTrace (prefixWord ++ tailWord_1466239) baseStart_1466239 baseEnd_1466239 := by
    simpa [prefixWord, tailWord_1466239, baseEnd_1466239] using wordTrace_append hprefix tailTrace_1466239
  have hstable : (prefixWord ++ tailWord_1466239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466239).length < 2 ^ (prefixWord ++ tailWord_1466239).sum := by decide
  have hdescent : baseEnd_1466239 < baseStart_1466239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466271 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_1466271 : Nat := 118140960795 + 1466271 * 2 ^ 59
def prefixEnd_1466271 : Nat := 4983230072969 + 3 ^ 40 * 1466271 * 2
def baseEnd_1466271 : Nat := 501934528499158627779499

theorem tailTrace_1466271 : CollatzResearch.WordTrace tailWord_1466271 prefixEnd_1466271 501934528499158627779499 := by
  unfold tailWord_1466271
  simp only [CollatzResearch.WordTrace]
  refine ⟨53479296870958060995022667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35652864580638707330015111 53479296870958060995022667)
  ·
    refine ⟨80218945306437091492534001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53479296870958060995022667 80218945306437091492534001)
    ·
      refine ⟨60164208979827818619400501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80218945306437091492534001 60164208979827818619400501)
      ·
        refine ⟨5640394591858857995568797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60164208979827818619400501 5640394591858857995568797)
        ·
          refine ⟨2115147971947071748338299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5640394591858857995568797 2115147971947071748338299)
          ·
            refine ⟨3172721957920607622507449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115147971947071748338299 3172721957920607622507449)
            ·
              refine ⟨2379541468440455716880587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172721957920607622507449 2379541468440455716880587)
              ·
                refine ⟨3569312202660683575320881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379541468440455716880587 3569312202660683575320881)
                ·
                  refine ⟨2676984151995512681490661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569312202660683575320881 2676984151995512681490661)
                  ·
                    refine ⟨501934528499158627779499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676984151995512681490661 501934528499158627779499)
                    ·
                      rfl

theorem cell22_1466271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_1466271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466271 prefixEnd_1466271 := by exact prefixLift 1466271
  have htrace : WordTrace (prefixWord ++ tailWord_1466271) baseStart_1466271 baseEnd_1466271 := by
    simpa [prefixWord, tailWord_1466271, baseEnd_1466271] using wordTrace_append hprefix tailTrace_1466271
  have hstable : (prefixWord ++ tailWord_1466271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466271).length < 2 ^ (prefixWord ++ tailWord_1466271).sum := by decide
  have hdescent : baseEnd_1466271 < baseStart_1466271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466286 : List Nat := [4, 1, 5, 1, 11]
def baseStart_1466286 : Nat := 118140960795 + 1466286 * 2 ^ 59
def prefixEnd_1466286 : Nat := 4983230072969 + 3 ^ 40 * 1466286 * 2
def baseEnd_1466286 : Nat := 2065595322245693780471

theorem tailTrace_1466286 : CollatzResearch.WordTrace tailWord_1466286 prefixEnd_1466286 2065595322245693780471 := by
  unfold tailWord_1466286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684980495737964819602339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35653229310602479037879141 6684980495737964819602339)
  ·
    refine ⟨10027470743606947229403509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684980495737964819602339 10027470743606947229403509)
    ·
      refine ⟨940075382213151302756579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10027470743606947229403509 940075382213151302756579)
      ·
        refine ⟨1410113073319726954134869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940075382213151302756579 1410113073319726954134869)
        ·
          refine ⟨2065595322245693780471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1410113073319726954134869 2065595322245693780471)
          ·
            rfl

theorem cell22_1466286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 11].length) (baseStart_1466286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466286 prefixEnd_1466286 := by exact prefixLift 1466286
  have htrace : WordTrace (prefixWord ++ tailWord_1466286) baseStart_1466286 baseEnd_1466286 := by
    simpa [prefixWord, tailWord_1466286, baseEnd_1466286] using wordTrace_append hprefix tailTrace_1466286
  have hstable : (prefixWord ++ tailWord_1466286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466286).length < 2 ^ (prefixWord ++ tailWord_1466286).sum := by decide
  have hdescent : baseEnd_1466286 < baseStart_1466286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466292 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1466292 : Nat := 118140960795 + 1466292 * 2 ^ 59
def prefixEnd_1466292 : Nat := 4983230072969 + 3 ^ 40 * 1466292 * 2
def baseEnd_1466292 : Nat := 167313905742773857668145

theorem tailTrace_1466292 : CollatzResearch.WordTrace tailWord_1466292 prefixEnd_1466292 167313905742773857668145 := by
  unfold tailWord_1466292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26740031401940990790768565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35653375202587987721024753 26740031401940990790768565)
  ·
    refine ⟨2506877943931967886634553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26740031401940990790768565 2506877943931967886634553)
    ·
      refine ⟨1880158457948975914975915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2506877943931967886634553 1880158457948975914975915)
      ·
        refine ⟨2820237686923463872463873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880158457948975914975915 2820237686923463872463873)
        ·
          refine ⟨2115178265192597904347905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820237686923463872463873 2115178265192597904347905)
          ·
            refine ⟨1586383698894448428260929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115178265192597904347905 1586383698894448428260929)
            ·
              refine ⟨1189787774170836321195697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586383698894448428260929 1189787774170836321195697)
              ·
                refine ⟨892340830628127240896773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189787774170836321195697 892340830628127240896773)
                ·
                  refine ⟨167313905742773857668145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892340830628127240896773 167313905742773857668145)
                  ·
                    rfl

theorem cell22_1466292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1466292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466292 prefixEnd_1466292 := by exact prefixLift 1466292
  have htrace : WordTrace (prefixWord ++ tailWord_1466292) baseStart_1466292 baseEnd_1466292 := by
    simpa [prefixWord, tailWord_1466292, baseEnd_1466292] using wordTrace_append hprefix tailTrace_1466292
  have hstable : (prefixWord ++ tailWord_1466292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466292).length < 2 ^ (prefixWord ++ tailWord_1466292).sum := by decide
  have hdescent : baseEnd_1466292 < baseStart_1466292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466314 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1466314 : Nat := 118140960795 + 1466314 * 2 ^ 59
def prefixEnd_1466314 : Nat := 4983230072969 + 3 ^ 40 * 1466314 * 2
def baseEnd_1466314 : Nat := 167316416092640282984789

theorem tailTrace_1466314 : CollatzResearch.WordTrace tailWord_1466314 prefixEnd_1466314 167316416092640282984789 := by
  unfold tailWord_1466314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370216302450569834709499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35653910139868186225891997 13370216302450569834709499)
  ·
    refine ⟨20055324453675854752064249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370216302450569834709499 20055324453675854752064249)
    ·
      refine ⟨15041493340256891064048187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20055324453675854752064249 15041493340256891064048187)
      ·
        refine ⟨22562240010385336596072281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15041493340256891064048187 22562240010385336596072281)
        ·
          refine ⟨16921680007789002447054211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22562240010385336596072281 16921680007789002447054211)
          ·
            refine ⟨25382520011683503670581317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16921680007789002447054211 25382520011683503670581317)
            ·
              refine ⟨4759222502190656938233997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25382520011683503670581317 4759222502190656938233997)
              ·
                refine ⟨1784708438321496351837749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4759222502190656938233997 1784708438321496351837749)
                ·
                  refine ⟨167316416092640282984789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1784708438321496351837749 167316416092640282984789)
                  ·
                    rfl

theorem cell22_1466314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1466314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466314 prefixEnd_1466314 := by exact prefixLift 1466314
  have htrace : WordTrace (prefixWord ++ tailWord_1466314) baseStart_1466314 baseEnd_1466314 := by
    simpa [prefixWord, tailWord_1466314, baseEnd_1466314] using wordTrace_append hprefix tailTrace_1466314
  have hstable : (prefixWord ++ tailWord_1466314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466314).length < 2 ^ (prefixWord ++ tailWord_1466314).sum := by decide
  have hdescent : baseEnd_1466314 < baseStart_1466314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466378 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1466378 : Nat := 118140960795 + 1466378 * 2 ^ 59
def prefixEnd_1466378 : Nat := 4983230072969 + 3 ^ 40 * 1466378 * 2
def baseEnd_1466378 : Nat := 501971156785846015354171

theorem tailTrace_1466378 : CollatzResearch.WordTrace tailWord_1466378 prefixEnd_1466378 501971156785846015354171 := by
  unfold tailWord_1466378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370799870392604567291947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35655466321046945512778525 13370799870392604567291947)
  ·
    refine ⟨20056199805588906850937921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370799870392604567291947 20056199805588906850937921)
    ·
      refine ⟨15042149854191680138203441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20056199805588906850937921 15042149854191680138203441)
      ·
        refine ⟨11281612390643760103652581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15042149854191680138203441 11281612390643760103652581)
        ·
          refine ⟨2115302323245705019434859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11281612390643760103652581 2115302323245705019434859)
          ·
            refine ⟨3172953484868557529152289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115302323245705019434859 3172953484868557529152289)
            ·
              refine ⟨2379715113651418146864217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172953484868557529152289 2379715113651418146864217)
              ·
                refine ⟨1784786335238563610148163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379715113651418146864217 1784786335238563610148163)
                ·
                  refine ⟨2677179502857845415222245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784786335238563610148163 2677179502857845415222245)
                  ·
                    refine ⟨501971156785846015354171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677179502857845415222245 501971156785846015354171)
                    ·
                      rfl

theorem cell22_1466378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1466378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466378 prefixEnd_1466378 := by exact prefixLift 1466378
  have htrace : WordTrace (prefixWord ++ tailWord_1466378) baseStart_1466378 baseEnd_1466378 := by
    simpa [prefixWord, tailWord_1466378, baseEnd_1466378] using wordTrace_append hprefix tailTrace_1466378
  have hstable : (prefixWord ++ tailWord_1466378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466378).length < 2 ^ (prefixWord ++ tailWord_1466378).sum := by decide
  have hdescent : baseEnd_1466378 < baseStart_1466378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466410 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_1466410 : Nat := 118140960795 + 1466410 * 2 ^ 59
def prefixEnd_1466410 : Nat := 4983230072969 + 3 ^ 40 * 1466410 * 2
def baseEnd_1466410 : Nat := 167327370346602866184691

theorem tailTrace_1466410 : CollatzResearch.WordTrace tailWord_1466410 prefixEnd_1466410 167327370346602866184691 := by
  unfold tailWord_1466410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371091654363621933583171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35656244411636325156221789 13371091654363621933583171)
  ·
    refine ⟨20056637481545432900374757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371091654363621933583171 20056637481545432900374757)
    ·
      refine ⟨3760619527789768668820267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20056637481545432900374757 3760619527789768668820267)
      ·
        refine ⟨5640929291684653003230401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760619527789768668820267 5640929291684653003230401)
        ·
          refine ⟨4230696968763489752422801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640929291684653003230401 4230696968763489752422801)
          ·
            refine ⟨3173022726572617314317101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4230696968763489752422801 3173022726572617314317101)
            ·
              refine ⟨1189883522464731492868913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3173022726572617314317101 1189883522464731492868913)
              ·
                refine ⟨892412641848548619651685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189883522464731492868913 892412641848548619651685)
                ·
                  refine ⟨167327370346602866184691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892412641848548619651685 167327370346602866184691)
                  ·
                    rfl

theorem cell22_1466410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_1466410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466410 prefixEnd_1466410 := by exact prefixLift 1466410
  have htrace : WordTrace (prefixWord ++ tailWord_1466410) baseStart_1466410 baseEnd_1466410 := by
    simpa [prefixWord, tailWord_1466410, baseEnd_1466410] using wordTrace_append hprefix tailTrace_1466410
  have hstable : (prefixWord ++ tailWord_1466410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466410).length < 2 ^ (prefixWord ++ tailWord_1466410).sum := by decide
  have hdescent : baseEnd_1466410 < baseStart_1466410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466496 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_1466496 : Nat := 118140960795 + 1466496 * 2 ^ 59
def prefixEnd_1466496 : Nat := 4983230072969 + 3 ^ 40 * 1466496 * 2
def baseEnd_1466496 : Nat := 502011550597333040903809

theorem tailTrace_1466496 : CollatzResearch.WordTrace tailWord_1466496 prefixEnd_1466496 502011550597333040903809 := by
  unfold tailWord_1466496
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743751647571462210981671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35658335530095282947975561 26743751647571462210981671)
  ·
    refine ⟨40115627471357193316472507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26743751647571462210981671 40115627471357193316472507)
    ·
      refine ⟨60173441207035789974708761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40115627471357193316472507 60173441207035789974708761)
      ·
        refine ⟨45130080905276842481031571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60173441207035789974708761 45130080905276842481031571)
        ·
          refine ⟨67695121357915263721547357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45130080905276842481031571 67695121357915263721547357)
          ·
            refine ⟨25385670509218223895580259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67695121357915263721547357 25385670509218223895580259)
            ·
              refine ⟨38078505763827335843370389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385670509218223895580259 38078505763827335843370389)
              ·
                refine ⟨1784929957679406367657987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38078505763827335843370389 1784929957679406367657987)
                ·
                  refine ⟨2677394936519109551486981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784929957679406367657987 2677394936519109551486981)
                  ·
                    refine ⟨502011550597333040903809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677394936519109551486981 502011550597333040903809)
                    ·
                      rfl

theorem cell22_1466496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_1466496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466496 prefixEnd_1466496 := by exact prefixLift 1466496
  have htrace : WordTrace (prefixWord ++ tailWord_1466496) baseStart_1466496 baseEnd_1466496 := by
    simpa [prefixWord, tailWord_1466496, baseEnd_1466496] using wordTrace_append hprefix tailTrace_1466496
  have hstable : (prefixWord ++ tailWord_1466496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466496).length < 2 ^ (prefixWord ++ tailWord_1466496).sum := by decide
  have hdescent : baseEnd_1466496 < baseStart_1466496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466528 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_1466528 : Nat := 118140960795 + 1466528 * 2 ^ 59
def prefixEnd_1466528 : Nat := 4983230072969 + 3 ^ 40 * 1466528 * 2
def baseEnd_1466528 : Nat := 167340834950431874701237

theorem tailTrace_1466528 : CollatzResearch.WordTrace tailWord_1466528 prefixEnd_1466528 167340834950431874701237 := by
  unfold tailWord_1466528
  simp only [CollatzResearch.WordTrace]
  refine ⟨26744335215513496943564119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35659113620684662591418825 26744335215513496943564119)
  ·
    refine ⟨40116502823270245415346179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26744335215513496943564119 40116502823270245415346179)
    ·
      refine ⟨60174754234905368123019269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40116502823270245415346179 60174754234905368123019269)
      ·
        refine ⟨11282766419044756523066113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60174754234905368123019269 11282766419044756523066113)
        ·
          refine ⟨8462074814283567392299585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11282766419044756523066113 8462074814283567392299585)
          ·
            refine ⟨6346556110712675544224689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8462074814283567392299585 6346556110712675544224689)
            ·
              refine ⟨4759917083034506658168517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346556110712675544224689 4759917083034506658168517)
              ·
                refine ⟨892484453068969998406597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4759917083034506658168517 892484453068969998406597)
                ·
                  refine ⟨167340834950431874701237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892484453068969998406597 167340834950431874701237)
                  ·
                    rfl

theorem cell22_1466528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_1466528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466528 prefixEnd_1466528 := by exact prefixLift 1466528
  have htrace : WordTrace (prefixWord ++ tailWord_1466528) baseStart_1466528 baseEnd_1466528 := by
    simpa [prefixWord, tailWord_1466528, baseEnd_1466528] using wordTrace_append hprefix tailTrace_1466528
  have hstable : (prefixWord ++ tailWord_1466528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466528).length < 2 ^ (prefixWord ++ tailWord_1466528).sum := by decide
  have hdescent : baseEnd_1466528 < baseStart_1466528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466601 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 5]
def baseStart_1466601 : Nat := 118140960795 + 1466601 * 2 ^ 59
def prefixEnd_1466601 : Nat := 4983230072969 + 3 ^ 40 * 1466601 * 2
def baseEnd_1466601 : Nat := 167349164747715922342829

theorem tailTrace_1466601 : CollatzResearch.WordTrace tailWord_1466601 prefixEnd_1466601 167349164747715922342829 := by
  unfold tailWord_1466601
  simp only [CollatzResearch.WordTrace]
  refine ⟨53491332959762527354535657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35660888639841684903023771 53491332959762527354535657)
  ·
    refine ⟨40118499719821895515901743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53491332959762527354535657 40118499719821895515901743)
    ·
      refine ⟨60177749579732843273852615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40118499719821895515901743 60177749579732843273852615)
      ·
        refine ⟨90266624369599264910778923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60177749579732843273852615 90266624369599264910778923)
        ·
          refine ⟨135399936554398897366168385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90266624369599264910778923 135399936554398897366168385)
          ·
            refine ⟨101549952415799173024626289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135399936554398897366168385 101549952415799173024626289)
            ·
              refine ⟨76162464311849379768469717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101549952415799173024626289 76162464311849379768469717)
              ·
                refine ⟨1785057757308969838323509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76162464311849379768469717 1785057757308969838323509)
                ·
                  refine ⟨167349164747715922342829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1785057757308969838323509 167349164747715922342829)
                  ·
                    rfl

theorem cell22_1466601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_1466601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466601 prefixEnd_1466601 := by exact prefixLift 1466601
  have htrace : WordTrace (prefixWord ++ tailWord_1466601) baseStart_1466601 baseEnd_1466601 := by
    simpa [prefixWord, tailWord_1466601, baseEnd_1466601] using wordTrace_append hprefix tailTrace_1466601
  have hstable : (prefixWord ++ tailWord_1466601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466601).length < 2 ^ (prefixWord ++ tailWord_1466601).sum := by decide
  have hdescent : baseEnd_1466601 < baseStart_1466601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466622 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1466622 : Nat := 118140960795 + 1466622 * 2 ^ 59
def prefixEnd_1466622 : Nat := 4983230072969 + 3 ^ 40 * 1466622 * 2
def baseEnd_1466622 : Nat := 502054682972310712253423

theorem tailTrace_1466622 : CollatzResearch.WordTrace tailWord_1466622 prefixEnd_1466622 502054682972310712253423 := by
  unfold tailWord_1466622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686512361585805992631265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35661399261790965294033413 6686512361585805992631265)
  ·
    refine ⟨5014884271189354494473449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6686512361585805992631265 5014884271189354494473449)
    ·
      refine ⟨3761163203392015870855087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5014884271189354494473449 3761163203392015870855087)
      ·
        refine ⟨5641744805088023806282631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761163203392015870855087 5641744805088023806282631)
        ·
          refine ⟨8462617207632035709423947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641744805088023806282631 8462617207632035709423947)
          ·
            refine ⟨12693925811448053564135921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462617207632035709423947 12693925811448053564135921)
            ·
              refine ⟨9520444358586040173101941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12693925811448053564135921 9520444358586040173101941)
              ·
                refine ⟨892541658617441266228307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9520444358586040173101941 892541658617441266228307)
                ·
                  refine ⟨1338812487926161899342461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892541658617441266228307 1338812487926161899342461)
                  ·
                    refine ⟨502054682972310712253423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338812487926161899342461 502054682972310712253423)
                    ·
                      rfl

theorem cell22_1466622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1466622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466622 prefixEnd_1466622 := by exact prefixLift 1466622
  have htrace : WordTrace (prefixWord ++ tailWord_1466622) baseStart_1466622 baseEnd_1466622 := by
    simpa [prefixWord, tailWord_1466622, baseEnd_1466622] using wordTrace_append hprefix tailTrace_1466622
  have hstable : (prefixWord ++ tailWord_1466622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466622).length < 2 ^ (prefixWord ++ tailWord_1466622).sum := by decide
  have hdescent : baseEnd_1466622 < baseStart_1466622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466682 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_1466682 : Nat := 118140960795 + 1466682 * 2 ^ 59
def prefixEnd_1466682 : Nat := 4983230072969 + 3 ^ 40 * 1466682 * 2
def baseEnd_1466682 : Nat := 502075222198490555753239

theorem tailTrace_1466682 : CollatzResearch.WordTrace tailWord_1466682 prefixEnd_1466682 502075222198490555753239 := by
  unfold tailWord_1466682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13373571818117269547058575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35662858181646052125489533 13373571818117269547058575)
  ·
    refine ⟨20060357727175904320587863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13373571818117269547058575 20060357727175904320587863)
    ·
      refine ⟨30090536590763856480881795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20060357727175904320587863 30090536590763856480881795)
      ·
        refine ⟨45135804886145784721322693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30090536590763856480881795 45135804886145784721322693)
        ·
          refine ⟨8462963416152334635248005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45135804886145784721322693 8462963416152334635248005)
          ·
            refine ⟨1586805640528562744109001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8462963416152334635248005 1586805640528562744109001)
            ·
              refine ⟨1190104230396422058081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586805640528562744109001 1190104230396422058081751)
              ·
                refine ⟨1785156345594633087122627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190104230396422058081751 1785156345594633087122627)
                ·
                  refine ⟨2677734518391949630683941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785156345594633087122627 2677734518391949630683941)
                  ·
                    refine ⟨502075222198490555753239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677734518391949630683941 502075222198490555753239)
                    ·
                      rfl

theorem cell22_1466682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_1466682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466682 prefixEnd_1466682 := by exact prefixLift 1466682
  have htrace : WordTrace (prefixWord ++ tailWord_1466682) baseStart_1466682 baseEnd_1466682 := by
    simpa [prefixWord, tailWord_1466682, baseEnd_1466682] using wordTrace_append hprefix tailTrace_1466682
  have hstable : (prefixWord ++ tailWord_1466682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466682).length < 2 ^ (prefixWord ++ tailWord_1466682).sum := by decide
  have hdescent : baseEnd_1466682 < baseStart_1466682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466725 : List Nat := [1, 3, 1, 3, 1, 5, 2, 6]
def baseStart_1466725 : Nat := 118140960795 + 1466725 * 2 ^ 59
def prefixEnd_1466725 : Nat := 4983230072969 + 3 ^ 40 * 1466725 * 2
def baseEnd_1466725 : Nat := 55787771330805864103123

theorem tailTrace_1466725 : CollatzResearch.WordTrace tailWord_1466725 prefixEnd_1466725 55787771330805864103123 := by
  unfold tailWord_1466725
  simp only [CollatzResearch.WordTrace]
  refine ⟨53495855611313296532049629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35663903740875531021366419 53495855611313296532049629)
  ·
    refine ⟨20060945854242486199518611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53495855611313296532049629 20060945854242486199518611)
    ·
      refine ⟨30091418781363729299277917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20060945854242486199518611 30091418781363729299277917)
      ·
        refine ⟨11284282043011398487229219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30091418781363729299277917 11284282043011398487229219)
        ·
          refine ⟨16926423064517097730843829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11284282043011398487229219 16926423064517097730843829)
          ·
            refine ⟨1586852162298477912266609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16926423064517097730843829 1586852162298477912266609)
            ·
              refine ⟨1190139121723858434199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586852162298477912266609 1190139121723858434199957)
              ·
                refine ⟨55787771330805864103123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1190139121723858434199957 55787771330805864103123)
                ·
                  rfl

theorem cell22_1466725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 6].length) (baseStart_1466725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466725 prefixEnd_1466725 := by exact prefixLift 1466725
  have htrace : WordTrace (prefixWord ++ tailWord_1466725) baseStart_1466725 baseEnd_1466725 := by
    simpa [prefixWord, tailWord_1466725, baseEnd_1466725] using wordTrace_append hprefix tailTrace_1466725
  have hstable : (prefixWord ++ tailWord_1466725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466725).length < 2 ^ (prefixWord ++ tailWord_1466725).sum := by decide
  have hdescent : baseEnd_1466725 < baseStart_1466725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466742 : List Nat := [5, 1, 1, 4, 1, 2, 8]
def baseStart_1466742 : Nat := 118140960795 + 1466742 * 2 ^ 59
def prefixEnd_1466742 : Nat := 4983230072969 + 3 ^ 40 * 1466742 * 2
def baseEnd_1466742 : Nat := 18596139312024829601965

theorem tailTrace_1466742 : CollatzResearch.WordTrace tailWord_1466742 prefixEnd_1466742 18596139312024829601965 := by
  unfold tailWord_1466742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343529728265731777213655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35664317101501138956945653 3343529728265731777213655)
  ·
    refine ⟨5015294592398597665820483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3343529728265731777213655 5015294592398597665820483)
    ·
      refine ⟨7522941888597896498730725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015294592398597665820483 7522941888597896498730725)
      ·
        refine ⟨1410551604112105593512011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7522941888597896498730725 1410551604112105593512011)
        ·
          refine ⟨2115827406168158390268017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410551604112105593512011 2115827406168158390268017)
          ·
            refine ⟨1586870554626118792701013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115827406168158390268017 1586870554626118792701013)
            ·
              refine ⟨18596139312024829601965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1586870554626118792701013 18596139312024829601965)
              ·
                rfl

theorem cell22_1466742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 8].length) (baseStart_1466742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466742 prefixEnd_1466742 := by exact prefixLift 1466742
  have htrace : WordTrace (prefixWord ++ tailWord_1466742) baseStart_1466742 baseEnd_1466742 := by
    simpa [prefixWord, tailWord_1466742, baseEnd_1466742] using wordTrace_append hprefix tailTrace_1466742
  have hstable : (prefixWord ++ tailWord_1466742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466742).length < 2 ^ (prefixWord ++ tailWord_1466742).sum := by decide
  have hdescent : baseEnd_1466742 < baseStart_1466742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466830 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1466830 : Nat := 118140960795 + 1466830 * 2 ^ 59
def prefixEnd_1466830 : Nat := 4983230072969 + 3 ^ 40 * 1466830 * 2
def baseEnd_1466830 : Nat := 502125885623067503052785

theorem tailTrace_1466830 : CollatzResearch.WordTrace tailWord_1466830 prefixEnd_1466830 502125885623067503052785 := by
  unfold tailWord_1466830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687460659491612433077743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35666456850621932976414629 6687460659491612433077743)
  ·
    refine ⟨10031190989237418649616615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687460659491612433077743 10031190989237418649616615)
    ·
      refine ⟨15046786483856127974424923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10031190989237418649616615 15046786483856127974424923)
      ·
        refine ⟨22570179725784191961637385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046786483856127974424923 22570179725784191961637385)
        ·
          refine ⟨16927634794338143971228039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22570179725784191961637385 16927634794338143971228039)
          ·
            refine ⟨25391452191507215956842059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927634794338143971228039 25391452191507215956842059)
            ·
              refine ⟨38087178287260823935263089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25391452191507215956842059 38087178287260823935263089)
              ·
                refine ⟨28565383715445617951447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38087178287260823935263089 28565383715445617951447317)
                ·
                  refine ⟨1339002361661513341474093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28565383715445617951447317 1339002361661513341474093)
                  ·
                    refine ⟨502125885623067503052785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339002361661513341474093 502125885623067503052785)
                    ·
                      rfl

theorem cell22_1466830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1466830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466830 prefixEnd_1466830 := by exact prefixLift 1466830
  have htrace : WordTrace (prefixWord ++ tailWord_1466830) baseStart_1466830 baseEnd_1466830 := by
    simpa [prefixWord, tailWord_1466830, baseEnd_1466830] using wordTrace_append hprefix tailTrace_1466830
  have hstable : (prefixWord ++ tailWord_1466830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466830).length < 2 ^ (prefixWord ++ tailWord_1466830).sum := by decide
  have hdescent : baseEnd_1466830 < baseStart_1466830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466845 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1466845 : Nat := 118140960795 + 1466845 * 2 ^ 59
def prefixEnd_1466845 : Nat := 4983230072969 + 3 ^ 40 * 1466845 * 2
def baseEnd_1466845 : Nat := 502131020429612463927739

theorem tailTrace_1466845 : CollatzResearch.WordTrace tailWord_1466845 prefixEnd_1466845 502131020429612463927739 := by
  unfold tailWord_1466845
  simp only [CollatzResearch.WordTrace]
  refine ⟨53500232370878557026417989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35666821580585704684278659 53500232370878557026417989)
  ·
    refine ⟨10031293569539729442453373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53500232370878557026417989 10031293569539729442453373)
    ·
      refine ⟨3761735088577398540920015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10031293569539729442453373 3761735088577398540920015)
      ·
        refine ⟨5642602632866097811380023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761735088577398540920015 5642602632866097811380023)
        ·
          refine ⟨8463903949299146717070035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642602632866097811380023 8463903949299146717070035)
          ·
            refine ⟨12695855923948720075605053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463903949299146717070035 12695855923948720075605053)
            ·
              refine ⟨4760945971480770028351895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12695855923948720075605053 4760945971480770028351895)
              ·
                refine ⟨7141418957221155042527843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760945971480770028351895 7141418957221155042527843)
                ·
                  refine ⟨10712128435831732563791765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141418957221155042527843 10712128435831732563791765)
                  ·
                    refine ⟨502131020429612463927739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10712128435831732563791765 502131020429612463927739)
                    ·
                      rfl

theorem cell22_1466845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1466845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466845 prefixEnd_1466845 := by exact prefixLift 1466845
  have htrace : WordTrace (prefixWord ++ tailWord_1466845) baseStart_1466845 baseEnd_1466845 := by
    simpa [prefixWord, tailWord_1466845, baseEnd_1466845] using wordTrace_append hprefix tailTrace_1466845
  have hstable : (prefixWord ++ tailWord_1466845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466845).length < 2 ^ (prefixWord ++ tailWord_1466845).sum := by decide
  have hdescent : baseEnd_1466845 < baseStart_1466845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466851 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 1, 4]
def baseStart_1466851 : Nat := 118140960795 + 1466851 * 2 ^ 59
def prefixEnd_1466851 : Nat := 4983230072969 + 3 ^ 40 * 1466851 * 2
def baseEnd_1466851 : Nat := 502133074352230448277721

theorem tailTrace_1466851 : CollatzResearch.WordTrace tailWord_1466851 prefixEnd_1466851 502133074352230448277721 := by
  unfold tailWord_1466851
  simp only [CollatzResearch.WordTrace]
  refine ⟨53500451208856820051136407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35666967472571213367424271 53500451208856820051136407)
  ·
    refine ⟨80250676813285230076704611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53500451208856820051136407 80250676813285230076704611)
    ·
      refine ⟨120376015219927845115056917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80250676813285230076704611 120376015219927845115056917)
      ·
        refine ⟨5642625713434117739768293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120376015219927845115056917 5642625713434117739768293)
        ·
          refine ⟨1057992321268897076206555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5642625713434117739768293 1057992321268897076206555)
          ·
            refine ⟨1586988481903345614309833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057992321268897076206555 1586988481903345614309833)
            ·
              refine ⟨1190241361427509210732375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586988481903345614309833 1190241361427509210732375)
              ·
                refine ⟨1785362042141263816098563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190241361427509210732375 1785362042141263816098563)
                ·
                  refine ⟨2678043063211895724147845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785362042141263816098563 2678043063211895724147845)
                  ·
                    refine ⟨502133074352230448277721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678043063211895724147845 502133074352230448277721)
                    ·
                      rfl

theorem cell22_1466851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 4].length) (baseStart_1466851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466851 prefixEnd_1466851 := by exact prefixLift 1466851
  have htrace : WordTrace (prefixWord ++ tailWord_1466851) baseStart_1466851 baseEnd_1466851 := by
    simpa [prefixWord, tailWord_1466851, baseEnd_1466851] using wordTrace_append hprefix tailTrace_1466851
  have hstable : (prefixWord ++ tailWord_1466851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466851).length < 2 ^ (prefixWord ++ tailWord_1466851).sum := by decide
  have hdescent : baseEnd_1466851 < baseStart_1466851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466873 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_1466873 : Nat := 118140960795 + 1466873 * 2 ^ 59
def prefixEnd_1466873 : Nat := 4983230072969 + 3 ^ 40 * 1466873 * 2
def baseEnd_1466873 : Nat := 502140605401829724227653

theorem tailTrace_1466873 : CollatzResearch.WordTrace tailWord_1466873 prefixEnd_1466873 502140605401829724227653 := by
  unfold tailWord_1466873
  simp only [CollatzResearch.WordTrace]
  refine ⟨53501253614777117808437273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35667502409851411872291515 53501253614777117808437273)
  ·
    refine ⟨40125940211082838356327955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53501253614777117808437273 40125940211082838356327955)
    ·
      refine ⟨60188910316624257534491933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40125940211082838356327955 60188910316624257534491933)
      ·
        refine ⟨22570841368734096575434475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60188910316624257534491933 22570841368734096575434475)
        ·
          refine ⟨33856262053101144863151713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22570841368734096575434475 33856262053101144863151713)
          ·
            refine ⟨25392196539825858647363785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33856262053101144863151713 25392196539825858647363785)
            ·
              refine ⟨19044147404869393985522839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25392196539825858647363785 19044147404869393985522839)
              ·
                refine ⟨28566221107304090978284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19044147404869393985522839 28566221107304090978284259)
                ·
                  refine ⟨42849331660956136467426389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28566221107304090978284259 42849331660956136467426389)
                  ·
                    refine ⟨502140605401829724227653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42849331660956136467426389 502140605401829724227653)
                    ·
                      rfl

theorem cell22_1466873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_1466873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466873 prefixEnd_1466873 := by exact prefixLift 1466873
  have htrace : WordTrace (prefixWord ++ tailWord_1466873) baseStart_1466873 baseEnd_1466873 := by
    simpa [prefixWord, tailWord_1466873, baseEnd_1466873] using wordTrace_append hprefix tailTrace_1466873
  have hstable : (prefixWord ++ tailWord_1466873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466873).length < 2 ^ (prefixWord ++ tailWord_1466873).sum := by decide
  have hdescent : baseEnd_1466873 < baseStart_1466873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466892 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1466892 : Nat := 118140960795 + 1466892 * 2 ^ 59
def prefixEnd_1466892 : Nat := 4983230072969 + 3 ^ 40 * 1466892 * 2
def baseEnd_1466892 : Nat := 502147109490120008002595

theorem tailTrace_1466892 : CollatzResearch.WordTrace tailWord_1466892 prefixEnd_1466892 502147109490120008002595 := by
  unfold tailWord_1466892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750973300854142026689465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35667964401138856035585953 26750973300854142026689465)
  ·
    refine ⟨20063229975640606520017099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26750973300854142026689465 20063229975640606520017099)
    ·
      refine ⟨30094844963460909780025649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20063229975640606520017099 30094844963460909780025649)
      ·
        refine ⟨22571133722595682335019237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30094844963460909780025649 22571133722595682335019237)
        ·
          refine ⟨4232087572986690437816107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22571133722595682335019237 4232087572986690437816107)
          ·
            refine ⟨6348131359480035656724161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232087572986690437816107 6348131359480035656724161)
            ·
              refine ⟨4761098519610026742543121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348131359480035656724161 4761098519610026742543121)
              ·
                refine ⟨3570823889707520056907341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761098519610026742543121 3570823889707520056907341)
                ·
                  refine ⟨1339058958640320021340253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3570823889707520056907341 1339058958640320021340253)
                  ·
                    refine ⟨502147109490120008002595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339058958640320021340253 502147109490120008002595)
                    ·
                      rfl

theorem cell22_1466892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1466892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466892 prefixEnd_1466892 := by exact prefixLift 1466892
  have htrace : WordTrace (prefixWord ++ tailWord_1466892) baseStart_1466892 baseEnd_1466892 := by
    simpa [prefixWord, tailWord_1466892, baseEnd_1466892] using wordTrace_append hprefix tailTrace_1466892
  have hstable : (prefixWord ++ tailWord_1466892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466892).length < 2 ^ (prefixWord ++ tailWord_1466892).sum := by decide
  have hdescent : baseEnd_1466892 < baseStart_1466892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466926 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1466926 : Nat := 118140960795 + 1466926 * 2 ^ 59
def prefixEnd_1466926 : Nat := 4983230072969 + 3 ^ 40 * 1466926 * 2
def baseEnd_1466926 : Nat := 502158748384955252652491

theorem tailTrace_1466926 : CollatzResearch.WordTrace tailWord_1466926 prefixEnd_1466926 502158748384955252652491 := by
  unfold tailWord_1466926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687898335448138482514579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35668791122390071906744421 6687898335448138482514579)
  ·
    refine ⟨10031847503172207723771869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687898335448138482514579 10031847503172207723771869)
    ·
      refine ⟨3761942813689577896414451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10031847503172207723771869 3761942813689577896414451)
      ·
        refine ⟨5642914220534366844621677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761942813689577896414451 5642914220534366844621677)
        ·
          refine ⟨2116092832700387566733129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5642914220534366844621677 2116092832700387566733129)
          ·
            refine ⟨1587069624525290675049847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116092832700387566733129 1587069624525290675049847)
            ·
              refine ⟨2380604436787936012574771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587069624525290675049847 2380604436787936012574771)
              ·
                refine ⟨3570906655181904018862157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380604436787936012574771 3570906655181904018862157)
                ·
                  refine ⟨1339089995693214007073309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3570906655181904018862157 1339089995693214007073309)
                  ·
                    refine ⟨502158748384955252652491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339089995693214007073309 502158748384955252652491)
                    ·
                      rfl

theorem cell22_1466926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1466926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466926 prefixEnd_1466926 := by exact prefixLift 1466926
  have htrace : WordTrace (prefixWord ++ tailWord_1466926) baseStart_1466926 baseEnd_1466926 := by
    simpa [prefixWord, tailWord_1466926, baseEnd_1466926] using wordTrace_append hprefix tailTrace_1466926
  have hstable : (prefixWord ++ tailWord_1466926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466926).length < 2 ^ (prefixWord ++ tailWord_1466926).sum := by decide
  have hdescent : baseEnd_1466926 < baseStart_1466926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466935 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1466935 : Nat := 118140960795 + 1466935 * 2 ^ 59
def prefixEnd_1466935 : Nat := 4983230072969 + 3 ^ 40 * 1466935 * 2
def baseEnd_1466935 : Nat := 502161829268882229177463

theorem tailTrace_1466935 : CollatzResearch.WordTrace tailWord_1466935 prefixEnd_1466935 502161829268882229177463 := by
  unfold tailWord_1466935
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503514940552502397194259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35669009960368334931462839 53503514940552502397194259)
  ·
    refine ⟨80255272410828753595791389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53503514940552502397194259 80255272410828753595791389)
    ·
      refine ⟨30095727154060782598421771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80255272410828753595791389 30095727154060782598421771)
      ·
        refine ⟨45143590731091173897632657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30095727154060782598421771 45143590731091173897632657)
        ·
          refine ⟨33857693048318380423224493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45143590731091173897632657 33857693048318380423224493)
          ·
            refine ⟨12696634893119392658709185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33857693048318380423224493 12696634893119392658709185)
            ·
              refine ⟨9522476169839544494031889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12696634893119392658709185 9522476169839544494031889)
              ·
                refine ⟨7141857127379658370523917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9522476169839544494031889 7141857127379658370523917)
                ·
                  refine ⟨2678196422767371888946469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7141857127379658370523917 2678196422767371888946469)
                  ·
                    refine ⟨502161829268882229177463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678196422767371888946469 502161829268882229177463)
                    ·
                      rfl

theorem cell22_1466935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1466935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466935 prefixEnd_1466935 := by exact prefixLift 1466935
  have htrace : WordTrace (prefixWord ++ tailWord_1466935) baseStart_1466935 baseEnd_1466935 := by
    simpa [prefixWord, tailWord_1466935, baseEnd_1466935] using wordTrace_append hprefix tailTrace_1466935
  have hstable : (prefixWord ++ tailWord_1466935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466935).length < 2 ^ (prefixWord ++ tailWord_1466935).sum := by decide
  have hdescent : baseEnd_1466935 < baseStart_1466935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466965 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1466965 : Nat := 118140960795 + 1466965 * 2 ^ 59
def prefixEnd_1466965 : Nat := 4983230072969 + 3 ^ 40 * 1466965 * 2
def baseEnd_1466965 : Nat := 502172098881972150927371

theorem tailTrace_1466965 : CollatzResearch.WordTrace tailWord_1466965 prefixEnd_1466965 502172098881972150927371 := by
  unfold tailWord_1466965
  simp only [CollatzResearch.WordTrace]
  refine ⟨53504609130443817520786349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35669739420295878347190899 53504609130443817520786349)
  ·
    refine ⟨20064228423916431570294881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53504609130443817520786349 20064228423916431570294881)
    ·
      refine ⟨15048171317937323677721161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20064228423916431570294881 15048171317937323677721161)
      ·
        refine ⟨11286128488452992758290871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15048171317937323677721161 11286128488452992758290871)
        ·
          refine ⟨16929192732679489137436307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11286128488452992758290871 16929192732679489137436307)
          ·
            refine ⟨25393789099019233706154461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16929192732679489137436307 25393789099019233706154461)
            ·
              refine ⟨9522670912132212639807923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25393789099019233706154461 9522670912132212639807923)
              ·
                refine ⟨14284006368198318959711885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9522670912132212639807923 14284006368198318959711885)
                ·
                  refine ⟨5356502388074369609891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14284006368198318959711885 5356502388074369609891957)
                  ·
                    refine ⟨502172098881972150927371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5356502388074369609891957 502172098881972150927371)
                    ·
                      rfl

theorem cell22_1466965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1466965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466965 prefixEnd_1466965 := by exact prefixLift 1466965
  have htrace : WordTrace (prefixWord ++ tailWord_1466965) baseStart_1466965 baseEnd_1466965 := by
    simpa [prefixWord, tailWord_1466965, baseEnd_1466965] using wordTrace_append hprefix tailTrace_1466965
  have hstable : (prefixWord ++ tailWord_1466965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466965).length < 2 ^ (prefixWord ++ tailWord_1466965).sum := by decide
  have hdescent : baseEnd_1466965 < baseStart_1466965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1466967 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 4]
def baseStart_1466967 : Nat := 118140960795 + 1466967 * 2 ^ 59
def prefixEnd_1466967 : Nat := 4983230072969 + 3 ^ 40 * 1466967 * 2
def baseEnd_1466967 : Nat := 167390927840948270792455

theorem tailTrace_1466967 : CollatzResearch.WordTrace tailWord_1466967 prefixEnd_1466967 167390927840948270792455 := by
  unfold tailWord_1466967
  simp only [CollatzResearch.WordTrace]
  refine ⟨53504682076436571862359155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35669788050957714574906103 53504682076436571862359155)
  ·
    refine ⟨80257023114654857793538733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53504682076436571862359155 80257023114654857793538733)
    ·
      refine ⟨30096383667995571672577025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80257023114654857793538733 30096383667995571672577025)
      ·
        refine ⟨22572287750996678754432769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30096383667995571672577025 22572287750996678754432769)
        ·
          refine ⟨16929215813247509065824577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22572287750996678754432769 16929215813247509065824577)
          ·
            refine ⟨12696911859935631799368433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16929215813247509065824577 12696911859935631799368433)
            ·
              refine ⟨9522683894951723849526325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12696911859935631799368433 9522683894951723849526325)
              ·
                refine ⟨892751615151724110893093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9522683894951723849526325 892751615151724110893093)
                ·
                  refine ⟨167390927840948270792455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 892751615151724110893093 167390927840948270792455)
                  ·
                    rfl

theorem cell22_1466967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 4].length) (baseStart_1466967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1466967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1466967 prefixEnd_1466967 := by exact prefixLift 1466967
  have htrace : WordTrace (prefixWord ++ tailWord_1466967) baseStart_1466967 baseEnd_1466967 := by
    simpa [prefixWord, tailWord_1466967, baseEnd_1466967] using wordTrace_append hprefix tailTrace_1466967
  have hstable : (prefixWord ++ tailWord_1466967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1466967).length < 2 ^ (prefixWord ++ tailWord_1466967).sum := by decide
  have hdescent : baseEnd_1466967 < baseStart_1466967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1466967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467044 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1467044 : Nat := 118140960795 + 1467044 * 2 ^ 59
def prefixEnd_1467044 : Nat := 4983230072969 + 3 ^ 40 * 1467044 * 2
def baseEnd_1467044 : Nat := 502199142196442278202129

theorem tailTrace_1467044 : CollatzResearch.WordTrace tailWord_1467044 prefixEnd_1467044 502199142196442278202129 := by
  unfold tailWord_1467044
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753745248578807006456093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35671660331438409341941457 26753745248578807006456093)
  ·
    refine ⟨10032654468217052627421035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26753745248578807006456093 10032654468217052627421035)
    ·
      refine ⟨15048981702325578941131553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032654468217052627421035 15048981702325578941131553)
      ·
        refine ⟨11286736276744184205848665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15048981702325578941131553 11286736276744184205848665)
        ·
          refine ⟨8465052207558138154386499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11286736276744184205848665 8465052207558138154386499)
          ·
            refine ⟨12697578311337207231579749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465052207558138154386499 12697578311337207231579749)
            ·
              refine ⟨2380795933375726355921203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12697578311337207231579749 2380795933375726355921203)
              ·
                refine ⟨3571193900063589533881805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380795933375726355921203 3571193900063589533881805)
                ·
                  refine ⟨1339197712523846075205677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3571193900063589533881805 1339197712523846075205677)
                  ·
                    refine ⟨502199142196442278202129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339197712523846075205677 502199142196442278202129)
                    ·
                      rfl

theorem cell22_1467044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1467044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467044 prefixEnd_1467044 := by exact prefixLift 1467044
  have htrace : WordTrace (prefixWord ++ tailWord_1467044) baseStart_1467044 baseEnd_1467044 := by
    simpa [prefixWord, tailWord_1467044, baseEnd_1467044] using wordTrace_append hprefix tailTrace_1467044
  have hstable : (prefixWord ++ tailWord_1467044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467044).length < 2 ^ (prefixWord ++ tailWord_1467044).sum := by decide
  have hdescent : baseEnd_1467044 < baseStart_1467044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467050 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1467050 : Nat := 118140960795 + 1467050 * 2 ^ 59
def prefixEnd_1467050 : Nat := 4983230072969 + 3 ^ 40 * 1467050 * 2
def baseEnd_1467050 : Nat := 502201196119060262552111

theorem tailTrace_1467050 : CollatzResearch.WordTrace tailWord_1467050 prefixEnd_1467050 502201196119060262552111 := by
  unfold tailWord_1467050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376927333783969259407651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35671806223423918025087069 13376927333783969259407651)
  ·
    refine ⟨20065391000675953889111477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13376927333783969259407651 20065391000675953889111477)
    ·
      refine ⟨1881130406313370677104201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20065391000675953889111477 1881130406313370677104201)
      ·
        refine ⟨1410847804735028007828151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881130406313370677104201 1410847804735028007828151)
        ·
          refine ⟨2116271707102542011742227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410847804735028007828151 2116271707102542011742227)
          ·
            refine ⟨3174407560653813017613341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116271707102542011742227 3174407560653813017613341)
            ·
              refine ⟨1190402835245179881605003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174407560653813017613341 1190402835245179881605003)
              ·
                refine ⟨1785604252867769822407505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190402835245179881605003 1785604252867769822407505)
                ·
                  refine ⟨1339203189650827366805629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1785604252867769822407505 1339203189650827366805629)
                  ·
                    refine ⟨502201196119060262552111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339203189650827366805629 502201196119060262552111)
                    ·
                      rfl

theorem cell22_1467050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1467050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467050 prefixEnd_1467050 := by exact prefixLift 1467050
  have htrace : WordTrace (prefixWord ++ tailWord_1467050) baseStart_1467050 baseEnd_1467050 := by
    simpa [prefixWord, tailWord_1467050, baseEnd_1467050] using wordTrace_append hprefix tailTrace_1467050
  have hstable : (prefixWord ++ tailWord_1467050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467050).length < 2 ^ (prefixWord ++ tailWord_1467050).sum := by decide
  have hdescent : baseEnd_1467050 < baseStart_1467050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467134 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1467134 : Nat := 118140960795 + 1467134 * 2 ^ 59
def prefixEnd_1467134 : Nat := 4983230072969 + 3 ^ 40 * 1467134 * 2
def baseEnd_1467134 : Nat := 502229951035712043451853

theorem tailTrace_1467134 : CollatzResearch.WordTrace tailWord_1467134 prefixEnd_1467134 502229951035712043451853 := by
  unfold tailWord_1467134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688846633353944922961057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35673848711221039589125637 6688846633353944922961057)
  ·
    refine ⟨5016634975015458692220793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6688846633353944922961057 5016634975015458692220793)
    ·
      refine ⟨3762476231261594019165595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5016634975015458692220793 3762476231261594019165595)
      ·
        refine ⟨5643714346892391028748393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762476231261594019165595 5643714346892391028748393)
        ·
          refine ⟨4232785760169293271561295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5643714346892391028748393 4232785760169293271561295)
          ·
            refine ⟨6349178640253939907341943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232785760169293271561295 6349178640253939907341943)
            ·
              refine ⟨9523767960380909861012915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349178640253939907341943 9523767960380909861012915)
              ·
                refine ⟨14285651940571364791519373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523767960380909861012915 14285651940571364791519373)
                ·
                  refine ⟨5357119477714261796819765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14285651940571364791519373 5357119477714261796819765)
                  ·
                    refine ⟨502229951035712043451853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5357119477714261796819765 502229951035712043451853)
                    ·
                      rfl

theorem cell22_1467134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1467134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467134 prefixEnd_1467134 := by exact prefixLift 1467134
  have htrace : WordTrace (prefixWord ++ tailWord_1467134) baseStart_1467134 baseEnd_1467134 := by
    simpa [prefixWord, tailWord_1467134, baseEnd_1467134] using wordTrace_append hprefix tailTrace_1467134
  have hstable : (prefixWord ++ tailWord_1467134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467134).length < 2 ^ (prefixWord ++ tailWord_1467134).sum := by decide
  have hdescent : baseEnd_1467134 < baseStart_1467134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467138 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1467138 : Nat := 118140960795 + 1467138 * 2 ^ 59
def prefixEnd_1467138 : Nat := 4983230072969 + 3 ^ 40 * 1467138 * 2
def baseEnd_1467138 : Nat := 502231320317457366351841

theorem tailTrace_1467138 : CollatzResearch.WordTrace tailWord_1467138 prefixEnd_1467138 502231320317457366351841 := by
  unfold tailWord_1467138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377729739704267016708517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35673945972544712044556045 13377729739704267016708517)
  ·
    refine ⟨2508324326194550065632847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13377729739704267016708517 2508324326194550065632847)
    ·
      refine ⟨3762486489291825098449271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508324326194550065632847 3762486489291825098449271)
      ·
        refine ⟨5643729733937737647673907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762486489291825098449271 5643729733937737647673907)
        ·
          refine ⟨8465594600906606471510861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643729733937737647673907 8465594600906606471510861)
          ·
            refine ⟨3174597975339977426816573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8465594600906606471510861 3174597975339977426816573)
            ·
              refine ⟨1190474240752491535056215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174597975339977426816573 1190474240752491535056215)
              ·
                refine ⟨1785711361128737302584323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190474240752491535056215 1785711361128737302584323)
                ·
                  refine ⟨2678567041693105953876485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785711361128737302584323 2678567041693105953876485)
                  ·
                    refine ⟨502231320317457366351841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678567041693105953876485 502231320317457366351841)
                    ·
                      rfl

theorem cell22_1467138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1467138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467138 prefixEnd_1467138 := by exact prefixLift 1467138
  have htrace : WordTrace (prefixWord ++ tailWord_1467138) baseStart_1467138 baseEnd_1467138 := by
    simpa [prefixWord, tailWord_1467138, baseEnd_1467138] using wordTrace_append hprefix tailTrace_1467138
  have hstable : (prefixWord ++ tailWord_1467138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467138).length < 2 ^ (prefixWord ++ tailWord_1467138).sum := by decide
  have hdescent : baseEnd_1467138 < baseStart_1467138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467164 : List Nat := [2, 2, 3, 1, 1, 5, 1, 7]
def baseStart_1467164 : Nat := 118140960795 + 1467164 * 2 ^ 59
def prefixEnd_1467164 : Nat := 4983230072969 + 3 ^ 40 * 1467164 * 2
def baseEnd_1467164 : Nat := 55804468960977996133529

theorem tailTrace_1467164 : CollatzResearch.WordTrace tailWord_1467164 prefixEnd_1467164 55804468960977996133529 := by
  unfold tailWord_1467164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755933628361437253640273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35674578171148583004853697 26755933628361437253640273)
  ·
    refine ⟨20066950221271077940230205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26755933628361437253640273 20066950221271077940230205)
    ·
      refine ⟨7525106332976654227586327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20066950221271077940230205 7525106332976654227586327)
      ·
        refine ⟨11287659499464981341379491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525106332976654227586327 11287659499464981341379491)
        ·
          refine ⟨16931489249197472012069237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11287659499464981341379491 16931489249197472012069237)
          ·
            refine ⟨1587327117112263001131491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16931489249197472012069237 1587327117112263001131491)
            ·
              refine ⟨2380990675668394501697237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587327117112263001131491 2380990675668394501697237)
              ·
                refine ⟨55804468960977996133529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2380990675668394501697237 55804468960977996133529)
                ·
                  rfl

theorem cell22_1467164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_1467164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467164 prefixEnd_1467164 := by exact prefixLift 1467164
  have htrace : WordTrace (prefixWord ++ tailWord_1467164) baseStart_1467164 baseEnd_1467164 := by
    simpa [prefixWord, tailWord_1467164, baseEnd_1467164] using wordTrace_append hprefix tailTrace_1467164
  have hstable : (prefixWord ++ tailWord_1467164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467164).length < 2 ^ (prefixWord ++ tailWord_1467164).sum := by decide
  have hdescent : baseEnd_1467164 < baseStart_1467164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467192 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_1467192 : Nat := 118140960795 + 1467192 * 2 ^ 59
def prefixEnd_1467192 : Nat := 4983230072969 + 3 ^ 40 * 1467192 * 2
def baseEnd_1467192 : Nat := 167416601873673075167225

theorem tailTrace_1467192 : CollatzResearch.WordTrace tailWord_1467192 prefixEnd_1467192 167416601873673075167225 := by
  unfold tailWord_1467192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756444250310717644649915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35675259000414290192866553 26756444250310717644649915)
  ·
    refine ⟨40134666375466076466974873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26756444250310717644649915 40134666375466076466974873)
    ·
      refine ⟨30100999781599557350231155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40134666375466076466974873 30100999781599557350231155)
      ·
        refine ⟨45151499672399336025346733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30100999781599557350231155 45151499672399336025346733)
        ·
          refine ⟨16931812377149751009505025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45151499672399336025346733 16931812377149751009505025)
          ·
            refine ⟨12698859282862313257128769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931812377149751009505025 12698859282862313257128769)
            ·
              refine ⟨9524144462146734942846577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12698859282862313257128769 9524144462146734942846577)
              ·
                refine ⟨7143108346610051207134933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9524144462146734942846577 7143108346610051207134933)
                ·
                  refine ⟨167416601873673075167225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7143108346610051207134933 167416601873673075167225)
                  ·
                    rfl

theorem cell22_1467192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_1467192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467192 prefixEnd_1467192 := by exact prefixLift 1467192
  have htrace : WordTrace (prefixWord ++ tailWord_1467192) baseStart_1467192 baseEnd_1467192 := by
    simpa [prefixWord, tailWord_1467192, baseEnd_1467192] using wordTrace_append hprefix tailTrace_1467192
  have hstable : (prefixWord ++ tailWord_1467192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467192).length < 2 ^ (prefixWord ++ tailWord_1467192).sum := by decide
  have hdescent : baseEnd_1467192 < baseStart_1467192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467209 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 5]
def baseStart_1467209 : Nat := 118140960795 + 1467209 * 2 ^ 59
def prefixEnd_1467209 : Nat := 4983230072969 + 3 ^ 40 * 1467209 * 2
def baseEnd_1467209 : Nat := 167418541689478949275541

theorem tailTrace_1467209 : CollatzResearch.WordTrace tailWord_1467209 prefixEnd_1467209 167418541689478949275541 := by
  unfold tailWord_1467209
  simp only [CollatzResearch.WordTrace]
  refine ⟨53513508541559847192668681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35675672361039898128445787 53513508541559847192668681)
  ·
    refine ⟨40135131406169885394501511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53513508541559847192668681 40135131406169885394501511)
    ·
      refine ⟨60202697109254828091752267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40135131406169885394501511 60202697109254828091752267)
      ·
        refine ⟨90304045663882242137628401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60202697109254828091752267 90304045663882242137628401)
        ·
          refine ⟨67728034247911681603221301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90304045663882242137628401 67728034247911681603221301)
          ·
            refine ⟨6349503210741720150301997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67728034247911681603221301 6349503210741720150301997)
            ·
              refine ⟨2381063704028145056363249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6349503210741720150301997 2381063704028145056363249)
              ·
                refine ⟨1785797778021108792272437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381063704028145056363249 1785797778021108792272437)
                ·
                  refine ⟨167418541689478949275541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1785797778021108792272437 167418541689478949275541)
                  ·
                    rfl

theorem cell22_1467209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_1467209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467209 prefixEnd_1467209 := by exact prefixLift 1467209
  have htrace : WordTrace (prefixWord ++ tailWord_1467209) baseStart_1467209 baseEnd_1467209 := by
    simpa [prefixWord, tailWord_1467209, baseEnd_1467209] using wordTrace_append hprefix tailTrace_1467209
  have hstable : (prefixWord ++ tailWord_1467209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467209).length < 2 ^ (prefixWord ++ tailWord_1467209).sum := by decide
  have hdescent : baseEnd_1467209 < baseStart_1467209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467226 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_1467226 : Nat := 118140960795 + 1467226 * 2 ^ 59
def prefixEnd_1467226 : Nat := 4983230072969 + 3 ^ 40 * 1467226 * 2
def baseEnd_1467226 : Nat := 167420481505284823383857

theorem tailTrace_1467226 : CollatzResearch.WordTrace tailWord_1467226 prefixEnd_1467226 167420481505284823383857 := by
  unfold tailWord_1467226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378532145624564774009383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35676085721665506064025021 13378532145624564774009383)
  ·
    refine ⟨20067798218436847161014075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13378532145624564774009383 20067798218436847161014075)
    ·
      refine ⟨30101697327655270741521113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20067798218436847161014075 30101697327655270741521113)
      ·
        refine ⟨22576272995741453056140835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30101697327655270741521113 22576272995741453056140835)
        ·
          refine ⟨33864409493612179584211253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22576272995741453056140835 33864409493612179584211253)
          ·
            refine ⟨3174788390026141836019805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33864409493612179584211253 3174788390026141836019805)
            ·
              refine ⟨1190545646259803188507427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174788390026141836019805 1190545646259803188507427)
              ·
                refine ⟨1785818469389704782761141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190545646259803188507427 1785818469389704782761141)
                ·
                  refine ⟨167420481505284823383857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1785818469389704782761141 167420481505284823383857)
                  ·
                    rfl

theorem cell22_1467226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_1467226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467226 prefixEnd_1467226 := by exact prefixLift 1467226
  have htrace : WordTrace (prefixWord ++ tailWord_1467226) baseStart_1467226 baseEnd_1467226 := by
    simpa [prefixWord, tailWord_1467226, baseEnd_1467226] using wordTrace_append hprefix tailTrace_1467226
  have hstable : (prefixWord ++ tailWord_1467226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467226).length < 2 ^ (prefixWord ++ tailWord_1467226).sum := by decide
  have hdescent : baseEnd_1467226 < baseStart_1467226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467271 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 6]
def baseStart_1467271 : Nat := 118140960795 + 1467271 * 2 ^ 59
def prefixEnd_1467271 : Nat := 4983230072969 + 3 ^ 40 * 1467271 * 2
def baseEnd_1467271 : Nat := 167425616311829784258811

theorem tailTrace_1467271 : CollatzResearch.WordTrace tailWord_1467271 prefixEnd_1467271 167425616311829784258811 := by
  unfold tailWord_1467271
  simp only [CollatzResearch.WordTrace]
  refine ⟨53515769867335231781425667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35677179911556821187617111 53515769867335231781425667)
  ·
    refine ⟨80273654801002847672138501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53515769867335231781425667 80273654801002847672138501)
    ·
      refine ⟨15051310275188033938525969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80273654801002847672138501 15051310275188033938525969)
      ·
        refine ⟨11288482706391025453894477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15051310275188033938525969 11288482706391025453894477)
        ·
          refine ⟨4233181014896634545210429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11288482706391025453894477 4233181014896634545210429)
          ·
            refine ⟨1587442880586237954453911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4233181014896634545210429 1587442880586237954453911)
            ·
              refine ⟨2381164320879356931680867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587442880586237954453911 2381164320879356931680867)
              ·
                refine ⟨3571746481319035397521301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381164320879356931680867 3571746481319035397521301)
                ·
                  refine ⟨167425616311829784258811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3571746481319035397521301 167425616311829784258811)
                  ·
                    rfl

theorem cell22_1467271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].length) (baseStart_1467271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467271 prefixEnd_1467271 := by exact prefixLift 1467271
  have htrace : WordTrace (prefixWord ++ tailWord_1467271) baseStart_1467271 baseEnd_1467271 := by
    simpa [prefixWord, tailWord_1467271, baseEnd_1467271] using wordTrace_append hprefix tailTrace_1467271
  have hstable : (prefixWord ++ tailWord_1467271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467271).length < 2 ^ (prefixWord ++ tailWord_1467271).sum := by decide
  have hdescent : baseEnd_1467271 < baseStart_1467271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467290 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_1467290 : Nat := 118140960795 + 1467290 * 2 ^ 59
def prefixEnd_1467290 : Nat := 4983230072969 + 3 ^ 40 * 1467290 * 2
def baseEnd_1467290 : Nat := 502283353023779636551375

theorem tailTrace_1467290 : CollatzResearch.WordTrace tailWord_1467290 prefixEnd_1467290 502283353023779636551375 := by
  unfold tailWord_1467290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379115713566599506591831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35677641902844265350911549 13379115713566599506591831)
  ·
    refine ⟨20068673570349899259887747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379115713566599506591831 20068673570349899259887747)
    ·
      refine ⟨30103010355524848889831621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20068673570349899259887747 30103010355524848889831621)
      ·
        refine ⟨5644314441660909166843429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30103010355524848889831621 5644314441660909166843429)
        ·
          refine ⟨1058308957811420468783143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5644314441660909166843429 1058308957811420468783143)
          ·
            refine ⟨1587463436717130703174715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058308957811420468783143 1587463436717130703174715)
            ·
              refine ⟨2381195155075696054762073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587463436717130703174715 2381195155075696054762073)
              ·
                refine ⟨1785896366306772041071555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381195155075696054762073 1785896366306772041071555)
                ·
                  refine ⟨2678844549460158061607333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785896366306772041071555 2678844549460158061607333)
                  ·
                    refine ⟨502283353023779636551375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678844549460158061607333 502283353023779636551375)
                    ·
                      rfl

theorem cell22_1467290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_1467290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467290 prefixEnd_1467290 := by exact prefixLift 1467290
  have htrace : WordTrace (prefixWord ++ tailWord_1467290) baseStart_1467290 baseEnd_1467290 := by
    simpa [prefixWord, tailWord_1467290, baseEnd_1467290] using wordTrace_append hprefix tailTrace_1467290
  have hstable : (prefixWord ++ tailWord_1467290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467290).length < 2 ^ (prefixWord ++ tailWord_1467290).sum := by decide
  have hdescent : baseEnd_1467290 < baseStart_1467290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467316 : List Nat := [2, 5, 2, 1, 1, 11]
def baseStart_1467316 : Nat := 118140960795 + 1467316 * 2 ^ 59
def prefixEnd_1467316 : Nat := 4983230072969 + 3 ^ 40 * 1467316 * 2
def baseEnd_1467316 : Nat := 6201138930310175745695

theorem tailTrace_1467316 : CollatzResearch.WordTrace tailWord_1467316 prefixEnd_1467316 6201138930310175745695 := by
  unfold tailWord_1467316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758705576086102233406901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35678274101448136311209201 26758705576086102233406901)
  ·
    refine ⟨2508628647758072084381897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26758705576086102233406901 2508628647758072084381897)
    ·
      refine ⟨1881471485818554063286423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2508628647758072084381897 1881471485818554063286423)
      ·
        refine ⟨2822207228727831094929635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881471485818554063286423 2822207228727831094929635)
        ·
          refine ⟨4233310843091746642394453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822207228727831094929635 4233310843091746642394453)
          ·
            refine ⟨6201138930310175745695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4233310843091746642394453 6201138930310175745695)
            ·
              rfl

theorem cell22_1467316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 11].length) (baseStart_1467316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467316 prefixEnd_1467316 := by exact prefixLift 1467316
  have htrace : WordTrace (prefixWord ++ tailWord_1467316) baseStart_1467316 baseEnd_1467316 := by
    simpa [prefixWord, tailWord_1467316, baseEnd_1467316] using wordTrace_append hprefix tailTrace_1467316
  have hstable : (prefixWord ++ tailWord_1467316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467316).length < 2 ^ (prefixWord ++ tailWord_1467316).sum := by decide
  have hdescent : baseEnd_1467316 < baseStart_1467316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467348 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1467348 : Nat := 118140960795 + 1467348 * 2 ^ 59
def prefixEnd_1467348 : Nat := 4983230072969 + 3 ^ 40 * 1467348 * 2
def baseEnd_1467348 : Nat := 502303207609086818601197

theorem tailTrace_1467348 : CollatzResearch.WordTrace tailWord_1467348 prefixEnd_1467348 502303207609086818601197 := by
  unfold tailWord_1467348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26759289144028136965989349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35679052192037515954652465 26759289144028136965989349)
  ·
    refine ⟨5017366714505275681123003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26759289144028136965989349 5017366714505275681123003)
    ·
      refine ⟨7526050071757913521684505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017366714505275681123003 7526050071757913521684505)
      ·
        refine ⟨5644537553818435141263379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7526050071757913521684505 5644537553818435141263379)
        ·
          refine ⟨8466806330727652711895069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644537553818435141263379 8466806330727652711895069)
          ·
            refine ⟨3175052374022869766960651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8466806330727652711895069 3175052374022869766960651)
            ·
              refine ⟨4762578561034304650440977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175052374022869766960651 4762578561034304650440977)
              ·
                refine ⟨3571933920775728487830733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762578561034304650440977 3571933920775728487830733)
                ·
                  refine ⟨1339475220290898182936525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3571933920775728487830733 1339475220290898182936525)
                  ·
                    refine ⟨502303207609086818601197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339475220290898182936525 502303207609086818601197)
                    ·
                      rfl

theorem cell22_1467348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1467348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467348 prefixEnd_1467348 := by exact prefixLift 1467348
  have htrace : WordTrace (prefixWord ++ tailWord_1467348) baseStart_1467348 baseEnd_1467348 := by
    simpa [prefixWord, tailWord_1467348, baseEnd_1467348] using wordTrace_append hprefix tailTrace_1467348
  have hstable : (prefixWord ++ tailWord_1467348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467348).length < 2 ^ (prefixWord ++ tailWord_1467348).sum := by decide
  have hdescent : baseEnd_1467348 < baseStart_1467348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467378 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_1467378 : Nat := 118140960795 + 1467378 * 2 ^ 59
def prefixEnd_1467378 : Nat := 4983230072969 + 3 ^ 40 * 1467378 * 2
def baseEnd_1467378 : Nat := 167437825740725580117035

theorem tailTrace_1467378 : CollatzResearch.WordTrace tailWord_1467378 prefixEnd_1467378 167437825740725580117035 := by
  unfold tailWord_1467378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379918119486897263892697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35679781651965059370380525 13379918119486897263892697)
  ·
    refine ⟨10034938589615172947919523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13379918119486897263892697 10034938589615172947919523)
    ·
      refine ⟨15052407884422759421879285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10034938589615172947919523 15052407884422759421879285)
      ·
        refine ⟨1411163239164633695801183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15052407884422759421879285 1411163239164633695801183)
        ·
          refine ⟨2116744858746950543701775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411163239164633695801183 2116744858746950543701775)
          ·
            refine ⟨3175117288120425815552663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116744858746950543701775 3175117288120425815552663)
            ·
              refine ⟨4762675932180638723328995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175117288120425815552663 4762675932180638723328995)
              ·
                refine ⟨7144013898270958084993493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762675932180638723328995 7144013898270958084993493)
                ·
                  refine ⟨167437825740725580117035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7144013898270958084993493 167437825740725580117035)
                  ·
                    rfl

theorem cell22_1467378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_1467378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467378 prefixEnd_1467378 := by exact prefixLift 1467378
  have htrace : WordTrace (prefixWord ++ tailWord_1467378) baseStart_1467378 baseEnd_1467378 := by
    simpa [prefixWord, tailWord_1467378, baseEnd_1467378] using wordTrace_append hprefix tailTrace_1467378
  have hstable : (prefixWord ++ tailWord_1467378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467378).length < 2 ^ (prefixWord ++ tailWord_1467378).sum := by decide
  have hdescent : baseEnd_1467378 < baseStart_1467378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467406 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1467406 : Nat := 118140960795 + 1467406 * 2 ^ 59
def prefixEnd_1467406 : Nat := 4983230072969 + 3 ^ 40 * 1467406 * 2
def baseEnd_1467406 : Nat := 167441020731464666883673

theorem tailTrace_1467406 : CollatzResearch.WordTrace tailWord_1467406 prefixEnd_1467406 167441020731464666883673 := by
  unfold tailWord_1467406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690086715230768729698759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35680462481230766558393381 6690086715230768729698759)
  ·
    refine ⟨10035130072846153094548139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690086715230768729698759 10035130072846153094548139)
    ·
      refine ⟨15052695109269229641822209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035130072846153094548139 15052695109269229641822209)
      ·
        refine ⟨11289521331951922231366657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15052695109269229641822209 11289521331951922231366657)
        ·
          refine ⟨8467140998963941673524993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11289521331951922231366657 8467140998963941673524993)
          ·
            refine ⟨6350355749222956255143745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8467140998963941673524993 6350355749222956255143745)
            ·
              refine ⟨4762766811917217191357809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350355749222956255143745 4762766811917217191357809)
              ·
                refine ⟨3572075108937912893518357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762766811917217191357809 3572075108937912893518357)
                ·
                  refine ⟨167441020731464666883673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3572075108937912893518357 167441020731464666883673)
                  ·
                    rfl

theorem cell22_1467406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1467406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467406 prefixEnd_1467406 := by exact prefixLift 1467406
  have htrace : WordTrace (prefixWord ++ tailWord_1467406) baseStart_1467406 baseEnd_1467406 := by
    simpa [prefixWord, tailWord_1467406, baseEnd_1467406] using wordTrace_append hprefix tailTrace_1467406
  have hstable : (prefixWord ++ tailWord_1467406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467406).length < 2 ^ (prefixWord ++ tailWord_1467406).sum := by decide
  have hdescent : baseEnd_1467406 < baseStart_1467406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467423 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 4]
def baseStart_1467423 : Nat := 118140960795 + 1467423 * 2 ^ 59
def prefixEnd_1467423 : Nat := 4983230072969 + 3 ^ 40 * 1467423 * 2
def baseEnd_1467423 : Nat := 167442960547270540991989

theorem tailTrace_1467423 : CollatzResearch.WordTrace tailWord_1467423 prefixEnd_1467423 167442960547270540991989 := by
  unfold tailWord_1467423
  simp only [CollatzResearch.WordTrace]
  refine ⟨53521313762784561740958923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35680875841856374493972615 53521313762784561740958923)
  ·
    refine ⟨80281970644176842611438385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53521313762784561740958923 80281970644176842611438385)
    ·
      refine ⟨60211477983132631958578789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80281970644176842611438385 60211477983132631958578789)
      ·
        refine ⟨11289652121837368492233523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60211477983132631958578789 11289652121837368492233523)
        ·
          refine ⟨16934478182756052738350285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11289652121837368492233523 16934478182756052738350285)
          ·
            refine ⟨6350429318533519776881357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16934478182756052738350285 6350429318533519776881357)
            ·
              refine ⟨2381410994450069916330509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6350429318533519776881357 2381410994450069916330509)
              ·
                refine ⟨893029122918776218623941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2381410994450069916330509 893029122918776218623941)
                ·
                  refine ⟨167442960547270540991989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893029122918776218623941 167442960547270540991989)
                  ·
                    rfl

theorem cell22_1467423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 4].length) (baseStart_1467423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467423 prefixEnd_1467423 := by exact prefixLift 1467423
  have htrace : WordTrace (prefixWord ++ tailWord_1467423) baseStart_1467423 baseEnd_1467423 := by
    simpa [prefixWord, tailWord_1467423, baseEnd_1467423] using wordTrace_append hprefix tailTrace_1467423
  have hstable : (prefixWord ++ tailWord_1467423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467423).length < 2 ^ (prefixWord ++ tailWord_1467423).sum := by decide
  have hdescent : baseEnd_1467423 < baseStart_1467423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467436 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1467436 : Nat := 118140960795 + 1467436 * 2 ^ 59
def prefixEnd_1467436 : Nat := 4983230072969 + 3 ^ 40 * 1467436 * 2
def baseEnd_1467436 : Nat := 502333331807483922400927

theorem tailTrace_1467436 : CollatzResearch.WordTrace tailWord_1467436 prefixEnd_1467436 502333331807483922400927 := by
  unfold tailWord_1467436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26760893955868732480591081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35681191941158309974121441 26760893955868732480591081)
  ·
    refine ⟨20070670466901549360443311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26760893955868732480591081 20070670466901549360443311)
    ·
      refine ⟨30106005700352324040664967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20070670466901549360443311 30106005700352324040664967)
      ·
        refine ⟨45159008550528486060997451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30106005700352324040664967 45159008550528486060997451)
        ·
          refine ⟨67738512825792729091496177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45159008550528486060997451 67738512825792729091496177)
          ·
            refine ⟨50803884619344546818622133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67738512825792729091496177 50803884619344546818622133)
            ·
              refine ⟨4762864183063551264245825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50803884619344546818622133 4762864183063551264245825)
              ·
                refine ⟨3572148137297663448184369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762864183063551264245825 3572148137297663448184369)
                ·
                  refine ⟨2679111102973247586138277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572148137297663448184369 2679111102973247586138277)
                  ·
                    refine ⟨502333331807483922400927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2679111102973247586138277 502333331807483922400927)
                    ·
                      rfl

theorem cell22_1467436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1467436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467436 prefixEnd_1467436 := by exact prefixLift 1467436
  have htrace : WordTrace (prefixWord ++ tailWord_1467436) baseStart_1467436 baseEnd_1467436 := by
    simpa [prefixWord, tailWord_1467436, baseEnd_1467436] using wordTrace_append hprefix tailTrace_1467436
  have hstable : (prefixWord ++ tailWord_1467436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467436).length < 2 ^ (prefixWord ++ tailWord_1467436).sum := by decide
  have hdescent : baseEnd_1467436 < baseStart_1467436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467438 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1467438 : Nat := 118140960795 + 1467438 * 2 ^ 59
def prefixEnd_1467438 : Nat := 4983230072969 + 3 ^ 40 * 1467438 * 2
def baseEnd_1467438 : Nat := 502334016448356583850921

theorem tailTrace_1467438 : CollatzResearch.WordTrace tailWord_1467438 prefixEnd_1467438 502334016448356583850921 := by
  unfold tailWord_1467438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690232607216277412844371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35681240571820146201836645 6690232607216277412844371)
  ·
    refine ⟨10035348910824416119266557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690232607216277412844371 10035348910824416119266557)
    ·
      refine ⟨3763255841559156044724959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10035348910824416119266557 3763255841559156044724959)
      ·
        refine ⟨5644883762338734067087439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763255841559156044724959 5644883762338734067087439)
        ·
          refine ⟨8467325643508101100631159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644883762338734067087439 8467325643508101100631159)
          ·
            refine ⟨12700988465262151650946739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8467325643508101100631159 12700988465262151650946739)
            ·
              refine ⟨19051482697893227476420109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12700988465262151650946739 19051482697893227476420109)
              ·
                refine ⟨7144306011709960303657541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19051482697893227476420109 7144306011709960303657541)
                ·
                  refine ⟨1339557377195617556935789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7144306011709960303657541 1339557377195617556935789)
                  ·
                    refine ⟨502334016448356583850921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339557377195617556935789 502334016448356583850921)
                    ·
                      rfl

theorem cell22_1467438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1467438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467438 prefixEnd_1467438 := by exact prefixLift 1467438
  have htrace : WordTrace (prefixWord ++ tailWord_1467438) baseStart_1467438 baseEnd_1467438 := by
    simpa [prefixWord, tailWord_1467438, baseEnd_1467438] using wordTrace_append hprefix tailTrace_1467438
  have hstable : (prefixWord ++ tailWord_1467438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467438).length < 2 ^ (prefixWord ++ tailWord_1467438).sum := by decide
  have hdescent : baseEnd_1467438 < baseStart_1467438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467500 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_1467500 : Nat := 118140960795 + 1467500 * 2 ^ 59
def prefixEnd_1467500 : Nat := 4983230072969 + 3 ^ 40 * 1467500 * 2
def baseEnd_1467500 : Nat := 502355240315409088800731

theorem tailTrace_1467500 : CollatzResearch.WordTrace tailWord_1467500 prefixEnd_1467500 502355240315409088800731 := by
  unfold tailWord_1467500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762061091752801945755977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35682748122337069261007969 26762061091752801945755977)
  ·
    refine ⟨20071545818814601459316983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26762061091752801945755977 20071545818814601459316983)
    ·
      refine ⟨30107318728221902188975475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20071545818814601459316983 30107318728221902188975475)
      ·
        refine ⟨45160978092332853283463213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107318728221902188975475 45160978092332853283463213)
        ·
          refine ⟨16935366784624819981298705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45160978092332853283463213 16935366784624819981298705)
          ·
            refine ⟨12701525088468614985974029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935366784624819981298705 12701525088468614985974029)
            ·
              refine ⟨4763071908175730619740261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12701525088468614985974029 4763071908175730619740261)
              ·
                refine ⟨893075982782949491201299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4763071908175730619740261 893075982782949491201299)
                ·
                  refine ⟨1339613974174424236801949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893075982782949491201299 1339613974174424236801949)
                  ·
                    refine ⟨502355240315409088800731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339613974174424236801949 502355240315409088800731)
                    ·
                      rfl

theorem cell22_1467500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_1467500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467500 prefixEnd_1467500 := by exact prefixLift 1467500
  have htrace : WordTrace (prefixWord ++ tailWord_1467500) baseStart_1467500 baseEnd_1467500 := by
    simpa [prefixWord, tailWord_1467500, baseEnd_1467500] using wordTrace_append hprefix tailTrace_1467500
  have hstable : (prefixWord ++ tailWord_1467500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467500).length < 2 ^ (prefixWord ++ tailWord_1467500).sum := by decide
  have hdescent : baseEnd_1467500 < baseStart_1467500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467511 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1467511 : Nat := 118140960795 + 1467511 * 2 ^ 59
def prefixEnd_1467511 : Nat := 4983230072969 + 3 ^ 40 * 1467511 * 2
def baseEnd_1467511 : Nat := 502359005840208726775697

theorem tailTrace_1467511 : CollatzResearch.WordTrace tailWord_1467511 prefixEnd_1467511 502359005840208726775697 := by
  unfold tailWord_1467511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53524523386465752770162387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35683015590977168513441591 53524523386465752770162387)
  ·
    refine ⟨80286785079698629155243581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53524523386465752770162387 80286785079698629155243581)
    ·
      refine ⟨30107544404886985933216343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80286785079698629155243581 30107544404886985933216343)
      ·
        refine ⟨45161316607330478899824515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107544404886985933216343 45161316607330478899824515)
        ·
          refine ⟨67741974910995718349736773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45161316607330478899824515 67741974910995718349736773)
          ·
            refine ⟨12701620295811697190575645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67741974910995718349736773 12701620295811697190575645)
            ·
              refine ⟨4763107610929386446465867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12701620295811697190575645 4763107610929386446465867)
              ·
                refine ⟨7144661416394079669698801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763107610929386446465867 7144661416394079669698801)
                ·
                  refine ⟨5358496062295559752274101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144661416394079669698801 5358496062295559752274101)
                  ·
                    refine ⟨502359005840208726775697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5358496062295559752274101 502359005840208726775697)
                    ·
                      rfl

theorem cell22_1467511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1467511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467511 prefixEnd_1467511 := by exact prefixLift 1467511
  have htrace : WordTrace (prefixWord ++ tailWord_1467511) baseStart_1467511 baseEnd_1467511 := by
    simpa [prefixWord, tailWord_1467511, baseEnd_1467511] using wordTrace_append hprefix tailTrace_1467511
  have hstable : (prefixWord ++ tailWord_1467511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467511).length < 2 ^ (prefixWord ++ tailWord_1467511).sum := by decide
  have hdescent : baseEnd_1467511 < baseStart_1467511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467571 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_1467571 : Nat := 118140960795 + 1467571 * 2 ^ 59
def prefixEnd_1467571 : Nat := 4983230072969 + 3 ^ 40 * 1467571 * 2
def baseEnd_1467571 : Nat := 502379545066388570275513

theorem tailTrace_1467571 : CollatzResearch.WordTrace tailWord_1467571 prefixEnd_1467571 502379545066388570275513 := by
  unfold tailWord_1467571
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526711766248383017346567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35684474510832255344897711 53526711766248383017346567)
  ·
    refine ⟨80290067649372574526019851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53526711766248383017346567 80290067649372574526019851)
    ·
      refine ⟨120435101474058861789029777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80290067649372574526019851 120435101474058861789029777)
      ·
        refine ⟨90326326105544146341772333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120435101474058861789029777 90326326105544146341772333)
        ·
          refine ⟨33872372289579054878164625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90326326105544146341772333 33872372289579054878164625)
          ·
            refine ⟨25404279217184291158623469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33872372289579054878164625 25404279217184291158623469)
            ·
              refine ⟨9526604706444109184483801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25404279217184291158623469 9526604706444109184483801)
              ·
                refine ⟨7144953529833081888362851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9526604706444109184483801 7144953529833081888362851)
                ·
                  refine ⟨10717430294749622832544277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144953529833081888362851 10717430294749622832544277)
                  ·
                    refine ⟨502379545066388570275513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10717430294749622832544277 502379545066388570275513)
                    ·
                      rfl

theorem cell22_1467571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_1467571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467571 prefixEnd_1467571 := by exact prefixLift 1467571
  have htrace : WordTrace (prefixWord ++ tailWord_1467571) baseStart_1467571 baseEnd_1467571 := by
    simpa [prefixWord, tailWord_1467571, baseEnd_1467571] using wordTrace_append hprefix tailTrace_1467571
  have hstable : (prefixWord ++ tailWord_1467571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467571).length < 2 ^ (prefixWord ++ tailWord_1467571).sum := by decide
  have hdescent : baseEnd_1467571 < baseStart_1467571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467605 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1467605 : Nat := 118140960795 + 1467605 * 2 ^ 59
def prefixEnd_1467605 : Nat := 4983230072969 + 3 ^ 40 * 1467605 * 2
def baseEnd_1467605 : Nat := 502391183961223814925409

theorem tailTrace_1467605 : CollatzResearch.WordTrace tailWord_1467605 prefixEnd_1467605 502391183961223814925409 := by
  unfold tailWord_1467605
  simp only [CollatzResearch.WordTrace]
  refine ⟨53527951848125206824084269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35685301232083471216056179 53527951848125206824084269)
  ·
    refine ⟨20072981943046952559031601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53527951848125206824084269 20072981943046952559031601)
    ·
      refine ⟨15054736457285214419273701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20072981943046952559031601 15054736457285214419273701)
      ·
        refine ⟨2822763085740977703613819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15054736457285214419273701 2822763085740977703613819)
        ·
          refine ⟨4234144628611466555420729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822763085740977703613819 4234144628611466555420729)
          ·
            refine ⟨3175608471458599916565547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234144628611466555420729 3175608471458599916565547)
            ·
              refine ⟨4763412707187899874848321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175608471458599916565547 4763412707187899874848321)
              ·
                refine ⟨3572559530390924906136241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763412707187899874848321 3572559530390924906136241)
                ·
                  refine ⟨2679419647793193679602181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572559530390924906136241 2679419647793193679602181)
                  ·
                    refine ⟨502391183961223814925409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2679419647793193679602181 502391183961223814925409)
                    ·
                      rfl

theorem cell22_1467605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1467605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467605 prefixEnd_1467605 := by exact prefixLift 1467605
  have htrace : WordTrace (prefixWord ++ tailWord_1467605) baseStart_1467605 baseEnd_1467605 := by
    simpa [prefixWord, tailWord_1467605, baseEnd_1467605] using wordTrace_append hprefix tailTrace_1467605
  have hstable : (prefixWord ++ tailWord_1467605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467605).length < 2 ^ (prefixWord ++ tailWord_1467605).sum := by decide
  have hdescent : baseEnd_1467605 < baseStart_1467605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467680 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_1467680 : Nat := 118140960795 + 1467680 * 2 ^ 59
def prefixEnd_1467680 : Nat := 4983230072969 + 3 ^ 40 * 1467680 * 2
def baseEnd_1467680 : Nat := 502416857993948619300179

theorem tailTrace_1467680 : CollatzResearch.WordTrace tailWord_1467680 prefixEnd_1467680 502416857993948619300179 := by
  unfold tailWord_1467680
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765343661426747316532247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35687124881902329755376329 26765343661426747316532247)
  ·
    refine ⟨40148015492140120974798371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26765343661426747316532247 40148015492140120974798371)
    ·
      refine ⟨60222023238210181462197557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40148015492140120974798371 60222023238210181462197557)
      ·
        refine ⟨5645814678582204512081021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60222023238210181462197557 5645814678582204512081021)
        ·
          refine ⟨2117180504468326692030383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5645814678582204512081021 2117180504468326692030383)
          ·
            refine ⟨3175770756702490038045575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117180504468326692030383 3175770756702490038045575)
            ·
              refine ⟨4763656135053735057068363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175770756702490038045575 4763656135053735057068363)
              ·
                refine ⟨7145484202580602585602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763656135053735057068363 7145484202580602585602545)
                ·
                  refine ⟨5359113151935451939201909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145484202580602585602545 5359113151935451939201909)
                  ·
                    refine ⟨502416857993948619300179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5359113151935451939201909 502416857993948619300179)
                    ·
                      rfl

theorem cell22_1467680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_1467680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467680 prefixEnd_1467680 := by exact prefixLift 1467680
  have htrace : WordTrace (prefixWord ++ tailWord_1467680) baseStart_1467680 baseEnd_1467680 := by
    simpa [prefixWord, tailWord_1467680, baseEnd_1467680] using wordTrace_append hprefix tailTrace_1467680
  have hstable : (prefixWord ++ tailWord_1467680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467680).length < 2 ^ (prefixWord ++ tailWord_1467680).sum := by decide
  have hdescent : baseEnd_1467680 < baseStart_1467680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467862 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1467862 : Nat := 118140960795 + 1467862 * 2 ^ 59
def prefixEnd_1467862 : Nat := 4983230072969 + 3 ^ 40 * 1467862 * 2
def baseEnd_1467862 : Nat := 167493053437786937083207

theorem tailTrace_1467862 : CollatzResearch.WordTrace tailWord_1467862 prefixEnd_1467862 167493053437786937083207 := by
  unfold tailWord_1467862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346082838012133732261865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35691550272129426477459893 3346082838012133732261865)
  ·
    refine ⟨2509562128509100299196399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3346082838012133732261865 2509562128509100299196399)
    ·
      refine ⟨3764343192763650448794599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509562128509100299196399 3764343192763650448794599)
      ·
        refine ⟨5646514789145475673191899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764343192763650448794599 5646514789145475673191899)
        ·
          refine ⟨8469772183718213509787849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646514789145475673191899 8469772183718213509787849)
          ·
            refine ⟨6352329137788660132340887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8469772183718213509787849 6352329137788660132340887)
            ·
              refine ⟨9528493706682990198511331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352329137788660132340887 9528493706682990198511331)
              ·
                refine ⟨14292740560024485297766997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9528493706682990198511331 14292740560024485297766997)
                ·
                  refine ⟨167493053437786937083207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14292740560024485297766997 167493053437786937083207)
                  ·
                    rfl

theorem cell22_1467862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1467862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467862 prefixEnd_1467862 := by exact prefixLift 1467862
  have htrace : WordTrace (prefixWord ++ tailWord_1467862) baseStart_1467862 baseEnd_1467862 := by
    simpa [prefixWord, tailWord_1467862, baseEnd_1467862] using wordTrace_append hprefix tailTrace_1467862
  have hstable : (prefixWord ++ tailWord_1467862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467862).length < 2 ^ (prefixWord ++ tailWord_1467862).sum := by decide
  have hdescent : baseEnd_1467862 < baseStart_1467862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467877 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1467877 : Nat := 118140960795 + 1467877 * 2 ^ 59
def prefixEnd_1467877 : Nat := 4983230072969 + 3 ^ 40 * 1467877 * 2
def baseEnd_1467877 : Nat := 502484295119905772124575

theorem tailTrace_1467877 : CollatzResearch.WordTrace tailWord_1467877 prefixEnd_1467877 502484295119905772124575 := by
  unfold tailWord_1467877
  simp only [CollatzResearch.WordTrace]
  refine ⟨53537872503139797277985885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35691915002093198185323923 53537872503139797277985885)
  ·
    refine ⟨20076702188677423979244707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53537872503139797277985885 20076702188677423979244707)
    ·
      refine ⟨30115053283016135968867061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20076702188677423979244707 30115053283016135968867061)
      ·
        refine ⟨2823286245282762747081287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30115053283016135968867061 2823286245282762747081287)
        ·
          refine ⟨4234929367924144120621931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823286245282762747081287 4234929367924144120621931)
          ·
            refine ⟨6352394051886216180932897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234929367924144120621931 6352394051886216180932897)
            ·
              refine ⟨4764295538914662135699673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352394051886216180932897 4764295538914662135699673)
              ·
                refine ⟨3573221654185996601774755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764295538914662135699673 3573221654185996601774755)
                ·
                  refine ⟨5359832481278994902662133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573221654185996601774755 5359832481278994902662133)
                  ·
                    refine ⟨502484295119905772124575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5359832481278994902662133 502484295119905772124575)
                    ·
                      rfl

theorem cell22_1467877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1467877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467877 prefixEnd_1467877 := by exact prefixLift 1467877
  have htrace : WordTrace (prefixWord ++ tailWord_1467877) baseStart_1467877 baseEnd_1467877 := by
    simpa [prefixWord, tailWord_1467877, baseEnd_1467877] using wordTrace_append hprefix tailTrace_1467877
  have hstable : (prefixWord ++ tailWord_1467877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467877).length < 2 ^ (prefixWord ++ tailWord_1467877).sum := by decide
  have hdescent : baseEnd_1467877 < baseStart_1467877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467879 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 4]
def baseStart_1467879 : Nat := 118140960795 + 1467879 * 2 ^ 59
def prefixEnd_1467879 : Nat := 4983230072969 + 3 ^ 40 * 1467879 * 2
def baseEnd_1467879 : Nat := 167494993253592811191523

theorem tailTrace_1467879 : CollatzResearch.WordTrace tailWord_1467879 prefixEnd_1467879 167494993253592811191523 := by
  unfold tailWord_1467879
  simp only [CollatzResearch.WordTrace]
  refine ⟨53537945449132551619558691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35691963632755034413039127 53537945449132551619558691)
  ·
    refine ⟨80306918173698827429338037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53537945449132551619558691 80306918173698827429338037)
    ·
      refine ⟨7528773578784265071500441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80306918173698827429338037 7528773578784265071500441)
      ·
        refine ⟨5646580184088198803625331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7528773578784265071500441 5646580184088198803625331)
        ·
          refine ⟨8469870276132298205437997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646580184088198803625331 8469870276132298205437997)
          ·
            refine ⟨3176201353549611827039249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8469870276132298205437997 3176201353549611827039249)
            ·
              refine ⟨2382151015162208870279437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176201353549611827039249 2382151015162208870279437)
              ·
                refine ⟨893306630685828326354789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382151015162208870279437 893306630685828326354789)
                ·
                  refine ⟨167494993253592811191523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893306630685828326354789 167494993253592811191523)
                  ·
                    rfl

theorem cell22_1467879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 4].length) (baseStart_1467879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467879 prefixEnd_1467879 := by exact prefixLift 1467879
  have htrace : WordTrace (prefixWord ++ tailWord_1467879) baseStart_1467879 baseEnd_1467879 := by
    simpa [prefixWord, tailWord_1467879, baseEnd_1467879] using wordTrace_append hprefix tailTrace_1467879
  have hstable : (prefixWord ++ tailWord_1467879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467879).length < 2 ^ (prefixWord ++ tailWord_1467879).sum := by decide
  have hdescent : baseEnd_1467879 < baseStart_1467879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467894 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_1467894 : Nat := 118140960795 + 1467894 * 2 ^ 59
def prefixEnd_1467894 : Nat := 4983230072969 + 3 ^ 40 * 1467894 * 2
def baseEnd_1467894 : Nat := 502490114567323394449523

theorem tailTrace_1467894 : CollatzResearch.WordTrace tailWord_1467894 prefixEnd_1467894 502490114567323394449523 := by
  unfold tailWord_1467894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346155784004888073834671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35692328362718806120903157 3346155784004888073834671)
  ·
    refine ⟨5019233676007332110752007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346155784004888073834671 5019233676007332110752007)
    ·
      refine ⟨7528850514010998166128011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019233676007332110752007 7528850514010998166128011)
      ·
        refine ⟨11293275771016497249192017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7528850514010998166128011 11293275771016497249192017)
        ·
          refine ⟨8469956828262372936894013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11293275771016497249192017 8469956828262372936894013)
          ·
            refine ⟨3176233810598389851335255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8469956828262372936894013 3176233810598389851335255)
            ·
              refine ⟨4764350715897584777002883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176233810598389851335255 4764350715897584777002883)
              ·
                refine ⟨7146526073846377165504325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764350715897584777002883 7146526073846377165504325)
                ·
                  refine ⟨1339973638846195718532061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7146526073846377165504325 1339973638846195718532061)
                  ·
                    refine ⟨502490114567323394449523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339973638846195718532061 502490114567323394449523)
                    ·
                      rfl

theorem cell22_1467894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_1467894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467894 prefixEnd_1467894 := by exact prefixLift 1467894
  have htrace : WordTrace (prefixWord ++ tailWord_1467894) baseStart_1467894 baseEnd_1467894 := by
    simpa [prefixWord, tailWord_1467894, baseEnd_1467894] using wordTrace_append hprefix tailTrace_1467894
  have hstable : (prefixWord ++ tailWord_1467894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467894).length < 2 ^ (prefixWord ++ tailWord_1467894).sum := by decide
  have hdescent : baseEnd_1467894 < baseStart_1467894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467911 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 2, 3]
def baseStart_1467911 : Nat := 118140960795 + 1467911 * 2 ^ 59
def prefixEnd_1467911 : Nat := 4983230072969 + 3 ^ 40 * 1467911 * 2
def baseEnd_1467911 : Nat := 502495934014741016774471

theorem tailTrace_1467911 : CollatzResearch.WordTrace tailWord_1467911 prefixEnd_1467911 502495934014741016774471 := by
  unfold tailWord_1467911
  simp only [CollatzResearch.WordTrace]
  refine ⟨53539112585016621084723587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35692741723344414056482391 53539112585016621084723587)
  ·
    refine ⟨80308668877524931627085381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53539112585016621084723587 80308668877524931627085381)
    ·
      refine ⟨15057875414535924680078509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80308668877524931627085381 15057875414535924680078509)
      ·
        refine ⟨5646703280450971755029441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15057875414535924680078509 5646703280450971755029441)
        ·
          refine ⟨4235027460338228816272081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5646703280450971755029441 4235027460338228816272081)
          ·
            refine ⟨3176270595253671612204061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235027460338228816272081 3176270595253671612204061)
            ·
              refine ⟨1191101473220126854576523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3176270595253671612204061 1191101473220126854576523)
              ·
                refine ⟨1786652209830190281864785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191101473220126854576523 1786652209830190281864785)
                ·
                  refine ⟨1339989157372642711398589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786652209830190281864785 1339989157372642711398589)
                  ·
                    refine ⟨502495934014741016774471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1339989157372642711398589 502495934014741016774471)
                    ·
                      rfl

theorem cell22_1467911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_1467911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467911 prefixEnd_1467911 := by exact prefixLift 1467911
  have htrace : WordTrace (prefixWord ++ tailWord_1467911) baseStart_1467911 baseEnd_1467911 := by
    simpa [prefixWord, tailWord_1467911, baseEnd_1467911] using wordTrace_append hprefix tailTrace_1467911
  have hstable : (prefixWord ++ tailWord_1467911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467911).length < 2 ^ (prefixWord ++ tailWord_1467911).sum := by decide
  have hdescent : baseEnd_1467911 < baseStart_1467911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467924 : List Nat := [2, 4, 3, 1, 2, 1, 1, 8]
def baseStart_1467924 : Nat := 118140960795 + 1467924 * 2 ^ 59
def prefixEnd_1467924 : Nat := 4983230072969 + 3 ^ 40 * 1467924 * 2
def baseEnd_1467924 : Nat := 55833376020045924022159

theorem tailTrace_1467924 : CollatzResearch.WordTrace tailWord_1467924 prefixEnd_1467924 55833376020045924022159 := by
  unfold tailWord_1467924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769793366984762152473413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35693057822646349536631217 26769793366984762152473413)
  ·
    refine ⟨5019336256309642903588765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26769793366984762152473413 5019336256309642903588765)
    ·
      refine ⟨1882251096116116088845787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5019336256309642903588765 1882251096116116088845787)
      ·
        refine ⟨2823376644174174133268681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882251096116116088845787 2823376644174174133268681)
        ·
          refine ⟨2117532483130630599951511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823376644174174133268681 2117532483130630599951511)
          ·
            refine ⟨3176298724695945899927267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117532483130630599951511 3176298724695945899927267)
            ·
              refine ⟨4764448087043918849890901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176298724695945899927267 4764448087043918849890901)
              ·
                refine ⟨55833376020045924022159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4764448087043918849890901 55833376020045924022159)
                ·
                  rfl

theorem cell22_1467924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_1467924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467924 prefixEnd_1467924 := by exact prefixLift 1467924
  have htrace : WordTrace (prefixWord ++ tailWord_1467924) baseStart_1467924 baseEnd_1467924 := by
    simpa [prefixWord, tailWord_1467924, baseEnd_1467924] using wordTrace_append hprefix tailTrace_1467924
  have hstable : (prefixWord ++ tailWord_1467924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467924).length < 2 ^ (prefixWord ++ tailWord_1467924).sum := by decide
  have hdescent : baseEnd_1467924 < baseStart_1467924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467935 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 7]
def baseStart_1467935 : Nat := 118140960795 + 1467935 * 2 ^ 59
def prefixEnd_1467935 : Nat := 4983230072969 + 3 ^ 40 * 1467935 * 2
def baseEnd_1467935 : Nat := 167501383235070984724799

theorem tailTrace_1467935 : CollatzResearch.WordTrace tailWord_1467935 prefixEnd_1467935 167501383235070984724799 := by
  unfold tailWord_1467935
  simp only [CollatzResearch.WordTrace]
  refine ⟨53539987936929673183597259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35693325291286448789064839 53539987936929673183597259)
  ·
    refine ⟨80309981905394509775395889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53539987936929673183597259 80309981905394509775395889)
    ·
      refine ⟨60232486429045882331546917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80309981905394509775395889 60232486429045882331546917)
      ·
        refine ⟨11293591205446102937165047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60232486429045882331546917 11293591205446102937165047)
        ·
          refine ⟨16940386808169154405747571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293591205446102937165047 16940386808169154405747571)
          ·
            refine ⟨25410580212253731608621357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940386808169154405747571 25410580212253731608621357)
            ·
              refine ⟨9528967579595149353233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25410580212253731608621357 9528967579595149353233009)
              ·
                refine ⟨7146725684696362014924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9528967579595149353233009 7146725684696362014924757)
                ·
                  refine ⟨167501383235070984724799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7146725684696362014924757 167501383235070984724799)
                  ·
                    rfl

theorem cell22_1467935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_1467935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1467935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1467935 prefixEnd_1467935 := by exact prefixLift 1467935
  have htrace : WordTrace (prefixWord ++ tailWord_1467935) baseStart_1467935 baseEnd_1467935 := by
    simpa [prefixWord, tailWord_1467935, baseEnd_1467935] using wordTrace_append hprefix tailTrace_1467935
  have hstable : (prefixWord ++ tailWord_1467935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467935).length < 2 ^ (prefixWord ++ tailWord_1467935).sum := by decide
  have hdescent : baseEnd_1467935 < baseStart_1467935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468029 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1468029 : Nat := 118140960795 + 1468029 * 2 ^ 59
def prefixEnd_1468029 : Nat := 4983230072969 + 3 ^ 40 * 1468029 * 2
def baseEnd_1468029 : Nat := 502536327826228042324109

theorem tailTrace_1468029 : CollatzResearch.WordTrace tailWord_1468029 prefixEnd_1468029 502536327826228042324109 := by
  unfold tailWord_1468029
  simp only [CollatzResearch.WordTrace]
  refine ⟨53543416398589127237519141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35695610932392751491679427 53543416398589127237519141)
  ·
    refine ⟨10039390574735461357034839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53543416398589127237519141 10039390574735461357034839)
    ·
      refine ⟨15059085862103192035552259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039390574735461357034839 15059085862103192035552259)
      ·
        refine ⟨22588628793154788053328389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15059085862103192035552259 22588628793154788053328389)
        ·
          refine ⟨4235367898716522759999073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22588628793154788053328389 4235367898716522759999073)
          ·
            refine ⟨3176525924037392069999305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235367898716522759999073 3176525924037392069999305)
            ·
              refine ⟨2382394443028044052499479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176525924037392069999305 2382394443028044052499479)
              ·
                refine ⟨3573591664542066078749219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382394443028044052499479 3573591664542066078749219)
                ·
                  refine ⟨5360387496813099118123829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573591664542066078749219 5360387496813099118123829)
                  ·
                    refine ⟨502536327826228042324109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5360387496813099118123829 502536327826228042324109)
                    ·
                      rfl

theorem cell22_1468029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1468029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468029 prefixEnd_1468029 := by exact prefixLift 1468029
  have htrace : WordTrace (prefixWord ++ tailWord_1468029) baseStart_1468029 baseEnd_1468029 := by
    simpa [prefixWord, tailWord_1468029, baseEnd_1468029] using wordTrace_append hprefix tailTrace_1468029
  have hstable : (prefixWord ++ tailWord_1468029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468029).length < 2 ^ (prefixWord ++ tailWord_1468029).sum := by decide
  have hdescent : baseEnd_1468029 < baseStart_1468029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468050 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1468050 : Nat := 118140960795 + 1468050 * 2 ^ 59
def prefixEnd_1468050 : Nat := 4983230072969 + 3 ^ 40 * 1468050 * 2
def baseEnd_1468050 : Nat := 502543516555390987549045

theorem tailTrace_1468050 : CollatzResearch.WordTrace tailWord_1468050 prefixEnd_1468050 502543516555390987549045 := by
  unfold tailWord_1468050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386045582878261956008401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35696121554342031882689069 13386045582878261956008401)
  ·
    refine ⟨10039534187158696467006301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386045582878261956008401 10039534187158696467006301)
    ·
      refine ⟨3764825320184511175127363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10039534187158696467006301 3764825320184511175127363)
      ·
        refine ⟨5647237980276766762691045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764825320184511175127363 5647237980276766762691045)
        ·
          refine ⟨1058857121301893768004571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5647237980276766762691045 1058857121301893768004571)
          ·
            refine ⟨1588285681952840652006857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058857121301893768004571 1588285681952840652006857)
            ·
              refine ⟨1191214261464630489005143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588285681952840652006857 1191214261464630489005143)
              ·
                refine ⟨1786821392196945733507715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191214261464630489005143 1786821392196945733507715)
                ·
                  refine ⟨2680232088295418600261573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786821392196945733507715 2680232088295418600261573)
                  ·
                    refine ⟨502543516555390987549045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680232088295418600261573 502543516555390987549045)
                    ·
                      rfl

theorem cell22_1468050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1468050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468050 prefixEnd_1468050 := by exact prefixLift 1468050
  have htrace : WordTrace (prefixWord ++ tailWord_1468050) baseStart_1468050 baseEnd_1468050 := by
    simpa [prefixWord, tailWord_1468050, baseEnd_1468050] using wordTrace_append hprefix tailTrace_1468050
  have hstable : (prefixWord ++ tailWord_1468050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468050).length < 2 ^ (prefixWord ++ tailWord_1468050).sum := by decide
  have hdescent : baseEnd_1468050 < baseStart_1468050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468125 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1468125 : Nat := 118140960795 + 1468125 * 2 ^ 59
def prefixEnd_1468125 : Nat := 4983230072969 + 3 ^ 40 * 1468125 * 2
def baseEnd_1468125 : Nat := 502569190588115791923815

theorem tailTrace_1468125 : CollatzResearch.WordTrace tailWord_1468125 prefixEnd_1468125 502569190588115791923815 := by
  unfold tailWord_1468125
  simp only [CollatzResearch.WordTrace]
  refine ⟨53546917806241335633013829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35697945204160890422009219 53546917806241335633013829)
  ·
    refine ⟨10040047088670250431190093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53546917806241335633013829 10040047088670250431190093)
    ·
      refine ⟨3765017658251343911696285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10040047088670250431190093 3765017658251343911696285)
      ·
        refine ⟨1411881621844253966886107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3765017658251343911696285 1411881621844253966886107)
        ·
          refine ⟨2117822432766380950329161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411881621844253966886107 2117822432766380950329161)
          ·
            refine ⟨1588366824574785712746871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117822432766380950329161 1588366824574785712746871)
            ·
              refine ⟨2382550236862178569120307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588366824574785712746871 2382550236862178569120307)
              ·
                refine ⟨3573825355293267853680461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382550236862178569120307 3573825355293267853680461)
                ·
                  refine ⟨1340184508234975445130173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3573825355293267853680461 1340184508234975445130173)
                  ·
                    refine ⟨502569190588115791923815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340184508234975445130173 502569190588115791923815)
                    ·
                      rfl

theorem cell22_1468125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1468125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468125 prefixEnd_1468125 := by exact prefixLift 1468125
  have htrace : WordTrace (prefixWord ++ tailWord_1468125) baseStart_1468125 baseEnd_1468125 := by
    simpa [prefixWord, tailWord_1468125, baseEnd_1468125] using wordTrace_append hprefix tailTrace_1468125
  have hstable : (prefixWord ++ tailWord_1468125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468125).length < 2 ^ (prefixWord ++ tailWord_1468125).sum := by decide
  have hdescent : baseEnd_1468125 < baseStart_1468125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468164 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1468164 : Nat := 118140960795 + 1468164 * 2 ^ 59
def prefixEnd_1468164 : Nat := 4983230072969 + 3 ^ 40 * 1468164 * 2
def baseEnd_1468164 : Nat := 502582541085132690198695

theorem tailTrace_1468164 : CollatzResearch.WordTrace tailWord_1468164 prefixEnd_1468164 502582541085132690198695 := by
  unfold tailWord_1468164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774170126550022646841773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35698893502066696862455697 26774170126550022646841773)
  ·
    refine ⟨10040313797456258492565665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26774170126550022646841773 10040313797456258492565665)
    ·
      refine ⟨7530235348092193869424249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10040313797456258492565665 7530235348092193869424249)
      ·
        refine ⟨5647676511069145402068187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7530235348092193869424249 5647676511069145402068187)
        ·
          refine ⟨8471514766603718103102281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647676511069145402068187 8471514766603718103102281)
          ·
            refine ⟨6353636074952788577326711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8471514766603718103102281 6353636074952788577326711)
            ·
              refine ⟨9530454112429182865990067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353636074952788577326711 9530454112429182865990067)
              ·
                refine ⟨14295681168643774298985101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9530454112429182865990067 14295681168643774298985101)
                ·
                  refine ⟨5360880438241415362119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14295681168643774298985101 5360880438241415362119413)
                  ·
                    refine ⟨502582541085132690198695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5360880438241415362119413 502582541085132690198695)
                    ·
                      rfl

theorem cell22_1468164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1468164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468164 prefixEnd_1468164 := by exact prefixLift 1468164
  have htrace : WordTrace (prefixWord ++ tailWord_1468164) baseStart_1468164 baseEnd_1468164 := by
    simpa [prefixWord, tailWord_1468164, baseEnd_1468164] using wordTrace_append hprefix tailTrace_1468164
  have hstable : (prefixWord ++ tailWord_1468164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468164).length < 2 ^ (prefixWord ++ tailWord_1468164).sum := by decide
  have hdescent : baseEnd_1468164 < baseStart_1468164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468181 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1468181 : Nat := 118140960795 + 1468181 * 2 ^ 59
def prefixEnd_1468181 : Nat := 4983230072969 + 3 ^ 40 * 1468181 * 2
def baseEnd_1468181 : Nat := 502588360532550312523643

theorem tailTrace_1468181 : CollatzResearch.WordTrace tailWord_1468181 prefixEnd_1468181 502588360532550312523643 := by
  unfold tailWord_1468181
  simp only [CollatzResearch.WordTrace]
  refine ⟨53548960294038457197052397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35699306862692304798034931 53548960294038457197052397)
  ·
    refine ⟨20080860110264421448894649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53548960294038457197052397 20080860110264421448894649)
    ·
      refine ⟨15060645082698316086670987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20080860110264421448894649 15060645082698316086670987)
      ·
        refine ⟨22590967624047474130006481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060645082698316086670987 22590967624047474130006481)
        ·
          refine ⟨16943225718035605597504861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22590967624047474130006481 16943225718035605597504861)
          ·
            refine ⟨6353709644263352099064323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16943225718035605597504861 6353709644263352099064323)
            ·
              refine ⟨9530564466395028148596485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353709644263352099064323 9530564466395028148596485)
              ·
                refine ⟨1786980837449067777861841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9530564466395028148596485 1786980837449067777861841)
                ·
                  refine ⟨1340235628086800833396381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786980837449067777861841 1340235628086800833396381)
                  ·
                    refine ⟨502588360532550312523643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340235628086800833396381 502588360532550312523643)
                    ·
                      rfl

theorem cell22_1468181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1468181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468181 prefixEnd_1468181 := by exact prefixLift 1468181
  have htrace : WordTrace (prefixWord ++ tailWord_1468181) baseStart_1468181 baseEnd_1468181 := by
    simpa [prefixWord, tailWord_1468181, baseEnd_1468181] using wordTrace_append hprefix tailTrace_1468181
  have hstable : (prefixWord ++ tailWord_1468181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468181).length < 2 ^ (prefixWord ++ tailWord_1468181).sum := by decide
  have hdescent : baseEnd_1468181 < baseStart_1468181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468183 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 4]
def baseStart_1468183 : Nat := 118140960795 + 1468183 * 2 ^ 59
def prefixEnd_1468183 : Nat := 4983230072969 + 3 ^ 40 * 1468183 * 2
def baseEnd_1468183 : Nat := 167529681724474324657879

theorem tailTrace_1468183 : CollatzResearch.WordTrace tailWord_1468183 prefixEnd_1468183 167529681724474324657879 := by
  unfold tailWord_1468183
  simp only [CollatzResearch.WordTrace]
  refine ⟨53549033240031211538625203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35699355493354141025750135 53549033240031211538625203)
  ·
    refine ⟨80323549860046817307937805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53549033240031211538625203 80323549860046817307937805)
    ·
      refine ⟨30121331197517556490476677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80323549860046817307937805 30121331197517556490476677)
      ·
        refine ⟨5647749599534541841964377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30121331197517556490476677 5647749599534541841964377)
        ·
          refine ⟨4235812199650906381473283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5647749599534541841964377 4235812199650906381473283)
          ·
            refine ⟨6353718299476359572209925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235812199650906381473283 6353718299476359572209925)
            ·
              refine ⟨1191322181151817419789361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6353718299476359572209925 1191322181151817419789361)
              ·
                refine ⟨893491635863863064842021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191322181151817419789361 893491635863863064842021)
                ·
                  refine ⟨167529681724474324657879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893491635863863064842021 167529681724474324657879)
                  ·
                    rfl

theorem cell22_1468183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 4].length) (baseStart_1468183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468183 prefixEnd_1468183 := by exact prefixLift 1468183
  have htrace : WordTrace (prefixWord ++ tailWord_1468183) baseStart_1468183 baseEnd_1468183 := by
    simpa [prefixWord, tailWord_1468183, baseEnd_1468183] using wordTrace_append hprefix tailTrace_1468183
  have hstable : (prefixWord ++ tailWord_1468183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468183).length < 2 ^ (prefixWord ++ tailWord_1468183).sum := by decide
  have hdescent : baseEnd_1468183 < baseStart_1468183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468211 : List Nat := [1, 1, 1, 2, 7, 1, 3, 6]
def baseStart_1468211 : Nat := 118140960795 + 1468211 * 2 ^ 59
def prefixEnd_1468211 : Nat := 4983230072969 + 3 ^ 40 * 1468211 * 2
def baseEnd_1468211 : Nat := 55844292238404470474839

theorem tailTrace_1468211 : CollatzResearch.WordTrace tailWord_1468211 prefixEnd_1468211 55844292238404470474839 := by
  unfold tailWord_1468211
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550054483929772320644487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35700036322619848213762991 53550054483929772320644487)
  ·
    refine ⟨80325081725894658480966731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53550054483929772320644487 80325081725894658480966731)
    ·
      refine ⟨120487622588841987721450097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80325081725894658480966731 120487622588841987721450097)
      ·
        refine ⟨90365716941631490791087573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120487622588841987721450097 90365716941631490791087573)
        ·
          refine ⟨2117946490819488065416115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90365716941631490791087573 2117946490819488065416115)
          ·
            refine ⟨3176919736229232098124173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117946490819488065416115 3176919736229232098124173)
            ·
              refine ⟨1191344901085962036796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3176919736229232098124173 1191344901085962036796565)
              ·
                refine ⟨55844292238404470474839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1191344901085962036796565 55844292238404470474839)
                ·
                  rfl

theorem cell22_1468211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 6].length) (baseStart_1468211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468211 prefixEnd_1468211 := by exact prefixLift 1468211
  have htrace : WordTrace (prefixWord ++ tailWord_1468211) baseStart_1468211 baseEnd_1468211 := by
    simpa [prefixWord, tailWord_1468211, baseEnd_1468211] using wordTrace_append hprefix tailTrace_1468211
  have hstable : (prefixWord ++ tailWord_1468211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468211).length < 2 ^ (prefixWord ++ tailWord_1468211).sum := by decide
  have hdescent : baseEnd_1468211 < baseStart_1468211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468213 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1468213 : Nat := 118140960795 + 1468213 * 2 ^ 59
def prefixEnd_1468213 : Nat := 4983230072969 + 3 ^ 40 * 1468213 * 2
def baseEnd_1468213 : Nat := 502599314786512895723545

theorem tailTrace_1468213 : CollatzResearch.WordTrace tailWord_1468213 prefixEnd_1468213 502599314786512895723545 := by
  unfold tailWord_1468213
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550127429922526662217293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35700084953281684441478195 53550127429922526662217293)
  ·
    refine ⟨20081297786220947498331485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53550127429922526662217293 20081297786220947498331485)
    ·
      refine ⟨7530486669832855311874307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20081297786220947498331485 7530486669832855311874307)
      ·
        refine ⟨11295730004749282967811461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7530486669832855311874307 11295730004749282967811461)
        ·
          refine ⟨2117949375890490556464649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11295730004749282967811461 2117949375890490556464649)
          ·
            refine ⟨1588462031917867917348487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117949375890490556464649 1588462031917867917348487)
            ·
              refine ⟨2382693047876801876022731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588462031917867917348487 2382693047876801876022731)
              ·
                refine ⟨3574039571815202814034097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382693047876801876022731 3574039571815202814034097)
                ·
                  refine ⟨2680529678861402110525573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574039571815202814034097 2680529678861402110525573)
                  ·
                    refine ⟨502599314786512895723545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680529678861402110525573 502599314786512895723545)
                    ·
                      rfl

theorem cell22_1468213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1468213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468213 prefixEnd_1468213 := by exact prefixLift 1468213
  have htrace : WordTrace (prefixWord ++ tailWord_1468213) baseStart_1468213 baseEnd_1468213 := by
    simpa [prefixWord, tailWord_1468213, baseEnd_1468213] using wordTrace_append hprefix tailTrace_1468213
  have hstable : (prefixWord ++ tailWord_1468213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468213).length < 2 ^ (prefixWord ++ tailWord_1468213).sum := by decide
  have hdescent : baseEnd_1468213 < baseStart_1468213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468350 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1468350 : Nat := 118140960795 + 1468350 * 2 ^ 59
def prefixEnd_1468350 : Nat := 4983230072969 + 3 ^ 40 * 1468350 * 2
def baseEnd_1468350 : Nat := 502646212686290205048125

theorem tailTrace_1468350 : CollatzResearch.WordTrace tailWord_1468350 prefixEnd_1468350 502646212686290205048125 := by
  unfold tailWord_1468350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694390528803274882494313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35703416153617466039969669 6694390528803274882494313)
  ·
    refine ⟨5020792896602456161870735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6694390528803274882494313 5020792896602456161870735)
    ·
      refine ⟨7531189344903684242806103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5020792896602456161870735 7531189344903684242806103)
      ·
        refine ⟨11296784017355526364209155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7531189344903684242806103 11296784017355526364209155)
        ·
          refine ⟨16945176026033289546313733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11296784017355526364209155 16945176026033289546313733)
          ·
            refine ⟨3177220504881241789933825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16945176026033289546313733 3177220504881241789933825)
            ·
              refine ⟨2382915378660931342450369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177220504881241789933825 2382915378660931342450369)
              ·
                refine ⟨1787186533995698506837777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382915378660931342450369 1787186533995698506837777)
                ·
                  refine ⟨1340389900496773880128333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787186533995698506837777 1340389900496773880128333)
                  ·
                    refine ⟨502646212686290205048125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340389900496773880128333 502646212686290205048125)
                    ·
                      rfl

theorem cell22_1468350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1468350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468350 prefixEnd_1468350 := by exact prefixLift 1468350
  have htrace : WordTrace (prefixWord ++ tailWord_1468350) baseStart_1468350 baseEnd_1468350 := by
    simpa [prefixWord, tailWord_1468350, baseEnd_1468350] using wordTrace_append hprefix tailTrace_1468350
  have hstable : (prefixWord ++ tailWord_1468350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468350).length < 2 ^ (prefixWord ++ tailWord_1468350).sum := by decide
  have hdescent : baseEnd_1468350 < baseStart_1468350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468451 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_1468451 : Nat := 118140960795 + 1468451 * 2 ^ 59
def prefixEnd_1468451 : Nat := 4983230072969 + 3 ^ 40 * 1468451 * 2
def baseEnd_1468451 : Nat := 502680787050359608272815

theorem tailTrace_1468451 : CollatzResearch.WordTrace tailWord_1468451 prefixEnd_1468451 502680787050359608272815 := by
  unfold tailWord_1468451
  simp only [CollatzResearch.WordTrace]
  refine ⟨53558808003060293309381207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35705872002040195539587471 53558808003060293309381207)
  ·
    refine ⟨80338212004590439964071811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53558808003060293309381207 80338212004590439964071811)
    ·
      refine ⟨120507318006885659946107717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80338212004590439964071811 120507318006885659946107717)
      ·
        refine ⟨22595122126291061239895197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120507318006885659946107717 22595122126291061239895197)
        ·
          refine ⟨8473170797359147964960699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22595122126291061239895197 8473170797359147964960699)
          ·
            refine ⟨12709756196038721947441049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473170797359147964960699 12709756196038721947441049)
            ·
              refine ⟨9532317147029041460580787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12709756196038721947441049 9532317147029041460580787)
              ·
                refine ⟨14298475720543562190871181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532317147029041460580787 14298475720543562190871181)
                ·
                  refine ⟨5361928395203835821576693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14298475720543562190871181 5361928395203835821576693)
                  ·
                    refine ⟨502680787050359608272815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5361928395203835821576693 502680787050359608272815)
                    ·
                      rfl

theorem cell22_1468451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_1468451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468451 prefixEnd_1468451 := by exact prefixLift 1468451
  have htrace : WordTrace (prefixWord ++ tailWord_1468451) baseStart_1468451 baseEnd_1468451 := by
    simpa [prefixWord, tailWord_1468451, baseEnd_1468451] using wordTrace_append hprefix tailTrace_1468451
  have hstable : (prefixWord ++ tailWord_1468451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468451).length < 2 ^ (prefixWord ++ tailWord_1468451).sum := by decide
  have hdescent : baseEnd_1468451 < baseStart_1468451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468502 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1468502 : Nat := 118140960795 + 1468502 * 2 ^ 59
def prefixEnd_1468502 : Nat := 4983230072969 + 3 ^ 40 * 1468502 * 2
def baseEnd_1468502 : Nat := 502698245392612475247659

theorem tailTrace_1468502 : CollatzResearch.WordTrace tailWord_1468502 prefixEnd_1468502 502698245392612475247659 := by
  unfold tailWord_1468502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347541757867220563717985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35707112083917019346325173 3347541757867220563717985)
  ·
    refine ⟨2510656318400415422788489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3347541757867220563717985 2510656318400415422788489)
    ·
      refine ⟨1882992238800311567091367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510656318400415422788489 1882992238800311567091367)
      ·
        refine ⟨2824488358200467350637051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882992238800311567091367 2824488358200467350637051)
        ·
          refine ⟨4236732537300701025955577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824488358200467350637051 4236732537300701025955577)
          ·
            refine ⟨3177549402975525769466683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4236732537300701025955577 3177549402975525769466683)
            ·
              refine ⟨4766324104463288654200025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177549402975525769466683 4766324104463288654200025)
              ·
                refine ⟨3574743078347466490650019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766324104463288654200025 3574743078347466490650019)
                ·
                  refine ⟨5362114617521199735975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574743078347466490650019 5362114617521199735975029)
                  ·
                    refine ⟨502698245392612475247659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5362114617521199735975029 502698245392612475247659)
                    ·
                      rfl

theorem cell22_1468502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1468502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468502 prefixEnd_1468502 := by exact prefixLift 1468502
  have htrace : WordTrace (prefixWord ++ tailWord_1468502) baseStart_1468502 baseEnd_1468502 := by
    simpa [prefixWord, tailWord_1468502, baseEnd_1468502] using wordTrace_append hprefix tailTrace_1468502
  have hstable : (prefixWord ++ tailWord_1468502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468502).length < 2 ^ (prefixWord ++ tailWord_1468502).sum := by decide
  have hdescent : baseEnd_1468502 < baseStart_1468502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468571 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 8]
def baseStart_1468571 : Nat := 118140960795 + 1468571 * 2 ^ 59
def prefixEnd_1468571 : Nat := 4983230072969 + 3 ^ 40 * 1468571 * 2
def baseEnd_1468571 : Nat := 167573955167573098424149

theorem tailTrace_1468571 : CollatzResearch.WordTrace tailWord_1468571 prefixEnd_1468571 167573955167573098424149 := by
  unfold tailWord_1468571
  simp only [CollatzResearch.WordTrace]
  refine ⟨53563184762625553803749567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35708789841750369202499711 53563184762625553803749567)
  ·
    refine ⟨80344777143938330705624351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53563184762625553803749567 80344777143938330705624351)
    ·
      refine ⟨120517165715907496058436527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80344777143938330705624351 120517165715907496058436527)
      ·
        refine ⟨180775748573861244087654791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120517165715907496058436527 180775748573861244087654791)
        ·
          refine ⟨271163622860791866131482187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180775748573861244087654791 271163622860791866131482187)
          ·
            refine ⟨406745434291187799197223281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271163622860791866131482187 406745434291187799197223281)
            ·
              refine ⟨305059075718390849397917461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406745434291187799197223281 305059075718390849397917461)
              ·
                refine ⟨14299644174299571065527381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305059075718390849397917461 14299644174299571065527381)
                ·
                  refine ⟨167573955167573098424149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14299644174299571065527381 167573955167573098424149)
                  ·
                    rfl

theorem cell22_1468571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_1468571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468571 prefixEnd_1468571 := by exact prefixLift 1468571
  have htrace : WordTrace (prefixWord ++ tailWord_1468571) baseStart_1468571 baseEnd_1468571 := by
    simpa [prefixWord, tailWord_1468571, baseEnd_1468571] using wordTrace_append hprefix tailTrace_1468571
  have hstable : (prefixWord ++ tailWord_1468571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468571).length < 2 ^ (prefixWord ++ tailWord_1468571).sum := by decide
  have hdescent : baseEnd_1468571 < baseStart_1468571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468618 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1468618 : Nat := 118140960795 + 1468618 * 2 ^ 59
def prefixEnd_1468618 : Nat := 4983230072969 + 3 ^ 40 * 1468618 * 2
def baseEnd_1468618 : Nat := 502737954563226839347303

theorem tailTrace_1468618 : CollatzResearch.WordTrace tailWord_1468618 prefixEnd_1468618 502737954563226839347303 := by
  unfold tailWord_1468618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391224748363820207677627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35709932662303520553807005 13391224748363820207677627)
  ·
    refine ⟨20086837122545730311516441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391224748363820207677627 20086837122545730311516441)
    ·
      refine ⟨15065127841909297733637331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086837122545730311516441 15065127841909297733637331)
      ·
        refine ⟨22597691762863946600455997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065127841909297733637331 22597691762863946600455997)
        ·
          refine ⟨8474134411073979975170999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22597691762863946600455997 8474134411073979975170999)
          ·
            refine ⟨12711201616610969962756499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474134411073979975170999 12711201616610969962756499)
            ·
              refine ⟨19066802424916454944134749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711201616610969962756499 19066802424916454944134749)
              ·
                refine ⟨7150050909343670604050531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19066802424916454944134749 7150050909343670604050531)
                ·
                  refine ⟨10725076364015505906075797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150050909343670604050531 10725076364015505906075797)
                  ·
                    refine ⟨502737954563226839347303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10725076364015505906075797 502737954563226839347303)
                    ·
                      rfl

theorem cell22_1468618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1468618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468618 prefixEnd_1468618 := by exact prefixLift 1468618
  have htrace : WordTrace (prefixWord ++ tailWord_1468618) baseStart_1468618 baseEnd_1468618 := by
    simpa [prefixWord, tailWord_1468618, baseEnd_1468618] using wordTrace_append hprefix tailTrace_1468618
  have hstable : (prefixWord ++ tailWord_1468618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468618).length < 2 ^ (prefixWord ++ tailWord_1468618).sum := by decide
  have hdescent : baseEnd_1468618 < baseStart_1468618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468622 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1468622 : Nat := 118140960795 + 1468622 * 2 ^ 59
def prefixEnd_1468622 : Nat := 4983230072969 + 3 ^ 40 * 1468622 * 2
def baseEnd_1468622 : Nat := 167579774614990720749097

theorem tailTrace_1468622 : CollatzResearch.WordTrace tailWord_1468622 prefixEnd_1468622 167579774614990720749097 := by
  unfold tailWord_1468622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695630610680098689232015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35710029923627193009237413 6695630610680098689232015)
  ·
    refine ⟨10043445916020148033848023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6695630610680098689232015 10043445916020148033848023)
    ·
      refine ⟨15065168874030222050772035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10043445916020148033848023 15065168874030222050772035)
      ·
        refine ⟨22597753311045333076158053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065168874030222050772035 22597753311045333076158053)
        ·
          refine ⟨4237078745820999951779635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22597753311045333076158053 4237078745820999951779635)
          ·
            refine ⟨6355618118731499927669453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237078745820999951779635 6355618118731499927669453)
            ·
              refine ⟨2383356794524312472876045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6355618118731499927669453 2383356794524312472876045)
              ·
                refine ⟨893758797946617177328517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2383356794524312472876045 893758797946617177328517)
                ·
                  refine ⟨167579774614990720749097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 893758797946617177328517 167579774614990720749097)
                  ·
                    rfl

theorem cell22_1468622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1468622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468622 prefixEnd_1468622 := by exact prefixLift 1468622
  have htrace : WordTrace (prefixWord ++ tailWord_1468622) baseStart_1468622 baseEnd_1468622 := by
    simpa [prefixWord, tailWord_1468622, baseEnd_1468622] using wordTrace_append hprefix tailTrace_1468622
  have hstable : (prefixWord ++ tailWord_1468622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468622).length < 2 ^ (prefixWord ++ tailWord_1468622).sum := by decide
  have hdescent : baseEnd_1468622 < baseStart_1468622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468637 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1468637 : Nat := 118140960795 + 1468637 * 2 ^ 59
def prefixEnd_1468637 : Nat := 4983230072969 + 3 ^ 40 * 1468637 * 2
def baseEnd_1468637 : Nat := 502744458651517123122245

theorem tailTrace_1468637 : CollatzResearch.WordTrace tailWord_1468637 prefixEnd_1468637 502744458651517123122245 := by
  unfold tailWord_1468637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53565591980386447075652165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35710394653590964717101443 53565591980386447075652165)
  ·
    refine ⟨10043548496322458826684781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53565591980386447075652165 10043548496322458826684781)
    ·
      refine ⟨3766330686120922060006793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10043548496322458826684781 3766330686120922060006793)
      ·
        refine ⟨2824748014590691545005095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3766330686120922060006793 2824748014590691545005095)
        ·
          refine ⟨4237122021886037317507643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824748014590691545005095 4237122021886037317507643)
          ·
            refine ⟨6355683032829055976261465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237122021886037317507643 6355683032829055976261465)
            ·
              refine ⟨4766762274621791982196099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6355683032829055976261465 4766762274621791982196099)
              ·
                refine ⟨7150143411932687973294149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766762274621791982196099 7150143411932687973294149)
                ·
                  refine ⟨1340651889737378994992653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7150143411932687973294149 1340651889737378994992653)
                  ·
                    refine ⟨502744458651517123122245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340651889737378994992653 502744458651517123122245)
                    ·
                      rfl

theorem cell22_1468637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1468637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468637 prefixEnd_1468637 := by exact prefixLift 1468637
  have htrace : WordTrace (prefixWord ++ tailWord_1468637) baseStart_1468637 baseEnd_1468637 := by
    simpa [prefixWord, tailWord_1468637, baseEnd_1468637] using wordTrace_append hprefix tailTrace_1468637
  have hstable : (prefixWord ++ tailWord_1468637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468637).length < 2 ^ (prefixWord ++ tailWord_1468637).sum := by decide
  have hdescent : baseEnd_1468637 < baseStart_1468637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468695 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 5]
def baseStart_1468695 : Nat := 118140960795 + 1468695 * 2 ^ 59
def prefixEnd_1468695 : Nat := 4983230072969 + 3 ^ 40 * 1468695 * 2
def baseEnd_1468695 : Nat := 167588104412274768390689

theorem tailTrace_1468695 : CollatzResearch.WordTrace tailWord_1468695 prefixEnd_1468695 167588104412274768390689 := by
  unfold tailWord_1468695
  simp only [CollatzResearch.WordTrace]
  refine ⟨53567707414176322981263539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35711804942784215320842359 53567707414176322981263539)
  ·
    refine ⟨80351561121264484471895309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53567707414176322981263539 80351561121264484471895309)
    ·
      refine ⟨30131835420474181676960741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80351561121264484471895309 30131835420474181676960741)
      ·
        refine ⟨5649719141338909064430139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30131835420474181676960741 5649719141338909064430139)
        ·
          refine ⟨8474578712008363596645209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649719141338909064430139 8474578712008363596645209)
          ·
            refine ⟨6355934034006272697483907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8474578712008363596645209 6355934034006272697483907)
            ·
              refine ⟨9533901051009409046225861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355934034006272697483907 9533901051009409046225861)
              ·
                refine ⟨1787606447064264196167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9533901051009409046225861 1787606447064264196167349)
                ·
                  refine ⟨167588104412274768390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787606447064264196167349 167588104412274768390689)
                  ·
                    rfl

theorem cell22_1468695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 5].length) (baseStart_1468695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468695 prefixEnd_1468695 := by exact prefixLift 1468695
  have htrace : WordTrace (prefixWord ++ tailWord_1468695) baseStart_1468695 baseEnd_1468695 := by
    simpa [prefixWord, tailWord_1468695, baseEnd_1468695] using wordTrace_append hprefix tailTrace_1468695
  have hstable : (prefixWord ++ tailWord_1468695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468695).length < 2 ^ (prefixWord ++ tailWord_1468695).sum := by decide
  have hdescent : baseEnd_1468695 < baseStart_1468695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468699 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 1, 3]
def baseStart_1468699 : Nat := 118140960795 + 1468699 * 2 ^ 59
def prefixEnd_1468699 : Nat := 4983230072969 + 3 ^ 40 * 1468699 * 2
def baseEnd_1468699 : Nat := 502765682518569628072055

theorem tailTrace_1468699 : CollatzResearch.WordTrace tailWord_1468699 prefixEnd_1468699 502765682518569628072055 := by
  unfold tailWord_1468699
  simp only [CollatzResearch.WordTrace]
  refine ⟨53567853306161831664409151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35711902204107887776272767 53567853306161831664409151)
  ·
    refine ⟨80351779959242747496613727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53567853306161831664409151 80351779959242747496613727)
    ·
      refine ⟨120527669938864121244920591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80351779959242747496613727 120527669938864121244920591)
      ·
        refine ⟨180791504908296181867380887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120527669938864121244920591 180791504908296181867380887)
        ·
          refine ⟨271187257362444272801071331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180791504908296181867380887 271187257362444272801071331)
          ·
            refine ⟨406780886043666409201606997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271187257362444272801071331 406780886043666409201606997)
            ·
              refine ⟨1191740877081053933207833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 406780886043666409201606997 1191740877081053933207833)
              ·
                refine ⟨893805657810790449905875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191740877081053933207833 893805657810790449905875)
                ·
                  refine ⟨1340708486716185674858813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893805657810790449905875 1340708486716185674858813)
                  ·
                    refine ⟨502765682518569628072055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340708486716185674858813 502765682518569628072055)
                    ·
                      rfl

theorem cell22_1468699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 3].length) (baseStart_1468699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468699 prefixEnd_1468699 := by exact prefixLift 1468699
  have htrace : WordTrace (prefixWord ++ tailWord_1468699) baseStart_1468699 baseEnd_1468699 := by
    simpa [prefixWord, tailWord_1468699, baseEnd_1468699] using wordTrace_append hprefix tailTrace_1468699
  have hstable : (prefixWord ++ tailWord_1468699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468699).length < 2 ^ (prefixWord ++ tailWord_1468699).sum := by decide
  have hdescent : baseEnd_1468699 < baseStart_1468699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468725 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1468725 : Nat := 118140960795 + 1468725 * 2 ^ 59
def prefixEnd_1468725 : Nat := 4983230072969 + 3 ^ 40 * 1468725 * 2
def baseEnd_1468725 : Nat := 502774582849914226921975

theorem tailTrace_1468725 : CollatzResearch.WordTrace tailWord_1468725 prefixEnd_1468725 502774582849914226921975 := by
  unfold tailWord_1468725
  simp only [CollatzResearch.WordTrace]
  refine ⟨53568801604067638104855629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35712534402711758736570419 53568801604067638104855629)
  ·
    refine ⟨20088300601525364289320861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53568801604067638104855629 20088300601525364289320861)
    ·
      refine ⟨7533112725572011608495323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20088300601525364289320861 7533112725572011608495323)
      ·
        refine ⟨11299669088358017412742985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533112725572011608495323 11299669088358017412742985)
        ·
          refine ⟨8474751816268513059557239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11299669088358017412742985 8474751816268513059557239)
          ·
            refine ⟨12712127724402769589335859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474751816268513059557239 12712127724402769589335859)
            ·
              refine ⟨19068191586604154384003789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12712127724402769589335859 19068191586604154384003789)
              ·
                refine ⟨7150571844976557894001421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19068191586604154384003789 7150571844976557894001421)
                ·
                  refine ⟨2681464441866209210250533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7150571844976557894001421 2681464441866209210250533)
                  ·
                    refine ⟨502774582849914226921975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681464441866209210250533 502774582849914226921975)
                    ·
                      rfl

theorem cell22_1468725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1468725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468725 prefixEnd_1468725 := by exact prefixLift 1468725
  have htrace : WordTrace (prefixWord ++ tailWord_1468725) baseStart_1468725 baseEnd_1468725 := by
    simpa [prefixWord, tailWord_1468725, baseEnd_1468725] using wordTrace_append hprefix tailTrace_1468725
  have hstable : (prefixWord ++ tailWord_1468725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468725).length < 2 ^ (prefixWord ++ tailWord_1468725).sum := by decide
  have hdescent : baseEnd_1468725 < baseStart_1468725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468757 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 6]
def baseStart_1468757 : Nat := 118140960795 + 1468757 * 2 ^ 59
def prefixEnd_1468757 : Nat := 4983230072969 + 3 ^ 40 * 1468757 * 2
def baseEnd_1468757 : Nat := 167595179034625603373959

theorem tailTrace_1468757 : CollatzResearch.WordTrace tailWord_1468757 prefixEnd_1468757 167595179034625603373959 := by
  unfold tailWord_1468757
  simp only [CollatzResearch.WordTrace]
  refine ⟨53569968739951707570020525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35713312493301138380013683 53569968739951707570020525)
  ·
    refine ⟨20088738277481890338757697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53569968739951707570020525 20088738277481890338757697)
    ·
      refine ⟨15066553708111417754068273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20088738277481890338757697 15066553708111417754068273)
      ·
        refine ⟨11299915281083563315551205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15066553708111417754068273 11299915281083563315551205)
        ·
          refine ⟨2118734115203168121665851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11299915281083563315551205 2118734115203168121665851)
          ·
            refine ⟨3178101172804752182498777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118734115203168121665851 3178101172804752182498777)
            ·
              refine ⟨2383575879603564136874083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178101172804752182498777 2383575879603564136874083)
              ·
                refine ⟨3575363819405346205311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383575879603564136874083 3575363819405346205311125)
                ·
                  refine ⟨167595179034625603373959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3575363819405346205311125 167595179034625603373959)
                  ·
                    rfl

theorem cell22_1468757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_1468757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468757 prefixEnd_1468757 := by exact prefixLift 1468757
  have htrace : WordTrace (prefixWord ++ tailWord_1468757) baseStart_1468757 baseEnd_1468757 := by
    simpa [prefixWord, tailWord_1468757, baseEnd_1468757] using wordTrace_append hprefix tailTrace_1468757
  have hstable : (prefixWord ++ tailWord_1468757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468757).length < 2 ^ (prefixWord ++ tailWord_1468757).sum := by decide
  have hdescent : baseEnd_1468757 < baseStart_1468757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468868 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1468868 : Nat := 118140960795 + 1468868 * 2 ^ 59
def prefixEnd_1468868 : Nat := 4983230072969 + 3 ^ 40 * 1468868 * 2
def baseEnd_1468868 : Nat := 502823534672309520596537

theorem tailTrace_1468868 : CollatzResearch.WordTrace tailWord_1468868 prefixEnd_1468868 502823534672309520596537 := by
  unfold tailWord_1468868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787008621274786763655629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35716011495033049018207505 26787008621274786763655629)
  ·
    refine ⟨10045128232978045036370861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26787008621274786763655629 10045128232978045036370861)
    ·
      refine ⟨3766923087366766888639073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10045128232978045036370861 3766923087366766888639073)
      ·
        refine ⟨2825192315525075166479305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3766923087366766888639073 2825192315525075166479305)
        ·
          refine ⟨2118894236643806374859479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825192315525075166479305 2118894236643806374859479)
          ·
            refine ⟨3178341354965709562289219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118894236643806374859479 3178341354965709562289219)
            ·
              refine ⟨4767512032448564343433829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178341354965709562289219 4767512032448564343433829)
              ·
                refine ⟨893908506084105814393843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4767512032448564343433829 893908506084105814393843)
                ·
                  refine ⟨1340862759126158721590765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893908506084105814393843 1340862759126158721590765)
                  ·
                    refine ⟨502823534672309520596537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340862759126158721590765 502823534672309520596537)
                    ·
                      rfl

theorem cell22_1468868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1468868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468868 prefixEnd_1468868 := by exact prefixLift 1468868
  have htrace : WordTrace (prefixWord ++ tailWord_1468868) baseStart_1468868 baseEnd_1468868 := by
    simpa [prefixWord, tailWord_1468868, baseEnd_1468868] using wordTrace_append hprefix tailTrace_1468868
  have hstable : (prefixWord ++ tailWord_1468868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468868).length < 2 ^ (prefixWord ++ tailWord_1468868).sum := by decide
  have hdescent : baseEnd_1468868 < baseStart_1468868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468875 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 6]
def baseStart_1468875 : Nat := 118140960795 + 1468875 * 2 ^ 59
def prefixEnd_1468875 : Nat := 4983230072969 + 3 ^ 40 * 1468875 * 2
def baseEnd_1468875 : Nat := 167608643638454611890505

theorem tailTrace_1468875 : CollatzResearch.WordTrace tailWord_1468875 prefixEnd_1468875 167608643638454611890505 := by
  unfold tailWord_1468875
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574272553524213722816079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35716181702349475815210719 53574272553524213722816079)
  ·
    refine ⟨80361408830286320584224119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53574272553524213722816079 80361408830286320584224119)
    ·
      refine ⟨120542113245429480876336179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80361408830286320584224119 120542113245429480876336179)
      ·
        refine ⟨180813169868144221314504269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120542113245429480876336179 180813169868144221314504269)
        ·
          refine ⟨67804938700554082992939101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180813169868144221314504269 67804938700554082992939101)
          ·
            refine ⟨25426852012707781122352163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67804938700554082992939101 25426852012707781122352163)
            ·
              refine ⟨38140278019061671683528245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25426852012707781122352163 38140278019061671683528245)
              ·
                refine ⟨3575651064287031720330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38140278019061671683528245 3575651064287031720330773)
                ·
                  refine ⟨167608643638454611890505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3575651064287031720330773 167608643638454611890505)
                  ·
                    rfl

theorem cell22_1468875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_1468875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468875 prefixEnd_1468875 := by exact prefixLift 1468875
  have htrace : WordTrace (prefixWord ++ tailWord_1468875) baseStart_1468875 baseEnd_1468875 := by
    simpa [prefixWord, tailWord_1468875, baseEnd_1468875] using wordTrace_append hprefix tailTrace_1468875
  have hstable : (prefixWord ++ tailWord_1468875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468875).length < 2 ^ (prefixWord ++ tailWord_1468875).sum := by decide
  have hdescent : baseEnd_1468875 < baseStart_1468875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468907 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 4, 3]
def baseStart_1468907 : Nat := 118140960795 + 1468907 * 2 ^ 59
def prefixEnd_1468907 : Nat := 4983230072969 + 3 ^ 40 * 1468907 * 2
def baseEnd_1468907 : Nat := 502836885169326418871417

theorem tailTrace_1468907 : CollatzResearch.WordTrace tailWord_1468907 prefixEnd_1468907 502836885169326418871417 := by
  unfold tailWord_1468907
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575439689408283187980975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35716959792938855458653983 53575439689408283187980975)
  ·
    refine ⟨80363159534112424781971463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53575439689408283187980975 80363159534112424781971463)
    ·
      refine ⟨120544739301168637172957195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80363159534112424781971463 120544739301168637172957195)
      ·
        refine ⟨180817108951752955759435793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120544739301168637172957195 180817108951752955759435793)
        ·
          refine ⟨135612831713814716819576845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180817108951752955759435793 135612831713814716819576845)
          ·
            refine ⟨50854811892680518807341317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135612831713814716819576845 50854811892680518807341317)
            ·
              refine ⟨9535277229877597276376497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50854811892680518807341317 9535277229877597276376497)
              ·
                refine ⟨7151457922408197957282373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9535277229877597276376497 7151457922408197957282373)
                ·
                  refine ⟨1340898360451537116990445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7151457922408197957282373 1340898360451537116990445)
                  ·
                    refine ⟨502836885169326418871417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340898360451537116990445 502836885169326418871417)
                    ·
                      rfl

theorem cell22_1468907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].length) (baseStart_1468907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468907 prefixEnd_1468907 := by exact prefixLift 1468907
  have htrace : WordTrace (prefixWord ++ tailWord_1468907) baseStart_1468907 baseEnd_1468907 := by
    simpa [prefixWord, tailWord_1468907, baseEnd_1468907] using wordTrace_append hprefix tailTrace_1468907
  have hstable : (prefixWord ++ tailWord_1468907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468907).length < 2 ^ (prefixWord ++ tailWord_1468907).sum := by decide
  have hdescent : baseEnd_1468907 < baseStart_1468907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468920 : List Nat := [2, 1, 2, 1, 1, 4, 11]
def baseStart_1468920 : Nat := 118140960795 + 1468920 * 2 ^ 59
def prefixEnd_1468920 : Nat := 4983230072969 + 3 ^ 40 * 1468920 * 2
def baseEnd_1468920 : Nat := 18623753160555508085051

theorem tailTrace_1468920 : CollatzResearch.WordTrace tailWord_1468920 prefixEnd_1468920 18623753160555508085051 := by
  unfold tailWord_1468920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787956919180593204102107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35717275892240790938802809 26787956919180593204102107)
  ·
    refine ⟨40181935378770889806153161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26787956919180593204102107 40181935378770889806153161)
    ·
      refine ⟨30136451534078167354614871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40181935378770889806153161 30136451534078167354614871)
      ·
        refine ⟨45204677301117251031922307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30136451534078167354614871 45204677301117251031922307)
        ·
          refine ⟨67807015951675876547883461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45204677301117251031922307 67807015951675876547883461)
          ·
            refine ⟨12713815490939226852728149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67807015951675876547883461 12713815490939226852728149)
            ·
              refine ⟨18623753160555508085051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12713815490939226852728149 18623753160555508085051)
              ·
                rfl

theorem cell22_1468920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 11].length) (baseStart_1468920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468920 prefixEnd_1468920 := by exact prefixLift 1468920
  have htrace : WordTrace (prefixWord ++ tailWord_1468920) baseStart_1468920 baseEnd_1468920 := by
    simpa [prefixWord, tailWord_1468920, baseEnd_1468920] using wordTrace_append hprefix tailTrace_1468920
  have hstable : (prefixWord ++ tailWord_1468920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468920).length < 2 ^ (prefixWord ++ tailWord_1468920).sum := by decide
  have hdescent : baseEnd_1468920 < baseStart_1468920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468986 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_1468986 : Nat := 118140960795 + 1468986 * 2 ^ 59
def prefixEnd_1468986 : Nat := 4983230072969 + 3 ^ 40 * 1468986 * 2
def baseEnd_1468986 : Nat := 502863928483796546146175

theorem tailTrace_1468986 : CollatzResearch.WordTrace tailWord_1468986 prefixEnd_1468986 502863928483796546146175 := by
  unfold tailWord_1468986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394580264030519920026703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35718880704081386453404541 13394580264030519920026703)
  ·
    refine ⟨20091870396045779880040055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13394580264030519920026703 20091870396045779880040055)
    ·
      refine ⟨30137805594068669820060083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20091870396045779880040055 30137805594068669820060083)
      ·
        refine ⟨45206708391103004730090125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30137805594068669820060083 45206708391103004730090125)
        ·
          refine ⟨16952515646663626773783797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45206708391103004730090125 16952515646663626773783797)
          ·
            refine ⟨1589298341874715010042231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16952515646663626773783797 1589298341874715010042231)
            ·
              refine ⟨2383947512812072515063347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589298341874715010042231 2383947512812072515063347)
              ·
                refine ⟨3575921269218108772595021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383947512812072515063347 3575921269218108772595021)
                ·
                  refine ⟨1340970475956790789723133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3575921269218108772595021 1340970475956790789723133)
                  ·
                    refine ⟨502863928483796546146175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340970475956790789723133 502863928483796546146175)
                    ·
                      rfl

theorem cell22_1468986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_1468986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468986 prefixEnd_1468986 := by exact prefixLift 1468986
  have htrace : WordTrace (prefixWord ++ tailWord_1468986) baseStart_1468986 baseEnd_1468986 := by
    simpa [prefixWord, tailWord_1468986, baseEnd_1468986] using wordTrace_append hprefix tailTrace_1468986
  have hstable : (prefixWord ++ tailWord_1468986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468986).length < 2 ^ (prefixWord ++ tailWord_1468986).sum := by decide
  have hdescent : baseEnd_1468986 < baseStart_1468986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468999 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 5]
def baseStart_1468999 : Nat := 118140960795 + 1468999 * 2 ^ 59
def prefixEnd_1468999 : Nat := 4983230072969 + 3 ^ 40 * 1468999 * 2
def baseEnd_1468999 : Nat := 167622792883156281857045

theorem tailTrace_1468999 : CollatzResearch.WordTrace tailWord_1468999 prefixEnd_1468999 167622792883156281857045 := by
  unfold tailWord_1468999
  simp only [CollatzResearch.WordTrace]
  refine ⟨53578795205074982900330051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35719196803383321933553367 53578795205074982900330051)
  ·
    refine ⟨80368192807612474350495077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53578795205074982900330051 80368192807612474350495077)
    ·
      refine ⟨15069036151427338940717827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80368192807612474350495077 15069036151427338940717827)
      ·
        refine ⟨22603554227141008411076741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15069036151427338940717827 22603554227141008411076741)
        ·
          refine ⟨4238166417588939077076889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22603554227141008411076741 4238166417588939077076889)
          ·
            refine ⟨3178624813191704307807667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238166417588939077076889 3178624813191704307807667)
            ·
              refine ⟨4767937219787556461711501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178624813191704307807667 4767937219787556461711501)
              ·
                refine ⟨1787976457420333673141813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767937219787556461711501 1787976457420333673141813)
                ·
                  refine ⟨167622792883156281857045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787976457420333673141813 167622792883156281857045)
                  ·
                    rfl

theorem cell22_1468999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].length) (baseStart_1468999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1468999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1468999 prefixEnd_1468999 := by exact prefixLift 1468999
  have htrace : WordTrace (prefixWord ++ tailWord_1468999) baseStart_1468999 baseEnd_1468999 := by
    simpa [prefixWord, tailWord_1468999, baseEnd_1468999] using wordTrace_append hprefix tailTrace_1468999
  have hstable : (prefixWord ++ tailWord_1468999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468999).length < 2 ^ (prefixWord ++ tailWord_1468999).sum := by decide
  have hdescent : baseEnd_1468999 < baseStart_1468999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469076 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1469076 : Nat := 118140960795 + 1469076 * 2 ^ 59
def prefixEnd_1469076 : Nat := 4983230072969 + 3 ^ 40 * 1469076 * 2
def baseEnd_1469076 : Nat := 502894737323066311395899

theorem tailTrace_1469076 : CollatzResearch.WordTrace tailWord_1469076 prefixEnd_1469076 502894737323066311395899 := by
  unfold tailWord_1469076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26790801812898012525441541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35721069083864016700588721 26790801812898012525441541)
  ·
    refine ⟨5023275339918377348520289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26790801812898012525441541 5023275339918377348520289)
    ·
      refine ⟨3767456504938783011390217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5023275339918377348520289 3767456504938783011390217)
      ·
        refine ⟨2825592378704087258542663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3767456504938783011390217 2825592378704087258542663)
        ·
          refine ⟨4238388568056130887813995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825592378704087258542663 4238388568056130887813995)
          ·
            refine ⟨6357582852084196331720993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238388568056130887813995 6357582852084196331720993)
            ·
              refine ⟨4768187139063147248790745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6357582852084196331720993 4768187139063147248790745)
              ·
                refine ⟨3576140354297360436593059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4768187139063147248790745 3576140354297360436593059)
                ·
                  refine ⟨5364210531446040654889589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576140354297360436593059 5364210531446040654889589)
                  ·
                    refine ⟨502894737323066311395899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5364210531446040654889589 502894737323066311395899)
                    ·
                      rfl

theorem cell22_1469076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1469076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469076 prefixEnd_1469076 := by exact prefixLift 1469076
  have htrace : WordTrace (prefixWord ++ tailWord_1469076) baseStart_1469076 baseEnd_1469076 := by
    simpa [prefixWord, tailWord_1469076, baseEnd_1469076] using wordTrace_append hprefix tailTrace_1469076
  have hstable : (prefixWord ++ tailWord_1469076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469076).length < 2 ^ (prefixWord ++ tailWord_1469076).sum := by decide
  have hdescent : baseEnd_1469076 < baseStart_1469076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469089 : List Nat := [1, 2, 3, 3, 3, 1, 9]
def baseStart_1469089 : Nat := 118140960795 + 1469089 * 2 ^ 59
def prefixEnd_1469089 : Nat := 4983230072969 + 3 ^ 40 * 1469089 * 2
def baseEnd_1469089 : Nat := 18625895832916244845217

theorem tailTrace_1469089 : CollatzResearch.WordTrace tailWord_1469089 prefixEnd_1469089 18625895832916244845217 := by
  unfold tailWord_1469089
  simp only [CollatzResearch.WordTrace]
  refine ⟨53582077774748928271106321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35721385183165952180737547 53582077774748928271106321)
  ·
    refine ⟨40186558331061696203329741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53582077774748928271106321 40186558331061696203329741)
    ·
      refine ⟨15069959374148136076248653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40186558331061696203329741 15069959374148136076248653)
      ·
        refine ⟨5651234765305551028593245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15069959374148136076248653 5651234765305551028593245)
        ·
          refine ⟨2119213036989581635722467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5651234765305551028593245 2119213036989581635722467)
          ·
            refine ⟨3178819555484372453583701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119213036989581635722467 3178819555484372453583701)
            ·
              refine ⟨18625895832916244845217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3178819555484372453583701 18625895832916244845217)
              ·
                rfl

theorem cell22_1469089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 9].length) (baseStart_1469089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469089 prefixEnd_1469089 := by exact prefixLift 1469089
  have htrace : WordTrace (prefixWord ++ tailWord_1469089) baseStart_1469089 baseEnd_1469089 := by
    simpa [prefixWord, tailWord_1469089, baseEnd_1469089] using wordTrace_append hprefix tailTrace_1469089
  have hstable : (prefixWord ++ tailWord_1469089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469089).length < 2 ^ (prefixWord ++ tailWord_1469089).sum := by decide
  have hdescent : baseEnd_1469089 < baseStart_1469089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469110 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1469110 : Nat := 118140960795 + 1469110 * 2 ^ 59
def prefixEnd_1469110 : Nat := 4983230072969 + 3 ^ 40 * 1469110 * 2
def baseEnd_1469110 : Nat := 502906376217901556045795

theorem tailTrace_1469110 : CollatzResearch.WordTrace tailWord_1469110 prefixEnd_1469110 502906376217901556045795 := by
  unfold tailWord_1469110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348927731729553053601299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35721895805115232571747189 3348927731729553053601299)
  ·
    refine ⟨5023391597594329580401949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348927731729553053601299 5023391597594329580401949)
    ·
      refine ⟨1883771849097873592650731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5023391597594329580401949 1883771849097873592650731)
      ·
        refine ⟨2825657773646810388976097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883771849097873592650731 2825657773646810388976097)
        ·
          refine ⟨2119243330235107791732073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825657773646810388976097 2119243330235107791732073)
          ·
            refine ⟨1589432497676330843799055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119243330235107791732073 1589432497676330843799055)
            ·
              refine ⟨2384148746514496265698583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589432497676330843799055 2384148746514496265698583)
              ·
                refine ⟨3576223119771744398547875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384148746514496265698583 3576223119771744398547875)
                ·
                  refine ⟨5364334679657616597821813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576223119771744398547875 5364334679657616597821813)
                  ·
                    refine ⟨502906376217901556045795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5364334679657616597821813 502906376217901556045795)
                    ·
                      rfl

theorem cell22_1469110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1469110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469110 prefixEnd_1469110 := by exact prefixLift 1469110
  have htrace : WordTrace (prefixWord ++ tailWord_1469110) baseStart_1469110 baseEnd_1469110 := by
    simpa [prefixWord, tailWord_1469110, baseEnd_1469110] using wordTrace_append hprefix tailTrace_1469110
  have hstable : (prefixWord ++ tailWord_1469110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469110).length < 2 ^ (prefixWord ++ tailWord_1469110).sum := by decide
  have hdescent : baseEnd_1469110 < baseStart_1469110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469134 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1469134 : Nat := 118140960795 + 1469134 * 2 ^ 59
def prefixEnd_1469134 : Nat := 4983230072969 + 3 ^ 40 * 1469134 * 2
def baseEnd_1469134 : Nat := 167638197302791164481907

theorem tailTrace_1469134 : CollatzResearch.WordTrace tailWord_1469134 prefixEnd_1469134 167638197302791164481907 := by
  unfold tailWord_1469134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697964882448237619561807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35722479373057267304329637 6697964882448237619561807)
  ·
    refine ⟨10046947323672356429342711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6697964882448237619561807 10046947323672356429342711)
    ·
      refine ⟨15070420985508534644014067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10046947323672356429342711 15070420985508534644014067)
      ·
        refine ⟨22605631478262801966021101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15070420985508534644014067 22605631478262801966021101)
        ·
          refine ⟨8477111804348550737257913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22605631478262801966021101 8477111804348550737257913)
          ·
            refine ⟨6357833853261413052943435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8477111804348550737257913 6357833853261413052943435)
            ·
              refine ⟨9536750779892119579415153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357833853261413052943435 9536750779892119579415153)
              ·
                refine ⟨7152563084919089684561365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9536750779892119579415153 7152563084919089684561365)
                ·
                  refine ⟨167638197302791164481907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7152563084919089684561365 167638197302791164481907)
                  ·
                    rfl

theorem cell22_1469134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1469134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469134 prefixEnd_1469134 := by exact prefixLift 1469134
  have htrace : WordTrace (prefixWord ++ tailWord_1469134) baseStart_1469134 baseEnd_1469134 := by
    simpa [prefixWord, tailWord_1469134, baseEnd_1469134] using wordTrace_append hprefix tailTrace_1469134
  have hstable : (prefixWord ++ tailWord_1469134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469134).length < 2 ^ (prefixWord ++ tailWord_1469134).sum := by decide
  have hdescent : baseEnd_1469134 < baseStart_1469134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469164 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1469164 : Nat := 118140960795 + 1469164 * 2 ^ 59
def prefixEnd_1469164 : Nat := 4983230072969 + 3 ^ 40 * 1469164 * 2
def baseEnd_1469164 : Nat := 502924861521463415195629

theorem tailTrace_1469164 : CollatzResearch.WordTrace tailWord_1469164 prefixEnd_1469164 502924861521463415195629 := by
  unfold tailWord_1469164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792406624738608040043273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35723208832984810720057697 26792406624738608040043273)
  ·
    refine ⟨20094304968553956030032455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26792406624738608040043273 20094304968553956030032455)
    ·
      refine ⟨30141457452830934045048683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20094304968553956030032455 30141457452830934045048683)
      ·
        refine ⟨45212186179246401067573025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30141457452830934045048683 45212186179246401067573025)
        ·
          refine ⟨33909139634434800800679769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45212186179246401067573025 33909139634434800800679769)
          ·
            refine ⟨25431854725826100600509827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33909139634434800800679769 25431854725826100600509827)
            ·
              refine ⟨38147782088739150900764741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25431854725826100600509827 38147782088739150900764741)
              ·
                refine ⟨7152709141638590793893389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38147782088739150900764741 7152709141638590793893389)
                ·
                  refine ⟨2682265928114471547710021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7152709141638590793893389 2682265928114471547710021)
                  ·
                    refine ⟨502924861521463415195629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682265928114471547710021 502924861521463415195629)
                    ·
                      rfl

theorem cell22_1469164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1469164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469164 prefixEnd_1469164 := by exact prefixLift 1469164
  have htrace : WordTrace (prefixWord ++ tailWord_1469164) baseStart_1469164 baseEnd_1469164 := by
    simpa [prefixWord, tailWord_1469164, baseEnd_1469164] using wordTrace_append hprefix tailTrace_1469164
  have hstable : (prefixWord ++ tailWord_1469164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469164).length < 2 ^ (prefixWord ++ tailWord_1469164).sum := by decide
  have hdescent : baseEnd_1469164 < baseStart_1469164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469196 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_1469196 : Nat := 118140960795 + 1469196 * 2 ^ 59
def prefixEnd_1469196 : Nat := 4983230072969 + 3 ^ 40 * 1469196 * 2
def baseEnd_1469196 : Nat := 167645271925141999465177

theorem tailTrace_1469196 : CollatzResearch.WordTrace tailWord_1469196 prefixEnd_1469196 167645271925141999465177 := by
  unfold tailWord_1469196
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792990192680642772625721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35723986923574190363500961 26792990192680642772625721)
  ·
    refine ⟨20094742644510482079469291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26792990192680642772625721 20094742644510482079469291)
    ·
      refine ⟨30142113966765723119203937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20094742644510482079469291 30142113966765723119203937)
      ·
        refine ⟨22606585475074292339402953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30142113966765723119203937 22606585475074292339402953)
        ·
          refine ⟨16954939106305719254552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22606585475074292339402953 16954939106305719254552215)
          ·
            refine ⟨25432408659458578881828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954939106305719254552215 25432408659458578881828323)
            ·
              refine ⟨38148612989187868322742485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25432408659458578881828323 38148612989187868322742485)
              ·
                refine ⟨894108116934090663814277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38148612989187868322742485 894108116934090663814277)
                ·
                  refine ⟨167645271925141999465177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894108116934090663814277 167645271925141999465177)
                  ·
                    rfl

theorem cell22_1469196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_1469196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469196 prefixEnd_1469196 := by exact prefixLift 1469196
  have htrace : WordTrace (prefixWord ++ tailWord_1469196) baseStart_1469196 baseEnd_1469196 := by
    simpa [prefixWord, tailWord_1469196, baseEnd_1469196] using wordTrace_append hprefix tailTrace_1469196
  have hstable : (prefixWord ++ tailWord_1469196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469196).length < 2 ^ (prefixWord ++ tailWord_1469196).sum := by decide
  have hdescent : baseEnd_1469196 < baseStart_1469196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_1469209 : Nat := 118140960795 + 1469209 * 2 ^ 59
def prefixEnd_1469209 : Nat := 4983230072969 + 3 ^ 40 * 1469209 * 2
def baseEnd_1469209 : Nat := 502940265941098297820491

theorem tailTrace_1469209 : CollatzResearch.WordTrace tailWord_1469209 prefixEnd_1469209 502940265941098297820491 := by
  unfold tailWord_1469209
  simp only [CollatzResearch.WordTrace]
  refine ⟨53586454534314188765474681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35724303022876125843649787 53586454534314188765474681)
  ·
    refine ⟨40189840900735641574106011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53586454534314188765474681 40189840900735641574106011)
    ·
      refine ⟨60284761351103462361159017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40189840900735641574106011 60284761351103462361159017)
      ·
        refine ⟨45213571013327596770869263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60284761351103462361159017 45213571013327596770869263)
        ·
          refine ⟨67820356519991395156303895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45213571013327596770869263 67820356519991395156303895)
          ·
            refine ⟨101730534779987092734455843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67820356519991395156303895 101730534779987092734455843)
            ·
              refine ⟨152595802169980639101683765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101730534779987092734455843 152595802169980639101683765)
              ·
                refine ⟨14305856453435684915782853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152595802169980639101683765 14305856453435684915782853)
                ·
                  refine ⟨2682348085019190921709285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14305856453435684915782853 2682348085019190921709285)
                  ·
                    refine ⟨502940265941098297820491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682348085019190921709285 502940265941098297820491)
                    ·
                      rfl

theorem cell22_1469209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_1469209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469209 prefixEnd_1469209 := by exact prefixLift 1469209
  have htrace : WordTrace (prefixWord ++ tailWord_1469209) baseStart_1469209 baseEnd_1469209 := by
    simpa [prefixWord, tailWord_1469209, baseEnd_1469209] using wordTrace_append hprefix tailTrace_1469209
  have hstable : (prefixWord ++ tailWord_1469209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469209).length < 2 ^ (prefixWord ++ tailWord_1469209).sum := by decide
  have hdescent : baseEnd_1469209 < baseStart_1469209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469249 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1469249 : Nat := 118140960795 + 1469249 * 2 ^ 59
def prefixEnd_1469249 : Nat := 4983230072969 + 3 ^ 40 * 1469249 * 2
def baseEnd_1469249 : Nat := 502953958758551526820369

theorem tailTrace_1469249 : CollatzResearch.WordTrace tailWord_1469249 prefixEnd_1469249 502953958758551526820369 := by
  unfold tailWord_1469249
  simp only [CollatzResearch.WordTrace]
  refine ⟨53587913454169275596930801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35725275636112850397953867 53587913454169275596930801)
  ·
    refine ⟨40190935090626956697698101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53587913454169275596930801 40190935090626956697698101)
    ·
      refine ⟨3767900164746277190409197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40190935090626956697698101 3767900164746277190409197)
      ·
        refine ⟨1412962561779853946403449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3767900164746277190409197 1412962561779853946403449)
        ·
          refine ⟨1059721921334890459802587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412962561779853946403449 1059721921334890459802587)
          ·
            refine ⟨1589582882002335689703881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059721921334890459802587 1589582882002335689703881)
            ·
              refine ⟨1192187161501751767277911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589582882002335689703881 1192187161501751767277911)
              ·
                refine ⟨1788280742252627650916867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192187161501751767277911 1788280742252627650916867)
                ·
                  refine ⟨2682421113378941476375301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788280742252627650916867 2682421113378941476375301)
                  ·
                    refine ⟨502953958758551526820369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682421113378941476375301 502953958758551526820369)
                    ·
                      rfl

theorem cell22_1469249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1469249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469249 prefixEnd_1469249 := by exact prefixLift 1469249
  have htrace : WordTrace (prefixWord ++ tailWord_1469249) baseStart_1469249 baseEnd_1469249 := by
    simpa [prefixWord, tailWord_1469249, baseEnd_1469249] using wordTrace_append hprefix tailTrace_1469249
  have hstable : (prefixWord ++ tailWord_1469249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469249).length < 2 ^ (prefixWord ++ tailWord_1469249).sum := by decide
  have hdescent : baseEnd_1469249 < baseStart_1469249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469256 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1469256 : Nat := 118140960795 + 1469256 * 2 ^ 59
def prefixEnd_1469256 : Nat := 4983230072969 + 3 ^ 40 * 1469256 * 2
def baseEnd_1469256 : Nat := 502956355001605841895347

theorem tailTrace_1469256 : CollatzResearch.WordTrace tailWord_1469256 prefixEnd_1469256 502956355001605841895347 := by
  unfold tailWord_1469256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26794084382571957896217811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35725445843429277194957081 26794084382571957896217811)
  ·
    refine ⟨40191126573857936844326717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26794084382571957896217811 40191126573857936844326717)
    ·
      refine ⟨15071672465196726316622519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40191126573857936844326717 15071672465196726316622519)
      ·
        refine ⟨22607508697795089474933779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15071672465196726316622519 22607508697795089474933779)
        ·
          refine ⟨33911263046692634212400669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22607508697795089474933779 33911263046692634212400669)
          ·
            refine ⟨12716723642509737829650251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33911263046692634212400669 12716723642509737829650251)
            ·
              refine ⟨19075085463764606744475377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12716723642509737829650251 19075085463764606744475377)
              ·
                refine ⟨14306314097823455058356533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19075085463764606744475377 14306314097823455058356533)
                ·
                  refine ⟨1341216946670948911720925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14306314097823455058356533 1341216946670948911720925)
                  ·
                    refine ⟨502956355001605841895347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341216946670948911720925 502956355001605841895347)
                    ·
                      rfl

theorem cell22_1469256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1469256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469256 prefixEnd_1469256 := by exact prefixLift 1469256
  have htrace : WordTrace (prefixWord ++ tailWord_1469256) baseStart_1469256 baseEnd_1469256 := by
    simpa [prefixWord, tailWord_1469256, baseEnd_1469256] using wordTrace_append hprefix tailTrace_1469256
  have hstable : (prefixWord ++ tailWord_1469256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469256).length < 2 ^ (prefixWord ++ tailWord_1469256).sum := by decide
  have hdescent : baseEnd_1469256 < baseStart_1469256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469273 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_1469273 : Nat := 118140960795 + 1469273 * 2 ^ 59
def prefixEnd_1469273 : Nat := 4983230072969 + 3 ^ 40 * 1469273 * 2
def baseEnd_1469273 : Nat := 502962174449023464220295

theorem tailTrace_1469273 : CollatzResearch.WordTrace tailWord_1469273 prefixEnd_1469273 502962174449023464220295 := by
  unfold tailWord_1469273
  simp only [CollatzResearch.WordTrace]
  refine ⟨53588788806082327695804473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35725859204054885130536315 53588788806082327695804473)
  ·
    refine ⟨40191591604561745771853355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53588788806082327695804473 40191591604561745771853355)
    ·
      refine ⟨60287387406842618657780033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40191591604561745771853355 60287387406842618657780033)
      ·
        refine ⟨45215540555131963993335025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60287387406842618657780033 45215540555131963993335025)
        ·
          refine ⟨33911655416348972995001269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45215540555131963993335025 33911655416348972995001269)
          ·
            refine ⟨3179217695282716218281369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33911655416348972995001269 3179217695282716218281369)
            ·
              refine ⟨2384413271462037163711027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179217695282716218281369 2384413271462037163711027)
              ·
                refine ⟨3576619907193055745566541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384413271462037163711027 3576619907193055745566541)
                ·
                  refine ⟨1341232465197395904587453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3576619907193055745566541 1341232465197395904587453)
                  ·
                    refine ⟨502962174449023464220295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341232465197395904587453 502962174449023464220295)
                    ·
                      rfl

theorem cell22_1469273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_1469273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469273 prefixEnd_1469273 := by exact prefixLift 1469273
  have htrace : WordTrace (prefixWord ++ tailWord_1469273) baseStart_1469273 baseEnd_1469273 := by
    simpa [prefixWord, tailWord_1469273, baseEnd_1469273] using wordTrace_append hprefix tailTrace_1469273
  have hstable : (prefixWord ++ tailWord_1469273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469273).length < 2 ^ (prefixWord ++ tailWord_1469273).sum := by decide
  have hdescent : baseEnd_1469273 < baseStart_1469273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1469316 : Nat := 118140960795 + 1469316 * 2 ^ 59
def prefixEnd_1469316 : Nat := 4983230072969 + 3 ^ 40 * 1469316 * 2
def baseEnd_1469316 : Nat := 502976894227785685395163

theorem tailTrace_1469316 : CollatzResearch.WordTrace tailWord_1469316 prefixEnd_1469316 502976894227785685395163 := by
  unfold tailWord_1469316
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795178572463273019809901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35726904763284364026413201 26795178572463273019809901)
  ·
    refine ⟨10048191964673727382428713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26795178572463273019809901 10048191964673727382428713)
    ·
      refine ⟨7536143973505295536821535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10048191964673727382428713 7536143973505295536821535)
      ·
        refine ⟨11304215960257943305232303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536143973505295536821535 11304215960257943305232303)
        ·
          refine ⟨16956323940386914957848455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304215960257943305232303 16956323940386914957848455)
          ·
            refine ⟨25434485910580372436772683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16956323940386914957848455 25434485910580372436772683)
            ·
              refine ⟨38151728865870558655159025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25434485910580372436772683 38151728865870558655159025)
              ·
                refine ⟨28613796649402918991369269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38151728865870558655159025 28613796649402918991369269)
                ·
                  refine ⟨2682543435881523655440869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28613796649402918991369269 2682543435881523655440869)
                  ·
                    refine ⟨502976894227785685395163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682543435881523655440869 502976894227785685395163)
                    ·
                      rfl

theorem cell22_1469316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1469316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469316 prefixEnd_1469316 := by exact prefixLift 1469316
  have htrace : WordTrace (prefixWord ++ tailWord_1469316) baseStart_1469316 baseEnd_1469316 := by
    simpa [prefixWord, tailWord_1469316, baseEnd_1469316] using wordTrace_append hprefix tailTrace_1469316
  have hstable : (prefixWord ++ tailWord_1469316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469316).length < 2 ^ (prefixWord ++ tailWord_1469316).sum := by decide
  have hdescent : baseEnd_1469316 < baseStart_1469316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469500 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1469500 : Nat := 118140960795 + 1469500 * 2 ^ 59
def prefixEnd_1469500 : Nat := 4983230072969 + 3 ^ 40 * 1469500 * 2
def baseEnd_1469500 : Nat := 167679960396023512931533

theorem tailTrace_1469500 : CollatzResearch.WordTrace tailWord_1469500 prefixEnd_1469500 167679960396023512931533 := by
  unfold tailWord_1469500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798534088129972732158977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35731378784173296976211969 26798534088129972732158977)
  ·
    refine ⟨20098900566097479549119233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26798534088129972732158977 20098900566097479549119233)
    ·
      refine ⟨15074175424573109661839425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20098900566097479549119233 15074175424573109661839425)
      ·
        refine ⟨11305631568429832246379569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15074175424573109661839425 11305631568429832246379569)
        ·
          refine ⟨8479223676322374184784677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11305631568429832246379569 8479223676322374184784677)
          ·
            refine ⟨1589854439310445159647127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8479223676322374184784677 1589854439310445159647127)
            ·
              refine ⟨2384781658965667739470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589854439310445159647127 2384781658965667739470691)
              ·
                refine ⟨3577172488448501609206037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384781658965667739470691 3577172488448501609206037)
                ·
                  refine ⟨167679960396023512931533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3577172488448501609206037 167679960396023512931533)
                  ·
                    rfl

theorem cell22_1469500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1469500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469500 prefixEnd_1469500 := by exact prefixLift 1469500
  have htrace : WordTrace (prefixWord ++ tailWord_1469500) baseStart_1469500 baseEnd_1469500 := by
    simpa [prefixWord, tailWord_1469500, baseEnd_1469500] using wordTrace_append hprefix tailTrace_1469500
  have hstable : (prefixWord ++ tailWord_1469500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469500).length < 2 ^ (prefixWord ++ tailWord_1469500).sum := by decide
  have hdescent : baseEnd_1469500 < baseStart_1469500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469566 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1469566 : Nat := 118140960795 + 1469566 * 2 ^ 59
def prefixEnd_1469566 : Nat := 4983230072969 + 3 ^ 40 * 1469566 * 2
def baseEnd_1469566 : Nat := 503062474336868366644397

theorem tailTrace_1469566 : CollatzResearch.WordTrace tailWord_1469566 prefixEnd_1469566 503062474336868366644397 := by
  unfold tailWord_1469566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699934424252604842027569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35732983596013892490813701 6699934424252604842027569)
  ·
    refine ⟨5024950818189453631520677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6699934424252604842027569 5024950818189453631520677)
    ·
      refine ⟨942178278410522555910127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5024950818189453631520677 942178278410522555910127)
      ·
        refine ⟨1413267417615783833865191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942178278410522555910127 1413267417615783833865191)
        ·
          refine ⟨2119901126423675750797787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413267417615783833865191 2119901126423675750797787)
          ·
            refine ⟨3179851689635513626196681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119901126423675750797787 3179851689635513626196681)
            ·
              refine ⟨2384888767226635219647511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179851689635513626196681 2384888767226635219647511)
              ·
                refine ⟨3577333150839952829471267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384888767226635219647511 3577333150839952829471267)
                ·
                  refine ⟨5365999726259929244206901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577333150839952829471267 5365999726259929244206901)
                  ·
                    refine ⟨503062474336868366644397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5365999726259929244206901 503062474336868366644397)
                    ·
                      rfl

theorem cell22_1469566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1469566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469566 prefixEnd_1469566 := by exact prefixLift 1469566
  have htrace : WordTrace (prefixWord ++ tailWord_1469566) baseStart_1469566 baseEnd_1469566 := by
    simpa [prefixWord, tailWord_1469566, baseEnd_1469566] using wordTrace_append hprefix tailTrace_1469566
  have hstable : (prefixWord ++ tailWord_1469566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469566).length < 2 ^ (prefixWord ++ tailWord_1469566).sum := by decide
  have hdescent : baseEnd_1469566 < baseStart_1469566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469594 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_1469594 : Nat := 118140960795 + 1469594 * 2 ^ 59
def prefixEnd_1469594 : Nat := 4983230072969 + 3 ^ 40 * 1469594 * 2
def baseEnd_1469594 : Nat := 503072059309085626944311

theorem tailTrace_1469594 : CollatzResearch.WordTrace tailWord_1469594 prefixEnd_1469594 503072059309085626944311 := by
  unfold tailWord_1469594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400124159479849879559959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35733664425279599678826557 13400124159479849879559959)
  ·
    refine ⟨20100186239219774819339939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13400124159479849879559959 20100186239219774819339939)
    ·
      refine ⟨30150279358829662229009909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20100186239219774819339939 30150279358829662229009909)
      ·
        refine ⟨2826588689890280833969679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30150279358829662229009909 2826588689890280833969679)
        ·
          refine ⟨4239883034835421250954519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826588689890280833969679 4239883034835421250954519)
          ·
            refine ⟨6359824552253131876431779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239883034835421250954519 6359824552253131876431779)
            ·
              refine ⟨9539736828379697814647669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359824552253131876431779 9539736828379697814647669)
              ·
                refine ⟨894350327660596670123219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9539736828379697814647669 894350327660596670123219)
                ·
                  refine ⟨1341525491490895005184829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894350327660596670123219 1341525491490895005184829)
                  ·
                    refine ⟨503072059309085626944311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341525491490895005184829 503072059309085626944311)
                    ·
                      rfl

theorem cell22_1469594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_1469594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469594 prefixEnd_1469594 := by exact prefixLift 1469594
  have htrace : WordTrace (prefixWord ++ tailWord_1469594) baseStart_1469594 baseEnd_1469594 := by
    simpa [prefixWord, tailWord_1469594, baseEnd_1469594] using wordTrace_append hprefix tailTrace_1469594
  have hstable : (prefixWord ++ tailWord_1469594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469594).length < 2 ^ (prefixWord ++ tailWord_1469594).sum := by decide
  have hdescent : baseEnd_1469594 < baseStart_1469594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469607 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 5]
def baseStart_1469607 : Nat := 118140960795 + 1469607 * 2 ^ 59
def prefixEnd_1469607 : Nat := 4983230072969 + 3 ^ 40 * 1469607 * 2
def baseEnd_1469607 : Nat := 167692169824919308789757

theorem tailTrace_1469607 : CollatzResearch.WordTrace tailWord_1469607 prefixEnd_1469607 167692169824919308789757 := by
  unfold tailWord_1469607
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600970786872302738463075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35733980524581535158975383 53600970786872302738463075)
  ·
    refine ⟨80401456180308454107694613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53600970786872302738463075 80401456180308454107694613)
    ·
      refine ⟨3768818258451958786298185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80401456180308454107694613 3768818258451958786298185)
      ·
        refine ⟨2826613693838969089723639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768818258451958786298185 2826613693838969089723639)
        ·
          refine ⟨4239920540758453634585459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826613693838969089723639 4239920540758453634585459)
          ·
            refine ⟨6359880811137680451878189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239920540758453634585459 6359880811137680451878189)
            ·
              refine ⟨2384955304176630169454321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6359880811137680451878189 2384955304176630169454321)
              ·
                refine ⟨1788716478132472627090741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384955304176630169454321 1788716478132472627090741)
                ·
                  refine ⟨167692169824919308789757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1788716478132472627090741 167692169824919308789757)
                  ·
                    rfl

theorem cell22_1469607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 5].length) (baseStart_1469607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469607 prefixEnd_1469607 := by exact prefixLift 1469607
  have htrace : WordTrace (prefixWord ++ tailWord_1469607) baseStart_1469607 baseEnd_1469607 := by
    simpa [prefixWord, tailWord_1469607, baseEnd_1469607] using wordTrace_append hprefix tailTrace_1469607
  have hstable : (prefixWord ++ tailWord_1469607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469607).length < 2 ^ (prefixWord ++ tailWord_1469607).sum := by decide
  have hdescent : baseEnd_1469607 < baseStart_1469607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469645 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1469645 : Nat := 118140960795 + 1469645 * 2 ^ 59
def prefixEnd_1469645 : Nat := 4983230072969 + 3 ^ 40 * 1469645 * 2
def baseEnd_1469645 : Nat := 503089517651338493919155

theorem tailTrace_1469645 : CollatzResearch.WordTrace tailWord_1469645 prefixEnd_1469645 503089517651338493919155 := by
  unfold tailWord_1469645
  simp only [CollatzResearch.WordTrace]
  refine ⟨53602356760734635228346389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35734904507156423485564259 53602356760734635228346389)
  ·
    refine ⟨2512610473159436026328737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53602356760734635228346389 2512610473159436026328737)
    ·
      refine ⟨1884457854869577019746553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2512610473159436026328737 1884457854869577019746553)
      ·
        refine ⟨1413343391152182764809915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1884457854869577019746553 1413343391152182764809915)
        ·
          refine ⟨2120015086728274147214873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413343391152182764809915 2120015086728274147214873)
          ·
            refine ⟨1590011315046205610411155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120015086728274147214873 1590011315046205610411155)
            ·
              refine ⟨2385016972569308415616733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590011315046205610411155 2385016972569308415616733)
              ·
                refine ⟨894381364713490655856275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2385016972569308415616733 894381364713490655856275)
                ·
                  refine ⟨1341572047070235983784413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894381364713490655856275 1341572047070235983784413)
                  ·
                    refine ⟨503089517651338493919155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341572047070235983784413 503089517651338493919155)
                    ·
                      rfl

theorem cell22_1469645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1469645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469645 prefixEnd_1469645 := by exact prefixLift 1469645
  have htrace : WordTrace (prefixWord ++ tailWord_1469645) baseStart_1469645 baseEnd_1469645 := by
    simpa [prefixWord, tailWord_1469645, baseEnd_1469645] using wordTrace_append hprefix tailTrace_1469645
  have hstable : (prefixWord ++ tailWord_1469645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469645).length < 2 ^ (prefixWord ++ tailWord_1469645).sum := by decide
  have hdescent : baseEnd_1469645 < baseStart_1469645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469650 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1469650 : Nat := 118140960795 + 1469650 * 2 ^ 59
def prefixEnd_1469650 : Nat := 4983230072969 + 3 ^ 40 * 1469650 * 2
def baseEnd_1469650 : Nat := 503091229253520147544139

theorem tailTrace_1469650 : CollatzResearch.WordTrace tailWord_1469650 prefixEnd_1469650 503091229253520147544139 := by
  unfold tailWord_1469650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400634781429130270569601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35735026083811014054852269 13400634781429130270569601)
  ·
    refine ⟨10050476086071847702927201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13400634781429130270569601 10050476086071847702927201)
    ·
      refine ⟨7537857064553885777195401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10050476086071847702927201 7537857064553885777195401)
      ·
        refine ⟨5653392798415414332896551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537857064553885777195401 5653392798415414332896551)
        ·
          refine ⟨8480089197623121499344827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653392798415414332896551 8480089197623121499344827)
          ·
            refine ⟨12720133796434682249017241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480089197623121499344827 12720133796434682249017241)
            ·
              refine ⟨9540100347326011686762931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12720133796434682249017241 9540100347326011686762931)
              ·
                refine ⟨14310150520989017530144397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9540100347326011686762931 14310150520989017530144397)
                ·
                  refine ⟨5366306445370881573804149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14310150520989017530144397 5366306445370881573804149)
                  ·
                    refine ⟨503091229253520147544139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5366306445370881573804149 503091229253520147544139)
                    ·
                      rfl

theorem cell22_1469650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1469650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469650 prefixEnd_1469650 := by exact prefixLift 1469650
  have htrace : WordTrace (prefixWord ++ tailWord_1469650) baseStart_1469650 baseEnd_1469650 := by
    simpa [prefixWord, tailWord_1469650, baseEnd_1469650] using wordTrace_append hprefix tailTrace_1469650
  have hstable : (prefixWord ++ tailWord_1469650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469650).length < 2 ^ (prefixWord ++ tailWord_1469650).sum := by decide
  have hdescent : baseEnd_1469650 < baseStart_1469650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469663 : List Nat := [1, 1, 2, 3, 2, 1, 12]
def baseStart_1469663 : Nat := 118140960795 + 1469663 * 2 ^ 59
def prefixEnd_1469663 : Nat := 4983230072969 + 3 ^ 40 * 1469663 * 2
def baseEnd_1469663 : Nat := 18633173311821942480337

theorem tailTrace_1469663 : CollatzResearch.WordTrace tailWord_1469663 prefixEnd_1469663 18633173311821942480337 := by
  unfold tailWord_1469663
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603013274669424302501643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735342183112949535001095 53603013274669424302501643)
  ·
    refine ⟨80404519912004136453752465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53603013274669424302501643 80404519912004136453752465)
    ·
      refine ⟨60303389934003102340314349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80404519912004136453752465 60303389934003102340314349)
      ·
        refine ⟨22613771225251163377617881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60303389934003102340314349 22613771225251163377617881)
        ·
          refine ⟨16960328418938372533213411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22613771225251163377617881 16960328418938372533213411)
          ·
            refine ⟨25440492628407558799820117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16960328418938372533213411 25440492628407558799820117)
            ·
              refine ⟨18633173311821942480337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25440492628407558799820117 18633173311821942480337)
              ·
                rfl

theorem cell22_1469663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 12].length) (baseStart_1469663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469663 prefixEnd_1469663 := by exact prefixLift 1469663
  have htrace : WordTrace (prefixWord ++ tailWord_1469663) baseStart_1469663 baseEnd_1469663 := by
    simpa [prefixWord, tailWord_1469663, baseEnd_1469663] using wordTrace_append hprefix tailTrace_1469663
  have hstable : (prefixWord ++ tailWord_1469663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469663).length < 2 ^ (prefixWord ++ tailWord_1469663).sum := by decide
  have hdescent : baseEnd_1469663 < baseStart_1469663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469665 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1469665 : Nat := 118140960795 + 1469665 * 2 ^ 59
def prefixEnd_1469665 : Nat := 4983230072969 + 3 ^ 40 * 1469665 * 2
def baseEnd_1469665 : Nat := 503096364060065108419093

theorem tailTrace_1469665 : CollatzResearch.WordTrace tailWord_1469665 prefixEnd_1469665 503096364060065108419093 := by
  unfold tailWord_1469665
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603086220662178644074449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735390813774785762716299 53603086220662178644074449)
  ·
    refine ⟨40202314665496633983055837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53603086220662178644074449 40202314665496633983055837)
    ·
      refine ⟨15075867999561237743645939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40202314665496633983055837 15075867999561237743645939)
      ·
        refine ⟨22613801999341856615468909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075867999561237743645939 22613801999341856615468909)
        ·
          refine ⟨8480175749753196230800841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22613801999341856615468909 8480175749753196230800841)
          ·
            refine ⟨6360131812314897173100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8480175749753196230800841 6360131812314897173100631)
            ·
              refine ⟨9540197718472345759650947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360131812314897173100631 9540197718472345759650947)
              ·
                refine ⟨14310296577708518639476421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9540197718472345759650947 14310296577708518639476421)
                ·
                  refine ⟨2683180608320347244901829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14310296577708518639476421 2683180608320347244901829)
                  ·
                    refine ⟨503096364060065108419093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2683180608320347244901829 503096364060065108419093)
                    ·
                      rfl

theorem cell22_1469665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1469665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469665 prefixEnd_1469665 := by exact prefixLift 1469665
  have htrace : WordTrace (prefixWord ++ tailWord_1469665) baseStart_1469665 baseEnd_1469665 := by
    simpa [prefixWord, tailWord_1469665, baseEnd_1469665] using wordTrace_append hprefix tailTrace_1469665
  have hstable : (prefixWord ++ tailWord_1469665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469665).length < 2 ^ (prefixWord ++ tailWord_1469665).sum := by decide
  have hdescent : baseEnd_1469665 < baseStart_1469665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469669 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 6]
def baseStart_1469669 : Nat := 118140960795 + 1469669 * 2 ^ 59
def prefixEnd_1469669 : Nat := 4983230072969 + 3 ^ 40 * 1469669 * 2
def baseEnd_1469669 : Nat := 167699244447270143773027

theorem tailTrace_1469669 : CollatzResearch.WordTrace tailWord_1469669 prefixEnd_1469669 167699244447270143773027 := by
  unfold tailWord_1469669
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603232112647687327220061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735488075098458218146707 53603232112647687327220061)
  ·
    refine ⟨20101212042242882747707523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53603232112647687327220061 20101212042242882747707523)
    ·
      refine ⟨30151818063364324121561285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20101212042242882747707523 30151818063364324121561285)
      ·
        refine ⟨5653465886880810772792741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30151818063364324121561285 5653465886880810772792741)
        ·
          refine ⟨1060024853790152019898639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5653465886880810772792741 1060024853790152019898639)
          ·
            refine ⟨1590037280685228029847959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060024853790152019898639 1590037280685228029847959)
            ·
              refine ⟨2385055921027842044771939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590037280685228029847959 2385055921027842044771939)
              ·
                refine ⟨3577583881541763067157909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385055921027842044771939 3577583881541763067157909)
                ·
                  refine ⟨167699244447270143773027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3577583881541763067157909 167699244447270143773027)
                  ·
                    rfl

theorem cell22_1469669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_1469669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469669 prefixEnd_1469669 := by exact prefixLift 1469669
  have htrace : WordTrace (prefixWord ++ tailWord_1469669) baseStart_1469669 baseEnd_1469669 := by
    simpa [prefixWord, tailWord_1469669, baseEnd_1469669] using wordTrace_append hprefix tailTrace_1469669
  have hstable : (prefixWord ++ tailWord_1469669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469669).length < 2 ^ (prefixWord ++ tailWord_1469669).sum := by decide
  have hdescent : baseEnd_1469669 < baseStart_1469669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469714 : List Nat := [3, 2, 4, 2, 2, 9]
def baseStart_1469714 : Nat := 118140960795 + 1469714 * 2 ^ 59
def prefixEnd_1469714 : Nat := 4983230072969 + 3 ^ 40 * 1469714 * 2
def baseEnd_1469714 : Nat := 6211273305696855727703

theorem tailTrace_1469714 : CollatzResearch.WordTrace tailWord_1469714 prefixEnd_1469714 6211273305696855727703 := by
  unfold tailWord_1469714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401218349371165003152049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35736582264989773341738797 13401218349371165003152049)
  ·
    refine ⟨10050913762028373752364037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13401218349371165003152049 10050913762028373752364037)
    ·
      refine ⟨1884546330380320078568257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10050913762028373752364037 1884546330380320078568257)
      ·
        refine ⟨1413409747785240058926193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1884546330380320078568257 1413409747785240058926193)
        ·
          refine ⟨1060057310838930044194645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413409747785240058926193 1060057310838930044194645)
          ·
            refine ⟨6211273305696855727703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1060057310838930044194645 6211273305696855727703)
            ·
              rfl

theorem cell22_1469714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 9].length) (baseStart_1469714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469714 prefixEnd_1469714 := by exact prefixLift 1469714
  have htrace : WordTrace (prefixWord ++ tailWord_1469714) baseStart_1469714 baseEnd_1469714 := by
    simpa [prefixWord, tailWord_1469714, baseEnd_1469714] using wordTrace_append hprefix tailTrace_1469714
  have hstable : (prefixWord ++ tailWord_1469714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469714).length < 2 ^ (prefixWord ++ tailWord_1469714).sum := by decide
  have hdescent : baseEnd_1469714 < baseStart_1469714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469785 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1469785 : Nat := 118140960795 + 1469785 * 2 ^ 59
def prefixEnd_1469785 : Nat := 4983230072969 + 3 ^ 40 * 1469785 * 2
def baseEnd_1469785 : Nat := 503137442512424795418725

theorem tailTrace_1469785 : CollatzResearch.WordTrace tailWord_1469785 prefixEnd_1469785 503137442512424795418725 := by
  unfold tailWord_1469785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53607462980227439138442809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35738308653484959425628539 53607462980227439138442809)
  ·
    refine ⟨40205597235170579353832107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53607462980227439138442809 40205597235170579353832107)
    ·
      refine ⟨60308395852755869030748161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40205597235170579353832107 60308395852755869030748161)
      ·
        refine ⟨45231296889566901773061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60308395852755869030748161 45231296889566901773061121)
        ·
          refine ⟨33923472667175176329795841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45231296889566901773061121 33923472667175176329795841)
          ·
            refine ⟨25442604500381382247346881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33923472667175176329795841 25442604500381382247346881)
            ·
              refine ⟨19081953375286036685510161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25442604500381382247346881 19081953375286036685510161)
              ·
                refine ⟨14311465031464527514132621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19081953375286036685510161 14311465031464527514132621)
                ·
                  refine ⟨5366799386799197817799733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14311465031464527514132621 5366799386799197817799733)
                  ·
                    refine ⟨503137442512424795418725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5366799386799197817799733 503137442512424795418725)
                    ·
                      rfl

theorem cell22_1469785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1469785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469785 prefixEnd_1469785 := by exact prefixLift 1469785
  have htrace : WordTrace (prefixWord ++ tailWord_1469785) baseStart_1469785 baseEnd_1469785 := by
    simpa [prefixWord, tailWord_1469785, baseEnd_1469785] using wordTrace_append hprefix tailTrace_1469785
  have hstable : (prefixWord ++ tailWord_1469785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469785).length < 2 ^ (prefixWord ++ tailWord_1469785).sum := by decide
  have hdescent : baseEnd_1469785 < baseStart_1469785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469815 : List Nat := [1, 1, 3, 1, 1, 2, 5, 8]
def baseStart_1469815 : Nat := 118140960795 + 1469815 * 2 ^ 59
def prefixEnd_1469815 : Nat := 4983230072969 + 3 ^ 40 * 1469815 * 2
def baseEnd_1469815 : Nat := 55905301347279413018737

theorem tailTrace_1469815 : CollatzResearch.WordTrace tailWord_1469815 prefixEnd_1469815 55905301347279413018737 := by
  unfold tailWord_1469815
  simp only [CollatzResearch.WordTrace]
  refine ⟨53608557170118754262034899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35739038113412502841356599 53608557170118754262034899)
  ·
    refine ⟨80412835755178131393052349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53608557170118754262034899 80412835755178131393052349)
    ·
      refine ⟨30154813408191799272394631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80412835755178131393052349 30154813408191799272394631)
      ·
        refine ⟨45232220112287698908591947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30154813408191799272394631 45232220112287698908591947)
        ·
          refine ⟨67848330168431548362887921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45232220112287698908591947 67848330168431548362887921)
          ·
            refine ⟨50886247626323661272165941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67848330168431548362887921 50886247626323661272165941)
            ·
              refine ⟨4770585714967843244265557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50886247626323661272165941 4770585714967843244265557)
              ·
                refine ⟨55905301347279413018737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4770585714967843244265557 55905301347279413018737)
                ·
                  rfl

theorem cell22_1469815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 8].length) (baseStart_1469815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469815 prefixEnd_1469815 := by exact prefixLift 1469815
  have htrace : WordTrace (prefixWord ++ tailWord_1469815) baseStart_1469815 baseEnd_1469815 := by
    simpa [prefixWord, tailWord_1469815, baseEnd_1469815] using wordTrace_append hprefix tailTrace_1469815
  have hstable : (prefixWord ++ tailWord_1469815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469815).length < 2 ^ (prefixWord ++ tailWord_1469815).sum := by decide
  have hdescent : baseEnd_1469815 < baseStart_1469815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469832 : List Nat := [2, 1, 3, 3, 1, 4, 8]
def baseStart_1469832 : Nat := 118140960795 + 1469832 * 2 ^ 59
def prefixEnd_1469832 : Nat := 4983230072969 + 3 ^ 40 * 1469832 * 2
def baseEnd_1469832 : Nat := 18635315984182679240503

theorem tailTrace_1469832 : CollatzResearch.WordTrace tailWord_1469832 prefixEnd_1469832 18635315984182679240503 := by
  unfold tailWord_1469832
  simp only [CollatzResearch.WordTrace]
  refine ⟨26804588605528583082701875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35739451474038110776935833 26804588605528583082701875)
  ·
    refine ⟨40206882908292874624052813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26804588605528583082701875 40206882908292874624052813)
    ·
      refine ⟨15077581090609827984019805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40206882908292874624052813 15077581090609827984019805)
      ·
        refine ⟨5654092908978685494007427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15077581090609827984019805 5654092908978685494007427)
        ·
          refine ⟨8481139363468028241011141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5654092908978685494007427 8481139363468028241011141)
          ·
            refine ⟨1590213630650255295189589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8481139363468028241011141 1590213630650255295189589)
            ·
              refine ⟨18635315984182679240503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1590213630650255295189589 18635315984182679240503)
              ·
                rfl

theorem cell22_1469832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 8].length) (baseStart_1469832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469832 prefixEnd_1469832 := by exact prefixLift 1469832
  have htrace : WordTrace (prefixWord ++ tailWord_1469832) baseStart_1469832 baseEnd_1469832 := by
    simpa [prefixWord, tailWord_1469832, baseEnd_1469832] using wordTrace_append hprefix tailTrace_1469832
  have hstable : (prefixWord ++ tailWord_1469832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469832).length < 2 ^ (prefixWord ++ tailWord_1469832).sum := by decide
  have hdescent : baseEnd_1469832 < baseStart_1469832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469838 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_1469838 : Nat := 118140960795 + 1469838 * 2 ^ 59
def prefixEnd_1469838 : Nat := 4983230072969 + 3 ^ 40 * 1469838 * 2
def baseEnd_1469838 : Nat := 167718528498516774614521

theorem tailTrace_1469838 : CollatzResearch.WordTrace tailWord_1469838 prefixEnd_1469838 167718528498516774614521 := by
  unfold tailWord_1469838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701174506129428648765271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35739597366023619460081445 6701174506129428648765271)
  ·
    refine ⟨10051761759194142973147907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701174506129428648765271 10051761759194142973147907)
    ·
      refine ⟨15077642638791214459721861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10051761759194142973147907 15077642638791214459721861)
      ·
        refine ⟨2827057994773352711197849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15077642638791214459721861 2827057994773352711197849)
        ·
          refine ⟨2120293496080014533398387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827057994773352711197849 2120293496080014533398387)
          ·
            refine ⟨3180440244120021800097581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120293496080014533398387 3180440244120021800097581)
            ·
              refine ⟨1192665091545008175036593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3180440244120021800097581 1192665091545008175036593)
              ·
                refine ⟨894498818658756131277445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192665091545008175036593 894498818658756131277445)
                ·
                  refine ⟨167718528498516774614521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894498818658756131277445 167718528498516774614521)
                  ·
                    rfl

theorem cell22_1469838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_1469838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469838 prefixEnd_1469838 := by exact prefixLift 1469838
  have htrace : WordTrace (prefixWord ++ tailWord_1469838) baseStart_1469838 baseEnd_1469838 := by
    simpa [prefixWord, tailWord_1469838, baseEnd_1469838] using wordTrace_append hprefix tailTrace_1469838
  have hstable : (prefixWord ++ tailWord_1469838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469838).length < 2 ^ (prefixWord ++ tailWord_1469838).sum := by decide
  have hdescent : baseEnd_1469838 < baseStart_1469838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469853 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1469853 : Nat := 118140960795 + 1469853 * 2 ^ 59
def prefixEnd_1469853 : Nat := 4983230072969 + 3 ^ 40 * 1469853 * 2
def baseEnd_1469853 : Nat := 503160720302095284718517

theorem tailTrace_1469853 : CollatzResearch.WordTrace tailWord_1469853 prefixEnd_1469853 503160720302095284718517 := by
  unfold tailWord_1469853
  simp only [CollatzResearch.WordTrace]
  refine ⟨53609943143981086751918213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35739962095987391167945475 53609943143981086751918213)
  ·
    refine ⟨10051864339496453765984665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53609943143981086751918213 10051864339496453765984665)
    ·
      refine ⟨7538898254622340324488499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10051864339496453765984665 7538898254622340324488499)
      ·
        refine ⟨11308347381933510486732749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538898254622340324488499 11308347381933510486732749)
        ·
          refine ⟨4240630268225066432524781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11308347381933510486732749 4240630268225066432524781)
          ·
            refine ⟨1590236350584399912196793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4240630268225066432524781 1590236350584399912196793)
            ·
              refine ⟨1192677262938299934147595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590236350584399912196793 1192677262938299934147595)
              ·
                refine ⟨1789015894407449901221393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192677262938299934147595 1789015894407449901221393)
                ·
                  refine ⟨1341761920805587425916045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789015894407449901221393 1341761920805587425916045)
                  ·
                    refine ⟨503160720302095284718517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341761920805587425916045 503160720302095284718517)
                    ·
                      rfl

theorem cell22_1469853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1469853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469853 prefixEnd_1469853 := by exact prefixLift 1469853
  have htrace : WordTrace (prefixWord ++ tailWord_1469853) baseStart_1469853 baseEnd_1469853 := by
    simpa [prefixWord, tailWord_1469853, baseEnd_1469853] using wordTrace_append hprefix tailTrace_1469853
  have hstable : (prefixWord ++ tailWord_1469853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469853).length < 2 ^ (prefixWord ++ tailWord_1469853).sum := by decide
  have hdescent : baseEnd_1469853 < baseStart_1469853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469898 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1469898 : Nat := 118140960795 + 1469898 * 2 ^ 59
def prefixEnd_1469898 : Nat := 4983230072969 + 3 ^ 40 * 1469898 * 2
def baseEnd_1469898 : Nat := 503176124721730167343379

theorem tailTrace_1469898 : CollatzResearch.WordTrace tailWord_1469898 prefixEnd_1469898 503176124721730167343379 := by
  unfold tailWord_1469898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402896107204514859326587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35741056285878706291537565 13402896107204514859326587)
  ·
    refine ⟨20104344160806772288989881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13402896107204514859326587 20104344160806772288989881)
    ·
      refine ⟨15078258120605079216742411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20104344160806772288989881 15078258120605079216742411)
      ·
        refine ⟨22617387180907618825113617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078258120605079216742411 22617387180907618825113617)
        ·
          refine ⟨16963040385680714118835213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22617387180907618825113617 16963040385680714118835213)
          ·
            refine ⟨6361140144630267794563205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16963040385680714118835213 6361140144630267794563205)
            ·
              refine ⟨1192713777118175211480601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6361140144630267794563205 1192713777118175211480601)
              ·
                refine ⟨894535332838631408610451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192713777118175211480601 894535332838631408610451)
                ·
                  refine ⟨1341802999257947112915677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894535332838631408610451 1341802999257947112915677)
                  ·
                    refine ⟨503176124721730167343379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341802999257947112915677 503176124721730167343379)
                    ·
                      rfl

theorem cell22_1469898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1469898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469898 prefixEnd_1469898 := by exact prefixLift 1469898
  have htrace : WordTrace (prefixWord ++ tailWord_1469898) baseStart_1469898 baseEnd_1469898 := by
    simpa [prefixWord, tailWord_1469898, baseEnd_1469898] using wordTrace_append hprefix tailTrace_1469898
  have hstable : (prefixWord ++ tailWord_1469898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469898).length < 2 ^ (prefixWord ++ tailWord_1469898).sum := by decide
  have hdescent : baseEnd_1469898 < baseStart_1469898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469956 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1469956 : Nat := 118140960795 + 1469956 * 2 ^ 59
def prefixEnd_1469956 : Nat := 4983230072969 + 3 ^ 40 * 1469956 * 2
def baseEnd_1469956 : Nat := 167731993102345783131067

theorem tailTrace_1469956 : CollatzResearch.WordTrace tailWord_1469956 prefixEnd_1469956 167731993102345783131067 := by
  unfold tailWord_1469956
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806849931303967671458861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35742466575071956895278481 26806849931303967671458861)
  ·
    refine ⟨10052568724238987876797073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26806849931303967671458861 10052568724238987876797073)
    ·
      refine ⟨7539426543179240907597805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10052568724238987876797073 7539426543179240907597805)
      ·
        refine ⟨2827284953692215340349177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7539426543179240907597805 2827284953692215340349177)
        ·
          refine ⟨2120463715269161505261883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827284953692215340349177 2120463715269161505261883)
          ·
            refine ⟨3180695572903742257892825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120463715269161505261883 3180695572903742257892825)
            ·
              refine ⟨2385521679677806693419619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180695572903742257892825 2385521679677806693419619)
              ·
                refine ⟨3578282519516710040129429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385521679677806693419619 3578282519516710040129429)
                ·
                  refine ⟨167731993102345783131067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3578282519516710040129429 167731993102345783131067)
                  ·
                    rfl

theorem cell22_1469956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1469956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469956 prefixEnd_1469956 := by exact prefixLift 1469956
  have htrace : WordTrace (prefixWord ++ tailWord_1469956) baseStart_1469956 baseEnd_1469956 := by
    simpa [prefixWord, tailWord_1469956, baseEnd_1469956] using wordTrace_append hprefix tailTrace_1469956
  have hstable : (prefixWord ++ tailWord_1469956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469956).length < 2 ^ (prefixWord ++ tailWord_1469956).sum := by decide
  have hdescent : baseEnd_1469956 < baseStart_1469956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469984 : List Nat := [2, 1, 1, 6, 1, 2, 1, 8]
def baseStart_1469984 : Nat := 118140960795 + 1469984 * 2 ^ 59
def prefixEnd_1469984 : Nat := 4983230072969 + 3 ^ 40 * 1469984 * 2
def baseEnd_1469984 : Nat := 55911729364361623299235

theorem tailTrace_1469984 : CollatzResearch.WordTrace tailWord_1469984 prefixEnd_1469984 55911729364361623299235 := by
  unfold tailWord_1469984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807360553253248062468503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35743147404337664083291337 26807360553253248062468503)
  ·
    refine ⟨40211040829879872093702755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26807360553253248062468503 40211040829879872093702755)
    ·
      refine ⟨60316561244819808140554133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40211040829879872093702755 60316561244819808140554133)
      ·
        refine ⟨2827338808350928506588475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60316561244819808140554133 2827338808350928506588475)
        ·
          refine ⟨4241008212526392759882713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827338808350928506588475 4241008212526392759882713)
          ·
            refine ⟨3180756159394794569912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4241008212526392759882713 3180756159394794569912035)
            ·
              refine ⟨4771134239092191854868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180756159394794569912035 4771134239092191854868053)
              ·
                refine ⟨55911729364361623299235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4771134239092191854868053 55911729364361623299235)
                ·
                  rfl

theorem cell22_1469984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_1469984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1469984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1469984 prefixEnd_1469984 := by exact prefixLift 1469984
  have htrace : WordTrace (prefixWord ++ tailWord_1469984) baseStart_1469984 baseEnd_1469984 := by
    simpa [prefixWord, tailWord_1469984, baseEnd_1469984] using wordTrace_append hprefix tailTrace_1469984
  have hstable : (prefixWord ++ tailWord_1469984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469984).length < 2 ^ (prefixWord ++ tailWord_1469984).sum := by decide
  have hdescent : baseEnd_1469984 < baseStart_1469984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470027 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_1470027 : Nat := 118140960795 + 1470027 * 2 ^ 59
def prefixEnd_1470027 : Nat := 4983230072969 + 3 ^ 40 * 1470027 * 2
def baseEnd_1470027 : Nat := 503220284058016830867983

theorem tailTrace_1470027 : CollatzResearch.WordTrace tailWord_1470027 prefixEnd_1470027 503220284058016830867983 := by
  unfold tailWord_1470027
  simp only [CollatzResearch.WordTrace]
  refine ⟨53616289445350714468752335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35744192963567142979168223 53616289445350714468752335)
  ·
    refine ⟨80424434168026071703128503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53616289445350714468752335 80424434168026071703128503)
    ·
      refine ⟨120636651252039107554692755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80424434168026071703128503 120636651252039107554692755)
      ·
        refine ⟨180954976878058661332039133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120636651252039107554692755 180954976878058661332039133)
        ·
          refine ⟨67858116329271997999514675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180954976878058661332039133 67858116329271997999514675)
          ·
            refine ⟨101787174493907996999272013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67858116329271997999514675 101787174493907996999272013)
            ·
              refine ⟨38170190435215498874727005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101787174493907996999272013 38170190435215498874727005)
              ·
                refine ⟨14313821413205812078022627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38170190435215498874727005 14313821413205812078022627)
                ·
                  refine ⟨21470732119808718117033941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14313821413205812078022627 21470732119808718117033941)
                  ·
                    refine ⟨503220284058016830867983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21470732119808718117033941 503220284058016830867983)
                    ·
                      rfl

theorem cell22_1470027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_1470027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470027 prefixEnd_1470027 := by exact prefixLift 1470027
  have htrace : WordTrace (prefixWord ++ tailWord_1470027) baseStart_1470027 baseEnd_1470027 := by
    simpa [prefixWord, tailWord_1470027, baseEnd_1470027] using wordTrace_append hprefix tailTrace_1470027
  have hstable : (prefixWord ++ tailWord_1470027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470027).length < 2 ^ (prefixWord ++ tailWord_1470027).sum := by decide
  have hdescent : baseEnd_1470027 < baseStart_1470027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470089 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_1470089 : Nat := 118140960795 + 1470089 * 2 ^ 59
def prefixEnd_1470089 : Nat := 4983230072969 + 3 ^ 40 * 1470089 * 2
def baseEnd_1470089 : Nat := 503241507925069335817793

theorem tailTrace_1470089 : CollatzResearch.WordTrace tailWord_1470089 prefixEnd_1470089 503241507925069335817793 := by
  unfold tailWord_1470089
  simp only [CollatzResearch.WordTrace]
  refine ⟨53618550771126099057509321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35745700514084066038339547 53618550771126099057509321)
  ·
    refine ⟨40213913078344574293131991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53618550771126099057509321 40213913078344574293131991)
    ·
      refine ⟨60320869617516861439697987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40213913078344574293131991 60320869617516861439697987)
      ·
        refine ⟨90481304426275292159546981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60320869617516861439697987 90481304426275292159546981)
        ·
          refine ⟨16965244579926617279915059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90481304426275292159546981 16965244579926617279915059)
          ·
            refine ⟨25447866869889925919872589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965244579926617279915059 25447866869889925919872589)
            ·
              refine ⟨9542950076208722219952221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25447866869889925919872589 9542950076208722219952221)
              ·
                refine ⟨3578606278578270832482083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9542950076208722219952221 3578606278578270832482083)
                ·
                  refine ⟨5367909417867406248723125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578606278578270832482083 5367909417867406248723125)
                  ·
                    refine ⟨503241507925069335817793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5367909417867406248723125 503241507925069335817793)
                    ·
                      rfl

theorem cell22_1470089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_1470089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470089 prefixEnd_1470089 := by exact prefixLift 1470089
  have htrace : WordTrace (prefixWord ++ tailWord_1470089) baseStart_1470089 baseEnd_1470089 := by
    simpa [prefixWord, tailWord_1470089, baseEnd_1470089] using wordTrace_append hprefix tailTrace_1470089
  have hstable : (prefixWord ++ tailWord_1470089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470089).length < 2 ^ (prefixWord ++ tailWord_1470089).sum := by decide
  have hdescent : baseEnd_1470089 < baseStart_1470089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470110 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1470110 : Nat := 118140960795 + 1470110 * 2 ^ 59
def prefixEnd_1470110 : Nat := 4983230072969 + 3 ^ 40 * 1470110 * 2
def baseEnd_1470110 : Nat := 503248696654232281042729

theorem tailTrace_1470110 : CollatzResearch.WordTrace tailWord_1470110 prefixEnd_1470110 503248696654232281042729 := by
  unfold tailWord_1470110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702414588006252455502973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35746211136033346429349189 6702414588006252455502973)
  ·
    refine ⟨2513405470502344670813615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6702414588006252455502973 2513405470502344670813615)
    ·
      refine ⟨3770108205753517006220423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2513405470502344670813615 3770108205753517006220423)
      ·
        refine ⟨5655162308630275509330635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770108205753517006220423 5655162308630275509330635)
        ·
          refine ⟨8482743462945413263995953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655162308630275509330635 8482743462945413263995953)
          ·
            refine ⟨6362057597209059947996965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8482743462945413263995953 6362057597209059947996965)
            ·
              refine ⟨1192885799476698740249431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6362057597209059947996965 1192885799476698740249431)
              ·
                refine ⟨1789328699215048110374147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192885799476698740249431 1789328699215048110374147)
                ·
                  refine ⟨2683993048822572165561221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789328699215048110374147 2683993048822572165561221)
                  ·
                    refine ⟨503248696654232281042729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2683993048822572165561221 503248696654232281042729)
                    ·
                      rfl

theorem cell22_1470110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1470110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470110 prefixEnd_1470110 := by exact prefixLift 1470110
  have htrace : WordTrace (prefixWord ++ tailWord_1470110) baseStart_1470110 baseEnd_1470110 := by
    simpa [prefixWord, tailWord_1470110, baseEnd_1470110] using wordTrace_append hprefix tailTrace_1470110
  have hstable : (prefixWord ++ tailWord_1470110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470110).length < 2 ^ (prefixWord ++ tailWord_1470110).sum := by decide
  have hdescent : baseEnd_1470110 < baseStart_1470110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470140 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_1470140 : Nat := 118140960795 + 1470140 * 2 ^ 59
def prefixEnd_1470140 : Nat := 4983230072969 + 3 ^ 40 * 1470140 * 2
def baseEnd_1470140 : Nat := 503258966267322202792637

theorem tailTrace_1470140 : CollatzResearch.WordTrace tailWord_1470140 prefixEnd_1470140 503258966267322202792637 := by
  unfold tailWord_1470140
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810205446970667383807937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35746940595960889845077249 26810205446970667383807937)
  ·
    refine ⟨20107654085228000537855953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26810205446970667383807937 20107654085228000537855953)
    ·
      refine ⟨15080740563921000403391965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20107654085228000537855953 15080740563921000403391965)
      ·
        refine ⟨5655277711470375151271987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15080740563921000403391965 5655277711470375151271987)
        ·
          refine ⟨8482916567205562726907981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655277711470375151271987 8482916567205562726907981)
          ·
            refine ⟨3181093712702086022590493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8482916567205562726907981 3181093712702086022590493)
            ·
              refine ⟨1192910142263282258471435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3181093712702086022590493 1192910142263282258471435)
              ·
                refine ⟨1789365213394923387707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192910142263282258471435 1789365213394923387707153)
                ·
                  refine ⟨1342023910046192540780365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789365213394923387707153 1342023910046192540780365)
                  ·
                    refine ⟨503258966267322202792637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342023910046192540780365 503258966267322202792637)
                    ·
                      rfl

theorem cell22_1470140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_1470140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470140 prefixEnd_1470140 := by exact prefixLift 1470140
  have htrace : WordTrace (prefixWord ++ tailWord_1470140) baseStart_1470140 baseEnd_1470140 := by
    simpa [prefixWord, tailWord_1470140, baseEnd_1470140] using wordTrace_append hprefix tailTrace_1470140
  have hstable : (prefixWord ++ tailWord_1470140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470140).length < 2 ^ (prefixWord ++ tailWord_1470140).sum := by decide
  have hdescent : baseEnd_1470140 < baseStart_1470140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470151 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1470151 : Nat := 118140960795 + 1470151 * 2 ^ 59
def prefixEnd_1470151 : Nat := 4983230072969 + 3 ^ 40 * 1470151 * 2
def baseEnd_1470151 : Nat := 503262731792121840767603

theorem tailTrace_1470151 : CollatzResearch.WordTrace tailWord_1470151 prefixEnd_1470151 503262731792121840767603 := by
  unfold tailWord_1470151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53620812096901483646266307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35747208064600989097510871 53620812096901483646266307)
  ·
    refine ⟨80431218145352225469399461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53620812096901483646266307 80431218145352225469399461)
    ·
      refine ⟨15080853402253542275512399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80431218145352225469399461 15080853402253542275512399)
      ·
        refine ⟨22621280103380313413268599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080853402253542275512399 22621280103380313413268599)
        ·
          refine ⟨33931920155070470119902899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22621280103380313413268599 33931920155070470119902899)
          ·
            refine ⟨50897880232605705179854349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33931920155070470119902899 50897880232605705179854349)
            ·
              refine ⟨19086705087227139442445381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50897880232605705179854349 19086705087227139442445381)
              ·
                refine ⟨3578757203855088645458509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19086705087227139442445381 3578757203855088645458509)
                ·
                  refine ⟨1342033951445658242046941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3578757203855088645458509 1342033951445658242046941)
                  ·
                    refine ⟨503262731792121840767603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342033951445658242046941 503262731792121840767603)
                    ·
                      rfl

theorem cell22_1470151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1470151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470151 prefixEnd_1470151 := by exact prefixLift 1470151
  have htrace : WordTrace (prefixWord ++ tailWord_1470151) baseStart_1470151 baseEnd_1470151 := by
    simpa [prefixWord, tailWord_1470151, baseEnd_1470151] using wordTrace_append hprefix tailTrace_1470151
  have hstable : (prefixWord ++ tailWord_1470151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470151).length < 2 ^ (prefixWord ++ tailWord_1470151).sum := by decide
  have hdescent : baseEnd_1470151 < baseStart_1470151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470181 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 5]
def baseStart_1470181 : Nat := 118140960795 + 1470181 * 2 ^ 59
def prefixEnd_1470181 : Nat := 4983230072969 + 3 ^ 40 * 1470181 * 2
def baseEnd_1470181 : Nat := 167757667135070587505837

theorem tailTrace_1470181 : CollatzResearch.WordTrace tailWord_1470181 prefixEnd_1470181 167757667135070587505837 := by
  unfold tailWord_1470181
  simp only [CollatzResearch.WordTrace]
  refine ⟨53621906286792798769858397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35747937524528532513238931 53621906286792798769858397)
  ·
    refine ⟨20108214857547299538696899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53621906286792798769858397 20108214857547299538696899)
    ·
      refine ⟨30162322286320949308045349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20108214857547299538696899 30162322286320949308045349)
      ·
        refine ⟨5655435428685177995258503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30162322286320949308045349 5655435428685177995258503)
        ·
          refine ⟨8483153143027766992887755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655435428685177995258503 8483153143027766992887755)
          ·
            refine ⟨12724729714541650489331633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483153143027766992887755 12724729714541650489331633)
            ·
              refine ⟨9543547285906237866998725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12724729714541650489331633 9543547285906237866998725)
              ·
                refine ⟨1789415116107419600062261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9543547285906237866998725 1789415116107419600062261)
                ·
                  refine ⟨167757667135070587505837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789415116107419600062261 167757667135070587505837)
                  ·
                    rfl

theorem cell22_1470181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_1470181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470181 prefixEnd_1470181 := by exact prefixLift 1470181
  have htrace : WordTrace (prefixWord ++ tailWord_1470181) baseStart_1470181 baseEnd_1470181 := by
    simpa [prefixWord, tailWord_1470181, baseEnd_1470181] using wordTrace_append hprefix tailTrace_1470181
  have hstable : (prefixWord ++ tailWord_1470181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470181).length < 2 ^ (prefixWord ++ tailWord_1470181).sum := by decide
  have hdescent : baseEnd_1470181 < baseStart_1470181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470198 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1470198 : Nat := 118140960795 + 1470198 * 2 ^ 59
def prefixEnd_1470198 : Nat := 4983230072969 + 3 ^ 40 * 1470198 * 2
def baseEnd_1470198 : Nat := 167759606950876461614153

theorem tailTrace_1470198 : CollatzResearch.WordTrace tailWord_1470198 prefixEnd_1470198 167759606950876461614153 := by
  unfold tailWord_1470198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351407895483200667076703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35748350885154140448818165 3351407895483200667076703)
  ·
    refine ⟨5027111843224801000615055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351407895483200667076703 5027111843224801000615055)
    ·
      refine ⟨7540667764837201500922583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027111843224801000615055 7540667764837201500922583)
      ·
        refine ⟨11311001647255802251383875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7540667764837201500922583 11311001647255802251383875)
        ·
          refine ⟨16966502470883703377075813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11311001647255802251383875 16966502470883703377075813)
          ·
            refine ⟨3181219213290694383201715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16966502470883703377075813 3181219213290694383201715)
            ·
              refine ⟨4771828819936041574802573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181219213290694383201715 4771828819936041574802573)
              ·
                refine ⟨1789435807476015590550965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4771828819936041574802573 1789435807476015590550965)
                ·
                  refine ⟨167759606950876461614153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789435807476015590550965 167759606950876461614153)
                  ·
                    rfl

theorem cell22_1470198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1470198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470198 prefixEnd_1470198 := by exact prefixLift 1470198
  have htrace : WordTrace (prefixWord ++ tailWord_1470198) baseStart_1470198 baseEnd_1470198 := by
    simpa [prefixWord, tailWord_1470198, baseEnd_1470198] using wordTrace_append hprefix tailTrace_1470198
  have hstable : (prefixWord ++ tailWord_1470198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470198).length < 2 ^ (prefixWord ++ tailWord_1470198).sum := by decide
  have hdescent : baseEnd_1470198 < baseStart_1470198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470258 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1470258 : Nat := 118140960795 + 1470258 * 2 ^ 59
def prefixEnd_1470258 : Nat := 4983230072969 + 3 ^ 40 * 1470258 * 2
def baseEnd_1470258 : Nat := 503299360078809228342275

theorem tailTrace_1470258 : CollatzResearch.WordTrace tailWord_1470258 prefixEnd_1470258 503299360078809228342275 := by
  unfold tailWord_1470258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406178676878460230102857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35749809805009227280274285 13406178676878460230102857)
  ·
    refine ⟨10054634007658845172577143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13406178676878460230102857 10054634007658845172577143)
    ·
      refine ⟨15081951011488267758865715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054634007658845172577143 15081951011488267758865715)
      ·
        refine ⟨22622926517232401638298573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15081951011488267758865715 22622926517232401638298573)
        ·
          refine ⟨8483597443962150614361965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22622926517232401638298573 8483597443962150614361965)
          ·
            refine ⟨3181349041485806480385737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8483597443962150614361965 3181349041485806480385737)
            ·
              refine ⟨2386011781114354860289303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181349041485806480385737 2386011781114354860289303)
              ·
                refine ⟨3579017671671532290433955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386011781114354860289303 3579017671671532290433955)
                ·
                  refine ⟨5368526507507298435650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579017671671532290433955 5368526507507298435650933)
                  ·
                    refine ⟨503299360078809228342275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5368526507507298435650933 503299360078809228342275)
                    ·
                      rfl

theorem cell22_1470258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1470258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470258 prefixEnd_1470258 := by exact prefixLift 1470258
  have htrace : WordTrace (prefixWord ++ tailWord_1470258) baseStart_1470258 baseEnd_1470258 := by
    simpa [prefixWord, tailWord_1470258, baseEnd_1470258] using wordTrace_append hprefix tailTrace_1470258
  have hstable : (prefixWord ++ tailWord_1470258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470258).length < 2 ^ (prefixWord ++ tailWord_1470258).sum := by decide
  have hdescent : baseEnd_1470258 < baseStart_1470258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470292 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1470292 : Nat := 118140960795 + 1470292 * 2 ^ 59
def prefixEnd_1470292 : Nat := 4983230072969 + 3 ^ 40 * 1470292 * 2
def baseEnd_1470292 : Nat := 503310998973644472992171

theorem tailTrace_1470292 : CollatzResearch.WordTrace tailWord_1470292 prefixEnd_1470292 503310998973644472992171 := by
  unfold tailWord_1470292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26812977394695332363574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35750636526260443151432753 26812977394695332363574565)
  ·
    refine ⟨5027433261505374818170231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26812977394695332363574565 5027433261505374818170231)
    ·
      refine ⟨7541149892258062227255347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027433261505374818170231 7541149892258062227255347)
      ·
        refine ⟨11311724838387093340883021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7541149892258062227255347 11311724838387093340883021)
        ·
          refine ⟨4241896814395160002831133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11311724838387093340883021 4241896814395160002831133)
          ·
            refine ⟨1590711305398185001061675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4241896814395160002831133 1590711305398185001061675)
            ·
              refine ⟨2386066958097277501592513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590711305398185001061675 2386066958097277501592513)
              ·
                refine ⟨1789550218572958126194385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386066958097277501592513 1789550218572958126194385)
                ·
                  refine ⟨1342162663929718594645789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789550218572958126194385 1342162663929718594645789)
                  ·
                    refine ⟨503310998973644472992171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342162663929718594645789 503310998973644472992171)
                    ·
                      rfl

theorem cell22_1470292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1470292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470292 prefixEnd_1470292 := by exact prefixLift 1470292
  have htrace : WordTrace (prefixWord ++ tailWord_1470292) baseStart_1470292 baseEnd_1470292 := by
    simpa [prefixWord, tailWord_1470292, baseEnd_1470292] using wordTrace_append hprefix tailTrace_1470292
  have hstable : (prefixWord ++ tailWord_1470292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470292).length < 2 ^ (prefixWord ++ tailWord_1470292).sum := by decide
  have hdescent : baseEnd_1470292 < baseStart_1470292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470303 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 3, 3]
def baseStart_1470303 : Nat := 118140960795 + 1470303 * 2 ^ 59
def prefixEnd_1470303 : Nat := 4983230072969 + 3 ^ 40 * 1470303 * 2
def baseEnd_1470303 : Nat := 503314764498444110967137

theorem tailTrace_1470303 : CollatzResearch.WordTrace tailWord_1470303 prefixEnd_1470303 503314764498444110967137 := by
  unfold tailWord_1470303
  simp only [CollatzResearch.WordTrace]
  refine ⟨53626355992350813605799563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35750903994900542403866375 53626355992350813605799563)
  ·
    refine ⟨80439533988526220408699345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53626355992350813605799563 80439533988526220408699345)
    ·
      refine ⟨60329650491394665306524509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80439533988526220408699345 60329650491394665306524509)
      ·
        refine ⟨22623618934272999489946691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60329650491394665306524509 22623618934272999489946691)
        ·
          refine ⟨33935428401409499234920037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22623618934272999489946691 33935428401409499234920037)
          ·
            refine ⟨6362892825264281106547507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33935428401409499234920037 6362892825264281106547507)
            ·
              refine ⟨9544339237896421659821261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362892825264281106547507 9544339237896421659821261)
              ·
                refine ⟨3579127214211158122432973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9544339237896421659821261 3579127214211158122432973)
                ·
                  refine ⟨1342172705329184295912365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3579127214211158122432973 1342172705329184295912365)
                  ·
                    refine ⟨503314764498444110967137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342172705329184295912365 503314764498444110967137)
                    ·
                      rfl

theorem cell22_1470303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_1470303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470303 prefixEnd_1470303 := by exact prefixLift 1470303
  have htrace : WordTrace (prefixWord ++ tailWord_1470303) baseStart_1470303 baseEnd_1470303 := by
    simpa [prefixWord, tailWord_1470303, baseEnd_1470303] using wordTrace_append hprefix tailTrace_1470303
  have hstable : (prefixWord ++ tailWord_1470303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470303).length < 2 ^ (prefixWord ++ tailWord_1470303).sum := by decide
  have hdescent : baseEnd_1470303 < baseStart_1470303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470367 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 5]
def baseStart_1470367 : Nat := 118140960795 + 1470367 * 2 ^ 59
def prefixEnd_1470367 : Nat := 4983230072969 + 3 ^ 40 * 1470367 * 2
def baseEnd_1470367 : Nat := 167778891002123092455647

theorem tailTrace_1470367 : CollatzResearch.WordTrace tailWord_1470367 prefixEnd_1470367 167778891002123092455647 := by
  unfold tailWord_1470367
  simp only [CollatzResearch.WordTrace]
  refine ⟨53628690264118952536129355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35752460176079301690752903 53628690264118952536129355)
  ·
    refine ⟨80443035396178428804194033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53628690264118952536129355 80443035396178428804194033)
    ·
      refine ⟨60332276547133821603145525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80443035396178428804194033 60332276547133821603145525)
      ·
        refine ⟨5656150926293795775294893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60332276547133821603145525 5656150926293795775294893)
        ·
          refine ⟨2121056597360173415735585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5656150926293795775294893 2121056597360173415735585)
          ·
            refine ⟨1590792448020130061801689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121056597360173415735585 1590792448020130061801689)
            ·
              refine ⟨1193094336015097546351267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590792448020130061801689 1193094336015097546351267)
              ·
                refine ⟨1789641504022646319526901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193094336015097546351267 1789641504022646319526901)
                ·
                  refine ⟨167778891002123092455647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1789641504022646319526901 167778891002123092455647)
                  ·
                    rfl

theorem cell22_1470367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 5].length) (baseStart_1470367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470367 prefixEnd_1470367 := by exact prefixLift 1470367
  have htrace : WordTrace (prefixWord ++ tailWord_1470367) baseStart_1470367 baseEnd_1470367 := by
    simpa [prefixWord, tailWord_1470367, baseEnd_1470367] using wordTrace_append hprefix tailTrace_1470367
  have hstable : (prefixWord ++ tailWord_1470367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470367).length < 2 ^ (prefixWord ++ tailWord_1470367).sum := by decide
  have hdescent : baseEnd_1470367 < baseStart_1470367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470393 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_1470393 : Nat := 118140960795 + 1470393 * 2 ^ 59
def prefixEnd_1470393 : Nat := 4983230072969 + 3 ^ 40 * 1470393 * 2
def baseEnd_1470393 : Nat := 503345573337713876216861

theorem tailTrace_1470393 : CollatzResearch.WordTrace tailWord_1470393 prefixEnd_1470393 503345573337713876216861 := by
  unfold tailWord_1470393
  simp only [CollatzResearch.WordTrace]
  refine ⟨53629638562024758976575833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35753092374683172651050555 53629638562024758976575833)
  ·
    refine ⟨40222228921518569232431875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53629638562024758976575833 40222228921518569232431875)
    ·
      refine ⟨60333343382277853848647813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40222228921518569232431875 60333343382277853848647813)
      ·
        refine ⟨11312501884177097596621465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60333343382277853848647813 11312501884177097596621465)
        ·
          refine ⟨8484376413132823197466099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11312501884177097596621465 8484376413132823197466099)
          ·
            refine ⟨12726564619699234796199149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484376413132823197466099 12726564619699234796199149)
            ·
              refine ⟨4772461732387213048574681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12726564619699234796199149 4772461732387213048574681)
              ·
                refine ⟨3579346299290409786431011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772461732387213048574681 3579346299290409786431011)
                ·
                  refine ⟨5369019448935614679646517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579346299290409786431011 5369019448935614679646517)
                  ·
                    refine ⟨503345573337713876216861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5369019448935614679646517 503345573337713876216861)
                    ·
                      rfl

theorem cell22_1470393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_1470393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470393 prefixEnd_1470393 := by exact prefixLift 1470393
  have htrace : WordTrace (prefixWord ++ tailWord_1470393) baseStart_1470393 baseEnd_1470393 := by
    simpa [prefixWord, tailWord_1470393, baseEnd_1470393] using wordTrace_append hprefix tailTrace_1470393
  have hstable : (prefixWord ++ tailWord_1470393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470393).length < 2 ^ (prefixWord ++ tailWord_1470393).sum := by decide
  have hdescent : baseEnd_1470393 < baseStart_1470393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470397 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_1470397 : Nat := 118140960795 + 1470397 * 2 ^ 59
def prefixEnd_1470397 : Nat := 4983230072969 + 3 ^ 40 * 1470397 * 2
def baseEnd_1470397 : Nat := 503346942619459199116849

theorem tailTrace_1470397 : CollatzResearch.WordTrace tailWord_1470397 prefixEnd_1470397 503346942619459199116849 := by
  unfold tailWord_1470397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53629784454010267659721445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35753189636006845106480963 53629784454010267659721445)
  ·
    refine ⟨10055584585126925186197771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53629784454010267659721445 10055584585126925186197771)
    ·
      refine ⟨15083376877690387779296657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10055584585126925186197771 15083376877690387779296657)
      ·
        refine ⟨11312532658267790834472493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15083376877690387779296657 11312532658267790834472493)
        ·
          refine ⟨4242199746850421562927185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11312532658267790834472493 4242199746850421562927185)
          ·
            refine ⟨3181649810137816172195389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242199746850421562927185 3181649810137816172195389)
            ·
              refine ⟨1193118678801681064573271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3181649810137816172195389 1193118678801681064573271)
              ·
                refine ⟨1789678018202521596859907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193118678801681064573271 1789678018202521596859907)
                ·
                  refine ⟨2684517027303782395289861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789678018202521596859907 2684517027303782395289861)
                  ·
                    refine ⟨503346942619459199116849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684517027303782395289861 503346942619459199116849)
                    ·
                      rfl

theorem cell22_1470397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_1470397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470397 prefixEnd_1470397 := by exact prefixLift 1470397
  have htrace : WordTrace (prefixWord ++ tailWord_1470397) baseStart_1470397 baseEnd_1470397 := by
    simpa [prefixWord, tailWord_1470397, baseEnd_1470397] using wordTrace_append hprefix tailTrace_1470397
  have hstable : (prefixWord ++ tailWord_1470397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470397).length < 2 ^ (prefixWord ++ tailWord_1470397).sum := by decide
  have hdescent : baseEnd_1470397 < baseStart_1470397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470410 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1470410 : Nat := 118140960795 + 1470410 * 2 ^ 59
def prefixEnd_1470410 : Nat := 4983230072969 + 3 ^ 40 * 1470410 * 2
def baseEnd_1470410 : Nat := 503351392785131498541809

theorem tailTrace_1470410 : CollatzResearch.WordTrace tailWord_1470410 prefixEnd_1470410 503351392785131498541809 := by
  unfold tailWord_1470410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13407564650740792719986171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35753505735308780586629789 13407564650740792719986171)
  ·
    refine ⟨20111346976111189079979257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13407564650740792719986171 20111346976111189079979257)
    ·
      refine ⟨15083510232083391809984443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20111346976111189079979257 15083510232083391809984443)
      ·
        refine ⟨22625265348125087714976665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15083510232083391809984443 22625265348125087714976665)
        ·
          refine ⟨16968949011093815786232499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22625265348125087714976665 16968949011093815786232499)
          ·
            refine ⟨25453423516640723679348749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16968949011093815786232499 25453423516640723679348749)
            ·
              refine ⟨9545033818740271379755781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25453423516640723679348749 9545033818740271379755781)
              ·
                refine ⟨1789693841013800883704209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9545033818740271379755781 1789693841013800883704209)
                ·
                  refine ⟨1342270380760350662778157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789693841013800883704209 1342270380760350662778157)
                  ·
                    refine ⟨503351392785131498541809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342270380760350662778157 503351392785131498541809)
                    ·
                      rfl

theorem cell22_1470410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1470410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470410 prefixEnd_1470410 := by exact prefixLift 1470410
  have htrace : WordTrace (prefixWord ++ tailWord_1470410) baseStart_1470410 baseEnd_1470410 := by
    simpa [prefixWord, tailWord_1470410, baseEnd_1470410] using wordTrace_append hprefix tailTrace_1470410
  have hstable : (prefixWord ++ tailWord_1470410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470410).length < 2 ^ (prefixWord ++ tailWord_1470410).sum := by decide
  have hdescent : baseEnd_1470410 < baseStart_1470410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470412 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1470412 : Nat := 118140960795 + 1470412 * 2 ^ 59
def prefixEnd_1470412 : Nat := 4983230072969 + 3 ^ 40 * 1470412 * 2
def baseEnd_1470412 : Nat := 167784025808668053330601

theorem tailTrace_1470412 : CollatzResearch.WordTrace tailWord_1470412 prefixEnd_1470412 167784025808668053330601 := by
  unfold tailWord_1470412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815165774477962610758745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35753554365970616814344993 26815165774477962610758745)
  ·
    refine ⟨20111374330858471958069059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26815165774477962610758745 20111374330858471958069059)
    ·
      refine ⟨30167061496287707937103589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20111374330858471958069059 30167061496287707937103589)
      ·
        refine ⟨5656324030553945238206923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30167061496287707937103589 5656324030553945238206923)
        ·
          refine ⟨8484486045830917857310385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656324030553945238206923 8484486045830917857310385)
          ·
            refine ⟨6363364534373188392982789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484486045830917857310385 6363364534373188392982789)
            ·
              refine ⟨1193130850194972823684273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6363364534373188392982789 1193130850194972823684273)
              ·
                refine ⟨894848137646229617763205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193130850194972823684273 894848137646229617763205)
                ·
                  refine ⟨167784025808668053330601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 894848137646229617763205 167784025808668053330601)
                  ·
                    rfl

theorem cell22_1470412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1470412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470412 prefixEnd_1470412 := by exact prefixLift 1470412
  have htrace : WordTrace (prefixWord ++ tailWord_1470412) baseStart_1470412 baseEnd_1470412 := by
    simpa [prefixWord, tailWord_1470412, baseEnd_1470412] using wordTrace_append hprefix tailTrace_1470412
  have hstable : (prefixWord ++ tailWord_1470412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470412).length < 2 ^ (prefixWord ++ tailWord_1470412).sum := by decide
  have hdescent : baseEnd_1470412 < baseStart_1470412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470472 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_1470472 : Nat := 118140960795 + 1470472 * 2 ^ 59
def prefixEnd_1470472 : Nat := 4983230072969 + 3 ^ 40 * 1470472 * 2
def baseEnd_1470472 : Nat := 503372616652184003491619

theorem tailTrace_1470472 : CollatzResearch.WordTrace tailWord_1470472 prefixEnd_1470472 503372616652184003491619 := by
  unfold tailWord_1470472
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816259964369277734350835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35755013285825703645801113 26816259964369277734350835)
  ·
    refine ⟨40224389946553916601526253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26816259964369277734350835 40224389946553916601526253)
    ·
      refine ⟨15084146229957718725572345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40224389946553916601526253 15084146229957718725572345)
      ·
        refine ⟨11313109672468289044179259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15084146229957718725572345 11313109672468289044179259)
        ·
          refine ⟨16969664508702433566268889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11313109672468289044179259 16969664508702433566268889)
          ·
            refine ⟨12727248381526825174701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16969664508702433566268889 12727248381526825174701667)
            ·
              refine ⟨19090872572290237762052501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12727248381526825174701667 19090872572290237762052501)
              ·
                refine ⟨894884651826104895096211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19090872572290237762052501 894884651826104895096211)
                ·
                  refine ⟨1342326977739157342644317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894884651826104895096211 1342326977739157342644317)
                  ·
                    refine ⟨503372616652184003491619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342326977739157342644317 503372616652184003491619)
                    ·
                      rfl

theorem cell22_1470472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_1470472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470472 prefixEnd_1470472 := by exact prefixLift 1470472
  have htrace : WordTrace (prefixWord ++ tailWord_1470472) baseStart_1470472 baseEnd_1470472 := by
    simpa [prefixWord, tailWord_1470472, baseEnd_1470472] using wordTrace_append hprefix tailTrace_1470472
  have hstable : (prefixWord ++ tailWord_1470472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470472).length < 2 ^ (prefixWord ++ tailWord_1470472).sum := by decide
  have hdescent : baseEnd_1470472 < baseStart_1470472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470483 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 5]
def baseStart_1470483 : Nat := 118140960795 + 1470483 * 2 ^ 59
def prefixEnd_1470483 : Nat := 4983230072969 + 3 ^ 40 * 1470483 * 2
def baseEnd_1470483 : Nat := 503376382176983641466585

theorem tailTrace_1470483 : CollatzResearch.WordTrace tailWord_1470483 prefixEnd_1470483 503376382176983641466585 := by
  unfold tailWord_1470483
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632921131698704347352103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35755280754465802898234735 53632921131698704347352103)
  ·
    refine ⟨80449381697548056521028155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53632921131698704347352103 80449381697548056521028155)
    ·
      refine ⟨120674072546322084781542233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80449381697548056521028155 120674072546322084781542233)
      ·
        refine ⟨90505554409741563586156675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120674072546322084781542233 90505554409741563586156675)
        ·
          refine ⟨135758331614612345379235013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90505554409741563586156675 135758331614612345379235013)
          ·
            refine ⟨25454687177739814758606565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135758331614612345379235013 25454687177739814758606565)
            ·
              refine ⟨4772753845826215267238731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25454687177739814758606565 4772753845826215267238731)
              ·
                refine ⟨7159130768739322900858097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772753845826215267238731 7159130768739322900858097)
                ·
                  refine ⟨5369348076554492175643573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7159130768739322900858097 5369348076554492175643573)
                  ·
                    refine ⟨503376382176983641466585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5369348076554492175643573 503376382176983641466585)
                    ·
                      rfl

theorem cell22_1470483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_1470483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470483 prefixEnd_1470483 := by exact prefixLift 1470483
  have htrace : WordTrace (prefixWord ++ tailWord_1470483) baseStart_1470483 baseEnd_1470483 := by
    simpa [prefixWord, tailWord_1470483, baseEnd_1470483] using wordTrace_append hprefix tailTrace_1470483
  have hstable : (prefixWord ++ tailWord_1470483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470483).length < 2 ^ (prefixWord ++ tailWord_1470483).sum := by decide
  have hdescent : baseEnd_1470483 < baseStart_1470483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470506 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1470506 : Nat := 118140960795 + 1470506 * 2 ^ 59
def prefixEnd_1470506 : Nat := 4983230072969 + 3 ^ 40 * 1470506 * 2
def baseEnd_1470506 : Nat := 503384255547019248141515

theorem tailTrace_1470506 : CollatzResearch.WordTrace tailWord_1470506 prefixEnd_1470506 503384255547019248141515 := by
  unfold tailWord_1470506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408440002653844818859843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35755840007076919516959581 13408440002653844818859843)
  ·
    refine ⟨20112660003980767228289765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13408440002653844818859843 20112660003980767228289765)
    ·
      refine ⟨3771123750746393855304331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20112660003980767228289765 3771123750746393855304331)
      ·
        refine ⟨5656685626119590782956497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771123750746393855304331 5656685626119590782956497)
        ·
          refine ⟨4242514219589693087217373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656685626119590782956497 4242514219589693087217373)
          ·
            refine ⟨1590942832346134907706515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4242514219589693087217373 1590942832346134907706515)
            ·
              refine ⟨2386414248519202361559773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590942832346134907706515 2386414248519202361559773)
              ·
                refine ⟨894905343194700885584915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386414248519202361559773 894905343194700885584915)
                ·
                  refine ⟨1342358014792051328377373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894905343194700885584915 1342358014792051328377373)
                  ·
                    refine ⟨503384255547019248141515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342358014792051328377373 503384255547019248141515)
                    ·
                      rfl

theorem cell22_1470506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1470506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470506 prefixEnd_1470506 := by exact prefixLift 1470506
  have htrace : WordTrace (prefixWord ++ tailWord_1470506) baseStart_1470506 baseEnd_1470506 := by
    simpa [prefixWord, tailWord_1470506, baseEnd_1470506] using wordTrace_append hprefix tailTrace_1470506
  have hstable : (prefixWord ++ tailWord_1470506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470506).length < 2 ^ (prefixWord ++ tailWord_1470506).sum := by decide
  have hdescent : baseEnd_1470506 < baseStart_1470506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470515 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 1, 4]
def baseStart_1470515 : Nat := 118140960795 + 1470515 * 2 ^ 59
def prefixEnd_1470515 : Nat := 4983230072969 + 3 ^ 40 * 1470515 * 2
def baseEnd_1470515 : Nat := 503387336430946224666487

theorem tailTrace_1470515 : CollatzResearch.WordTrace tailWord_1470515 prefixEnd_1470515 503387336430946224666487 := by
  unfold tailWord_1470515
  simp only [CollatzResearch.WordTrace]
  refine ⟨53634088267582773812516999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35756058845055182541677999 53634088267582773812516999)
  ·
    refine ⟨80451132401374160718775499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53634088267582773812516999 80451132401374160718775499)
    ·
      refine ⟨120676698602061241078163249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80451132401374160718775499 120676698602061241078163249)
      ·
        refine ⟨90507523951545930808622437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120676698602061241078163249 90507523951545930808622437)
        ·
          refine ⟨16970160740914862026616707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90507523951545930808622437 16970160740914862026616707)
          ·
            refine ⟨25455241111372293039925061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16970160740914862026616707 25455241111372293039925061)
            ·
              refine ⟨4772857708382304944985949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25455241111372293039925061 4772857708382304944985949)
              ·
                refine ⟨1789821640643364354369731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772857708382304944985949 1789821640643364354369731)
                ·
                  refine ⟨2684732460965046531554597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789821640643364354369731 2684732460965046531554597)
                  ·
                    refine ⟨503387336430946224666487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684732460965046531554597 503387336430946224666487)
                    ·
                      rfl

theorem cell22_1470515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_1470515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470515 prefixEnd_1470515 := by exact prefixLift 1470515
  have htrace : WordTrace (prefixWord ++ tailWord_1470515) baseStart_1470515 baseEnd_1470515 := by
    simpa [prefixWord, tailWord_1470515, baseEnd_1470515] using wordTrace_append hprefix tailTrace_1470515
  have hstable : (prefixWord ++ tailWord_1470515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470515).length < 2 ^ (prefixWord ++ tailWord_1470515).sum := by decide
  have hdescent : baseEnd_1470515 < baseStart_1470515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470560 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_1470560 : Nat := 118140960795 + 1470560 * 2 ^ 59
def prefixEnd_1470560 : Nat := 4983230072969 + 3 ^ 40 * 1470560 * 2
def baseEnd_1470560 : Nat := 503402740850581107291349

theorem tailTrace_1470560 : CollatzResearch.WordTrace tailWord_1470560 prefixEnd_1470560 503402740850581107291349 := by
  unfold tailWord_1470560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26817864776209873248952567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35757153034946497665270089 26817864776209873248952567)
  ·
    refine ⟨40226797164314809873428851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26817864776209873248952567 40226797164314809873428851)
    ·
      refine ⟨60340195746472214810143277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40226797164314809873428851 60340195746472214810143277)
      ·
        refine ⟨22627573404927080553803729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60340195746472214810143277 22627573404927080553803729)
        ·
          refine ⟨16970680053695310415352797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22627573404927080553803729 16970680053695310415352797)
          ·
            refine ⟨6364005020135741405757299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16970680053695310415352797 6364005020135741405757299)
            ·
              refine ⟨9546007530203612108635949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364005020135741405757299 9546007530203612108635949)
              ·
                refine ⟨3579752823826354540738481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9546007530203612108635949 3579752823826354540738481)
                ·
                  refine ⟨2684814617869765905553861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579752823826354540738481 2684814617869765905553861)
                  ·
                    refine ⟨503402740850581107291349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684814617869765905553861 503402740850581107291349)
                    ·
                      rfl

theorem cell22_1470560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_1470560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470560 prefixEnd_1470560 := by exact prefixLift 1470560
  have htrace : WordTrace (prefixWord ++ tailWord_1470560) baseStart_1470560 baseEnd_1470560 := by
    simpa [prefixWord, tailWord_1470560, baseEnd_1470560] using wordTrace_append hprefix tailTrace_1470560
  have hstable : (prefixWord ++ tailWord_1470560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470560).length < 2 ^ (prefixWord ++ tailWord_1470560).sum := by decide
  have hdescent : baseEnd_1470560 < baseStart_1470560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470603 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 11]
def baseStart_1470603 : Nat := 118140960795 + 1470603 * 2 ^ 59
def prefixEnd_1470603 : Nat := 4983230072969 + 3 ^ 40 * 1470603 * 2
def baseEnd_1470603 : Nat := 167805820209781109488739

theorem tailTrace_1470603 : CollatzResearch.WordTrace tailWord_1470603 prefixEnd_1470603 167805820209781109488739 := by
  unfold tailWord_1470603
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637297891263964841720463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35758198594175976561146975 53637297891263964841720463)
  ·
    refine ⟨80455946836895947262580695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53637297891263964841720463 80455946836895947262580695)
    ·
      refine ⟨120683920255343920893871043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80455946836895947262580695 120683920255343920893871043)
      ·
        refine ⟨181025880383015881340806565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120683920255343920893871043 181025880383015881340806565)
        ·
          refine ⟨33942352571815477751401231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181025880383015881340806565 33942352571815477751401231)
          ·
            refine ⟨50913528857723216627101847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33942352571815477751401231 50913528857723216627101847)
            ·
              refine ⟨76370293286584824940652771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50913528857723216627101847 76370293286584824940652771)
              ·
                refine ⟨114555439929877237410979157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76370293286584824940652771 114555439929877237410979157)
                ·
                  refine ⟨167805820209781109488739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 114555439929877237410979157 167805820209781109488739)
                  ·
                    rfl

theorem cell22_1470603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_1470603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470603 prefixEnd_1470603 := by exact prefixLift 1470603
  have htrace : WordTrace (prefixWord ++ tailWord_1470603) baseStart_1470603 baseEnd_1470603 := by
    simpa [prefixWord, tailWord_1470603, baseEnd_1470603] using wordTrace_append hprefix tailTrace_1470603
  have hstable : (prefixWord ++ tailWord_1470603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470603).length < 2 ^ (prefixWord ++ tailWord_1470603).sum := by decide
  have hdescent : baseEnd_1470603 < baseStart_1470603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470620 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1470620 : Nat := 118140960795 + 1470620 * 2 ^ 59
def prefixEnd_1470620 : Nat := 4983230072969 + 3 ^ 40 * 1470620 * 2
def baseEnd_1470620 : Nat := 167807760025586983597055

theorem tailTrace_1470620 : CollatzResearch.WordTrace tailWord_1470620 prefixEnd_1470620 167807760025586983597055 := by
  unfold tailWord_1470620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818958966101188372544657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35758611954801584496726209 26818958966101188372544657)
  ·
    refine ⟨20114219224575891279408493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26818958966101188372544657 20114219224575891279408493)
    ·
      refine ⟨7542832209215959229778185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20114219224575891279408493 7542832209215959229778185)
      ·
        refine ⟨5657124156911969422333639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542832209215959229778185 5657124156911969422333639)
        ·
          refine ⟨8485686235367954133500459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657124156911969422333639 8485686235367954133500459)
          ·
            refine ⟨12728529353051931200250689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485686235367954133500459 12728529353051931200250689)
            ·
              refine ⟨9546397014788948400188017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728529353051931200250689 9546397014788948400188017)
              ·
                refine ⟨7159797761091711300141013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9546397014788948400188017 7159797761091711300141013)
                ·
                  refine ⟨167807760025586983597055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7159797761091711300141013 167807760025586983597055)
                  ·
                    rfl

theorem cell22_1470620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1470620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470620 prefixEnd_1470620 := by exact prefixLift 1470620
  have htrace : WordTrace (prefixWord ++ tailWord_1470620) baseStart_1470620 baseEnd_1470620 := by
    simpa [prefixWord, tailWord_1470620, baseEnd_1470620] using wordTrace_append hprefix tailTrace_1470620
  have hstable : (prefixWord ++ tailWord_1470620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470620).length < 2 ^ (prefixWord ++ tailWord_1470620).sum := by decide
  have hdescent : baseEnd_1470620 < baseStart_1470620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470624 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_1470624 : Nat := 118140960795 + 1470624 * 2 ^ 59
def prefixEnd_1470624 : Nat := 4983230072969 + 3 ^ 40 * 1470624 * 2
def baseEnd_1470624 : Nat := 503424649358506273691153

theorem tailTrace_1470624 : CollatzResearch.WordTrace tailWord_1470624 prefixEnd_1470624 503424649358506273691153 := by
  unfold tailWord_1470624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819031912093942714117463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35758709216125256952156617 26819031912093942714117463)
  ·
    refine ⟨40228547868140914071176195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26819031912093942714117463 40228547868140914071176195)
    ·
      refine ⟨60342821802211371106764293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40228547868140914071176195 60342821802211371106764293)
      ·
        refine ⟨11314279087914632082518305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60342821802211371106764293 11314279087914632082518305)
        ·
          refine ⟨8485709315935974061888729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11314279087914632082518305 8485709315935974061888729)
          ·
            refine ⟨6364281986951980546416547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8485709315935974061888729 6364281986951980546416547)
            ·
              refine ⟨9546422980427970819624821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364281986951980546416547 9546422980427970819624821)
              ·
                refine ⟨894977154415122264339827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9546422980427970819624821 894977154415122264339827)
                ·
                  refine ⟨1342465731622683396509741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894977154415122264339827 1342465731622683396509741)
                  ·
                    refine ⟨503424649358506273691153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342465731622683396509741 503424649358506273691153)
                    ·
                      rfl

theorem cell22_1470624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_1470624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470624 prefixEnd_1470624 := by exact prefixLift 1470624
  have htrace : WordTrace (prefixWord ++ tailWord_1470624) baseStart_1470624 baseEnd_1470624 := by
    simpa [prefixWord, tailWord_1470624, baseEnd_1470624] using wordTrace_append hprefix tailTrace_1470624
  have hstable : (prefixWord ++ tailWord_1470624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470624).length < 2 ^ (prefixWord ++ tailWord_1470624).sum := by decide
  have hdescent : baseEnd_1470624 < baseStart_1470624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470637 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1470637 : Nat := 118140960795 + 1470637 * 2 ^ 59
def prefixEnd_1470637 : Nat := 4983230072969 + 3 ^ 40 * 1470637 * 2
def baseEnd_1470637 : Nat := 167809699841392857705371

theorem tailTrace_1470637 : CollatzResearch.WordTrace tailWord_1470637 prefixEnd_1470637 167809699841392857705371 := by
  unfold tailWord_1470637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53638537973140788648458165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35759025315427192432305443 53638537973140788648458165)
  ·
    refine ⟨5028612934981948935792953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53638537973140788648458165 5028612934981948935792953)
    ·
      refine ⟨3771459701236461701844715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5028612934981948935792953 3771459701236461701844715)
      ·
        refine ⟨5657189551854692552767073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771459701236461701844715 5657189551854692552767073)
        ·
          refine ⟨4242892163891019414575305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657189551854692552767073 4242892163891019414575305)
          ·
            refine ⟨3182169122918264560931479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242892163891019414575305 3182169122918264560931479)
            ·
              refine ⟨4773253684377396841397219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182169122918264560931479 4773253684377396841397219)
              ·
                refine ⟨7159880526566095262095829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773253684377396841397219 7159880526566095262095829)
                ·
                  refine ⟨167809699841392857705371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7159880526566095262095829 167809699841392857705371)
                  ·
                    rfl

theorem cell22_1470637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1470637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470637 prefixEnd_1470637 := by exact prefixLift 1470637
  have htrace : WordTrace (prefixWord ++ tailWord_1470637) baseStart_1470637 baseEnd_1470637 := by
    simpa [prefixWord, tailWord_1470637, baseEnd_1470637] using wordTrace_append hprefix tailTrace_1470637
  have hstable : (prefixWord ++ tailWord_1470637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470637).length < 2 ^ (prefixWord ++ tailWord_1470637).sum := by decide
  have hdescent : baseEnd_1470637 < baseStart_1470637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470650 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1470650 : Nat := 118140960795 + 1470650 * 2 ^ 59
def prefixEnd_1470650 : Nat := 4983230072969 + 3 ^ 40 * 1470650 * 2
def baseEnd_1470650 : Nat := 503433549689850872541073

theorem tailTrace_1470650 : CollatzResearch.WordTrace tailWord_1470650 prefixEnd_1470650 503433549689850872541073 := by
  unfold tailWord_1470650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13409753030523422967170351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35759341414729127912454269 13409753030523422967170351)
  ·
    refine ⟨20114629545785134450755527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13409753030523422967170351 20114629545785134450755527)
    ·
      refine ⟨30171944318677701676133291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20114629545785134450755527 30171944318677701676133291)
      ·
        refine ⟨45257916478016552514199937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30171944318677701676133291 45257916478016552514199937)
        ·
          refine ⟨33943437358512414385649953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45257916478016552514199937 33943437358512414385649953)
          ·
            refine ⟨25457578018884310789237465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33943437358512414385649953 25457578018884310789237465)
            ·
              refine ⟨19093183514163233091928099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25457578018884310789237465 19093183514163233091928099)
              ·
                refine ⟨28639775271244849637892149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19093183514163233091928099 28639775271244849637892149)
                ·
                  refine ⟨2684978931679204653552389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28639775271244849637892149 2684978931679204653552389)
                  ·
                    refine ⟨503433549689850872541073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2684978931679204653552389 503433549689850872541073)
                    ·
                      rfl

theorem cell22_1470650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1470650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470650 prefixEnd_1470650 := by exact prefixLift 1470650
  have htrace : WordTrace (prefixWord ++ tailWord_1470650) baseStart_1470650 baseEnd_1470650 := by
    simpa [prefixWord, tailWord_1470650, baseEnd_1470650] using wordTrace_append hprefix tailTrace_1470650
  have hstable : (prefixWord ++ tailWord_1470650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470650).length < 2 ^ (prefixWord ++ tailWord_1470650).sum := by decide
  have hdescent : baseEnd_1470650 < baseStart_1470650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470667 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 1, 4]
def baseStart_1470667 : Nat := 118140960795 + 1470667 * 2 ^ 59
def prefixEnd_1470667 : Nat := 4983230072969 + 3 ^ 40 * 1470667 * 2
def baseEnd_1470667 : Nat := 503439369137268494866021

theorem tailTrace_1470667 : CollatzResearch.WordTrace tailWord_1470667 prefixEnd_1470667 503439369137268494866021 := by
  unfold tailWord_1470667
  simp only [CollatzResearch.WordTrace]
  refine ⟨53639632163032103772050255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35759754775354735848033503 53639632163032103772050255)
  ·
    refine ⟨80459448244548155658075383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53639632163032103772050255 80459448244548155658075383)
    ·
      refine ⟨120689172366822233487113075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80459448244548155658075383 120689172366822233487113075)
      ·
        refine ⟨181033758550233350230669613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120689172366822233487113075 181033758550233350230669613)
        ·
          refine ⟨67887659456337506336501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181033758550233350230669613 67887659456337506336501105)
          ·
            refine ⟨50915744592253129752375829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67887659456337506336501105 50915744592253129752375829)
            ·
              refine ⟨2386675527761865457142617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50915744592253129752375829 2386675527761865457142617)
              ·
                refine ⟨1790006645821399092856963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386675527761865457142617 1790006645821399092856963)
                ·
                  refine ⟨2685009968732098639285445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790006645821399092856963 2685009968732098639285445)
                  ·
                    refine ⟨503439369137268494866021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2685009968732098639285445 503439369137268494866021)
                    ·
                      rfl

theorem cell22_1470667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_1470667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470667 prefixEnd_1470667 := by exact prefixLift 1470667
  have htrace : WordTrace (prefixWord ++ tailWord_1470667) baseStart_1470667 baseEnd_1470667 := by
    simpa [prefixWord, tailWord_1470667, baseEnd_1470667] using wordTrace_append hprefix tailTrace_1470667
  have hstable : (prefixWord ++ tailWord_1470667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470667).length < 2 ^ (prefixWord ++ tailWord_1470667).sum := by decide
  have hdescent : baseEnd_1470667 < baseStart_1470667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470699 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 4]
def baseStart_1470699 : Nat := 118140960795 + 1470699 * 2 ^ 59
def prefixEnd_1470699 : Nat := 4983230072969 + 3 ^ 40 * 1470699 * 2
def baseEnd_1470699 : Nat := 167816774463743692688641

theorem tailTrace_1470699 : CollatzResearch.WordTrace tailWord_1470699 prefixEnd_1470699 167816774463743692688641 := by
  unfold tailWord_1470699
  simp only [CollatzResearch.WordTrace]
  refine ⟨53640799298916173237215151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35760532865944115491476767 53640799298916173237215151)
  ·
    refine ⟨80461198948374259855822727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53640799298916173237215151 80461198948374259855822727)
    ·
      refine ⟨120691798422561389783734091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80461198948374259855822727 120691798422561389783734091)
      ·
        refine ⟨181037697633842084675601137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120691798422561389783734091 181037697633842084675601137)
        ·
          refine ⟨135778273225381563506700853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181037697633842084675601137 135778273225381563506700853)
          ·
            refine ⟨12729213114879521578753205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135778273225381563506700853 12729213114879521578753205)
            ·
              refine ⟨1193363729519955148008113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12729213114879521578753205 1193363729519955148008113)
              ·
                refine ⟨895022797139966361006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193363729519955148008113 895022797139966361006085)
                ·
                  refine ⟨167816774463743692688641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895022797139966361006085 167816774463743692688641)
                  ·
                    rfl

theorem cell22_1470699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 4].length) (baseStart_1470699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470699 prefixEnd_1470699 := by exact prefixLift 1470699
  have htrace : WordTrace (prefixWord ++ tailWord_1470699) baseStart_1470699 baseEnd_1470699 := by
    simpa [prefixWord, tailWord_1470699, baseEnd_1470699] using wordTrace_append hprefix tailTrace_1470699
  have hstable : (prefixWord ++ tailWord_1470699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470699).length < 2 ^ (prefixWord ++ tailWord_1470699).sum := by decide
  have hdescent : baseEnd_1470699 < baseStart_1470699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470714 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_1470714 : Nat := 118140960795 + 1470714 * 2 ^ 59
def prefixEnd_1470714 : Nat := 4983230072969 + 3 ^ 40 * 1470714 * 2
def baseEnd_1470714 : Nat := 503455458197776038940877

theorem tailTrace_1470714 : CollatzResearch.WordTrace tailWord_1470714 prefixEnd_1470714 503455458197776038940877 := by
  unfold tailWord_1470714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410336598465457699752799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35760897595907887199340797 13410336598465457699752799)
  ·
    refine ⟨20115504897698186549629199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13410336598465457699752799 20115504897698186549629199)
    ·
      refine ⟨30173257346547279824443799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20115504897698186549629199 30173257346547279824443799)
      ·
        refine ⟨45259886019820919736665699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30173257346547279824443799 45259886019820919736665699)
        ·
          refine ⟨67889829029731379604998549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45259886019820919736665699 67889829029731379604998549)
          ·
            refine ⟨3182335735768658418984307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67889829029731379604998549 3182335735768658418984307)
            ·
              refine ⟨4773503603652987628476461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182335735768658418984307 4773503603652987628476461)
              ·
                refine ⟨1790063851369870360678673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4773503603652987628476461 1790063851369870360678673)
                ·
                  refine ⟨1342547888527402770509005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790063851369870360678673 1342547888527402770509005)
                  ·
                    refine ⟨503455458197776038940877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342547888527402770509005 503455458197776038940877)
                    ·
                      rfl

theorem cell22_1470714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_1470714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470714 prefixEnd_1470714 := by exact prefixLift 1470714
  have htrace : WordTrace (prefixWord ++ tailWord_1470714) baseStart_1470714 baseEnd_1470714 := by
    simpa [prefixWord, tailWord_1470714, baseEnd_1470714] using wordTrace_append hprefix tailTrace_1470714
  have hstable : (prefixWord ++ tailWord_1470714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470714).length < 2 ^ (prefixWord ++ tailWord_1470714).sum := by decide
  have hdescent : baseEnd_1470714 < baseStart_1470714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470750 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1470750 : Nat := 118140960795 + 1470750 * 2 ^ 59
def prefixEnd_1470750 : Nat := 4983230072969 + 3 ^ 40 * 1470750 * 2
def baseEnd_1470750 : Nat := 167822593911161315013589

theorem tailTrace_1470750 : CollatzResearch.WordTrace tailWord_1470750 prefixEnd_1470750 167822593911161315013589 := by
  unfold tailWord_1470750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705332427716426118415213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35761772947820939298214469 6705332427716426118415213)
  ·
    refine ⟨2514499660393659794405705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6705332427716426118415213 2514499660393659794405705)
    ·
      refine ⟨1885874745295244845804279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2514499660393659794405705 1885874745295244845804279)
      ·
        refine ⟨2828812117942867268706419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885874745295244845804279 2828812117942867268706419)
        ·
          refine ⟨4243218176914300903059629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828812117942867268706419 4243218176914300903059629)
          ·
            refine ⟨1591206816342862838647361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4243218176914300903059629 1591206816342862838647361)
            ·
              refine ⟨1193405112257147128985521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591206816342862838647361 1193405112257147128985521)
              ·
                refine ⟨895053834192860346739141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193405112257147128985521 895053834192860346739141)
                ·
                  refine ⟨167822593911161315013589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895053834192860346739141 167822593911161315013589)
                  ·
                    rfl

theorem cell22_1470750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1470750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470750 prefixEnd_1470750 := by exact prefixLift 1470750
  have htrace : WordTrace (prefixWord ++ tailWord_1470750) baseStart_1470750 baseEnd_1470750 := by
    simpa [prefixWord, tailWord_1470750, baseEnd_1470750] using wordTrace_append hprefix tailTrace_1470750
  have hstable : (prefixWord ++ tailWord_1470750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470750).length < 2 ^ (prefixWord ++ tailWord_1470750).sum := by decide
  have hdescent : baseEnd_1470750 < baseStart_1470750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470868 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1470868 : Nat := 118140960795 + 1470868 * 2 ^ 59
def prefixEnd_1470868 : Nat := 4983230072969 + 3 ^ 40 * 1470868 * 2
def baseEnd_1470868 : Nat := 167836058514990323530135

theorem tailTrace_1470868 : CollatzResearch.WordTrace tailWord_1470868 prefixEnd_1470868 167836058514990323530135 := by
  unfold tailWord_1470868
  simp only [CollatzResearch.WordTrace]
  refine ⟨26823481617651957550058629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35764642156869276733411505 26823481617651957550058629)
  ·
    refine ⟨5029402803309742040635993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26823481617651957550058629 5029402803309742040635993)
    ·
      refine ⟨3772052102482306530476995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029402803309742040635993 3772052102482306530476995)
      ·
        refine ⟨5658078153723459795715493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772052102482306530476995 5658078153723459795715493)
        ·
          refine ⟨1060889653823148711696655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5658078153723459795715493 1060889653823148711696655)
          ·
            refine ⟨1591334480734723067544983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060889653823148711696655 1591334480734723067544983)
            ·
              refine ⟨2387001721102084601317475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591334480734723067544983 2387001721102084601317475)
              ·
                refine ⟨3580502581653126901976213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387001721102084601317475 3580502581653126901976213)
                ·
                  refine ⟨167836058514990323530135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3580502581653126901976213 167836058514990323530135)
                  ·
                    rfl

theorem cell22_1470868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1470868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470868 prefixEnd_1470868 := by exact prefixLift 1470868
  have htrace : WordTrace (prefixWord ++ tailWord_1470868) baseStart_1470868 baseEnd_1470868 := by
    simpa [prefixWord, tailWord_1470868, baseEnd_1470868] using wordTrace_append hprefix tailTrace_1470868
  have hstable : (prefixWord ++ tailWord_1470868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470868).length < 2 ^ (prefixWord ++ tailWord_1470868).sum := by decide
  have hdescent : baseEnd_1470868 < baseStart_1470868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470883 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 2, 3]
def baseStart_1470883 : Nat := 118140960795 + 1470883 * 2 ^ 59
def prefixEnd_1470883 : Nat := 4983230072969 + 3 ^ 40 * 1470883 * 2
def baseEnd_1470883 : Nat := 503513310351515931465359

theorem tailTrace_1470883 : CollatzResearch.WordTrace tailWord_1470883 prefixEnd_1470883 503513310351515931465359 := by
  unfold tailWord_1470883
  simp only [CollatzResearch.WordTrace]
  refine ⟨53647510330249572661913303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35765006886833048441275535 53647510330249572661913303)
  ·
    refine ⟨80471265495374358992869955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53647510330249572661913303 80471265495374358992869955)
    ·
      refine ⟨120706898243061538489304933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80471265495374358992869955 120706898243061538489304933)
      ·
        refine ⟨22632543420574038466744675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120706898243061538489304933 22632543420574038466744675)
        ·
          refine ⟨33948815130861057700117013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22632543420574038466744675 33948815130861057700117013)
          ·
            refine ⟨1591350709259112079692985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33948815130861057700117013 1591350709259112079692985)
            ·
              refine ⟨1193513031944334059769739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591350709259112079692985 1193513031944334059769739)
              ·
                refine ⟨1790269547916501089654609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193513031944334059769739 1790269547916501089654609)
                ·
                  refine ⟨1342702160937375817240957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790269547916501089654609 1342702160937375817240957)
                  ·
                    refine ⟨503513310351515931465359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342702160937375817240957 503513310351515931465359)
                    ·
                      rfl

theorem cell22_1470883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 3].length) (baseStart_1470883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470883 prefixEnd_1470883 := by exact prefixLift 1470883
  have htrace : WordTrace (prefixWord ++ tailWord_1470883) baseStart_1470883 baseEnd_1470883 := by
    simpa [prefixWord, tailWord_1470883, baseEnd_1470883] using wordTrace_append hprefix tailTrace_1470883
  have hstable : (prefixWord ++ tailWord_1470883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470883).length < 2 ^ (prefixWord ++ tailWord_1470883).sum := by decide
  have hdescent : baseEnd_1470883 < baseStart_1470883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470913 : List Nat := [1, 2, 7, 1, 2, 9]
def baseStart_1470913 : Nat := 118140960795 + 1470913 * 2 ^ 59
def prefixEnd_1470913 : Nat := 4983230072969 + 3 ^ 40 * 1470913 * 2
def baseEnd_1470913 : Nat := 6216340493390195718707

theorem tailTrace_1470913 : CollatzResearch.WordTrace tailWord_1470913 prefixEnd_1470913 6216340493390195718707 := by
  unfold tailWord_1470913
  simp only [CollatzResearch.WordTrace]
  refine ⟨53648604520140887785505393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35765736346760591857003595 53648604520140887785505393)
  ·
    refine ⟨40236453390105665839129045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53648604520140887785505393 40236453390105665839129045)
    ·
      refine ⟨943041876330601543104587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40236453390105665839129045 943041876330601543104587)
      ·
        refine ⟨1414562814495902314656881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943041876330601543104587 1414562814495902314656881)
        ·
          refine ⟨1060922110871926735992661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414562814495902314656881 1060922110871926735992661)
          ·
            refine ⟨6216340493390195718707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1060922110871926735992661 6216340493390195718707)
            ·
              rfl

theorem cell22_1470913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 9].length) (baseStart_1470913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470913 prefixEnd_1470913 := by exact prefixLift 1470913
  have htrace : WordTrace (prefixWord ++ tailWord_1470913) baseStart_1470913 baseEnd_1470913 := by
    simpa [prefixWord, tailWord_1470913, baseEnd_1470913] using wordTrace_append hprefix tailTrace_1470913
  have hstable : (prefixWord ++ tailWord_1470913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470913).length < 2 ^ (prefixWord ++ tailWord_1470913).sum := by decide
  have hdescent : baseEnd_1470913 < baseStart_1470913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470967 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1470967 : Nat := 118140960795 + 1470967 * 2 ^ 59
def prefixEnd_1470967 : Nat := 4983230072969 + 3 ^ 40 * 1470967 * 2
def baseEnd_1470967 : Nat := 503542065268167712365101

theorem tailTrace_1470967 : CollatzResearch.WordTrace tailWord_1470967 prefixEnd_1470967 503542065268167712365101 := by
  unfold tailWord_1470967
  simp only [CollatzResearch.WordTrace]
  refine ⟨53650574061945255007971155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35767049374630170005314103 53650574061945255007971155)
  ·
    refine ⟨80475861092917882511956733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53650574061945255007971155 80475861092917882511956733)
    ·
      refine ⟨30178447909844205941983775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80475861092917882511956733 30178447909844205941983775)
      ·
        refine ⟨45267671864766308912975663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30178447909844205941983775 45267671864766308912975663)
        ·
          refine ⟨67901507797149463369463495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45267671864766308912975663 67901507797149463369463495)
          ·
            refine ⟨101852261695724195054195243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67901507797149463369463495 101852261695724195054195243)
            ·
              refine ⟨152778392543586292581292865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101852261695724195054195243 152778392543586292581292865)
              ·
                refine ⟨114583794407689719435969649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152778392543586292581292865 114583794407689719435969649)
                ·
                  refine ⟨85937845805767289576977237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114583794407689719435969649 85937845805767289576977237)
                  ·
                    refine ⟨503542065268167712365101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85937845805767289576977237 503542065268167712365101)
                    ·
                      rfl

theorem cell22_1470967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1470967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470967 prefixEnd_1470967 := by exact prefixLift 1470967
  have htrace : WordTrace (prefixWord ++ tailWord_1470967) baseStart_1470967 baseEnd_1470967 := by
    simpa [prefixWord, tailWord_1470967, baseEnd_1470967] using wordTrace_append hprefix tailTrace_1470967
  have hstable : (prefixWord ++ tailWord_1470967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470967).length < 2 ^ (prefixWord ++ tailWord_1470967).sum := by decide
  have hdescent : baseEnd_1470967 < baseStart_1470967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470986 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_1470986 : Nat := 118140960795 + 1470986 * 2 ^ 59
def prefixEnd_1470986 : Nat := 4983230072969 + 3 ^ 40 * 1470986 * 2
def baseEnd_1470986 : Nat := 167849523118819332046681

theorem tailTrace_1470986 : CollatzResearch.WordTrace tailWord_1470986 prefixEnd_1470986 167849523118819332046681 := by
  unfold tailWord_1470986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412816762219105313228203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35767511365917614168608541 13412816762219105313228203)
  ·
    refine ⟨20119225143328657969842305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412816762219105313228203 20119225143328657969842305)
    ·
      refine ⟨15089418857496493477381729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20119225143328657969842305 15089418857496493477381729)
      ·
        refine ⟨11317064143122370108036297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15089418857496493477381729 11317064143122370108036297)
        ·
          refine ⟨8487798107341777581027223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11317064143122370108036297 8487798107341777581027223)
          ·
            refine ⟨12731697161012666371540835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487798107341777581027223 12731697161012666371540835)
            ·
              refine ⟨19097545741518999557311253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731697161012666371540835 19097545741518999557311253)
              ·
                refine ⟨895197456633703104248965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19097545741518999557311253 895197456633703104248965)
                ·
                  refine ⟨167849523118819332046681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895197456633703104248965 167849523118819332046681)
                  ·
                    rfl

theorem cell22_1470986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_1470986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1470986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1470986 prefixEnd_1470986 := by exact prefixLift 1470986
  have htrace : WordTrace (prefixWord ++ tailWord_1470986) baseStart_1470986 baseEnd_1470986 := by
    simpa [prefixWord, tailWord_1470986, baseEnd_1470986] using wordTrace_append hprefix tailTrace_1470986
  have hstable : (prefixWord ++ tailWord_1470986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470986).length < 2 ^ (prefixWord ++ tailWord_1470986).sum := by decide
  have hdescent : baseEnd_1470986 < baseStart_1470986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471016 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1471016 : Nat := 118140960795 + 1471016 * 2 ^ 59
def prefixEnd_1471016 : Nat := 4983230072969 + 3 ^ 40 * 1471016 * 2
def baseEnd_1471016 : Nat := 503558838969547917889951

theorem tailTrace_1471016 : CollatzResearch.WordTrace tailWord_1471016 prefixEnd_1471016 503558838969547917889951 := by
  unfold tailWord_1471016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826180619383868188252451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35768240825845157584336601 26826180619383868188252451)
  ·
    refine ⟨40239270929075802282378677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26826180619383868188252451 40239270929075802282378677)
    ·
      refine ⟨3772431649600856463973001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40239270929075802282378677 3772431649600856463973001)
      ·
        refine ⟨2829323737200642347979751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772431649600856463973001 2829323737200642347979751)
        ·
          refine ⟨4243985605800963521969627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829323737200642347979751 4243985605800963521969627)
          ·
            refine ⟨6365978408701445282954441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243985605800963521969627 6365978408701445282954441)
            ·
              refine ⟨4774483806526083962215831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6365978408701445282954441 4774483806526083962215831)
              ·
                refine ⟨7161725709789125943323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4774483806526083962215831 7161725709789125943323747)
                ·
                  refine ⟨10742588564683688914985621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7161725709789125943323747 10742588564683688914985621)
                  ·
                    refine ⟨503558838969547917889951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10742588564683688914985621 503558838969547917889951)
                    ·
                      rfl

theorem cell22_1471016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1471016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471016 prefixEnd_1471016 := by exact prefixLift 1471016
  have htrace : WordTrace (prefixWord ++ tailWord_1471016) baseStart_1471016 baseEnd_1471016 := by
    simpa [prefixWord, tailWord_1471016, baseEnd_1471016] using wordTrace_append hprefix tailTrace_1471016
  have hstable : (prefixWord ++ tailWord_1471016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471016).length < 2 ^ (prefixWord ++ tailWord_1471016).sum := by decide
  have hdescent : baseEnd_1471016 < baseStart_1471016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471097 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_1471097 : Nat := 118140960795 + 1471097 * 2 ^ 59
def prefixEnd_1471097 : Nat := 4983230072969 + 3 ^ 40 * 1471097 * 2
def baseEnd_1471097 : Nat := 503586566924890706614703

theorem tailTrace_1471097 : CollatzResearch.WordTrace tailWord_1471097 prefixEnd_1471097 503586566924890706614703 := by
  unfold tailWord_1471097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53655315551474287210203545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35770210367649524806802363 53655315551474287210203545)
  ·
    refine ⟨40241486663605715407652659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53655315551474287210203545 40241486663605715407652659)
    ·
      refine ⟨60362229995408573111478989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40241486663605715407652659 60362229995408573111478989)
      ·
        refine ⟨22635836248278214916804621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60362229995408573111478989 22635836248278214916804621)
        ·
          refine ⟨8488438593104330593801733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22635836248278214916804621 8488438593104330593801733)
          ·
            refine ⟨1591582236207061986337825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8488438593104330593801733 1591582236207061986337825)
            ·
              refine ⟨1193686677155296489753369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591582236207061986337825 1193686677155296489753369)
              ·
                refine ⟨895265007866472367315027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193686677155296489753369 895265007866472367315027)
                ·
                  refine ⟨1342897511799708550972541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895265007866472367315027 1342897511799708550972541)
                  ·
                    refine ⟨503586566924890706614703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342897511799708550972541 503586566924890706614703)
                    ·
                      rfl

theorem cell22_1471097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_1471097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471097 prefixEnd_1471097 := by exact prefixLift 1471097
  have htrace : WordTrace (prefixWord ++ tailWord_1471097) baseStart_1471097 baseEnd_1471097 := by
    simpa [prefixWord, tailWord_1471097, baseEnd_1471097] using wordTrace_append hprefix tailTrace_1471097
  have hstable : (prefixWord ++ tailWord_1471097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471097).length < 2 ^ (prefixWord ++ tailWord_1471097).sum := by decide
  have hdescent : baseEnd_1471097 < baseStart_1471097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471119 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_1471119 : Nat := 118140960795 + 1471119 * 2 ^ 59
def prefixEnd_1471119 : Nat := 4983230072969 + 3 ^ 40 * 1471119 * 2
def baseEnd_1471119 : Nat := 503594097974489982564635

theorem tailTrace_1471119 : CollatzResearch.WordTrace tailWord_1471119 prefixEnd_1471119 503594097974489982564635 := by
  unfold tailWord_1471119
  simp only [CollatzResearch.WordTrace]
  refine ⟨53656117957394584967504411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35770745304929723311669607 53656117957394584967504411)
  ·
    refine ⟨80484176936091877451256617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53656117957394584967504411 80484176936091877451256617)
    ·
      refine ⟨60363132702068908088442463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80484176936091877451256617 60363132702068908088442463)
      ·
        refine ⟨90544699053103362132663695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60363132702068908088442463 90544699053103362132663695)
        ·
          refine ⟨135817048579655043198995543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90544699053103362132663695 135817048579655043198995543)
          ·
            refine ⟨203725572869482564798493315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135817048579655043198995543 203725572869482564798493315)
            ·
              refine ⟨305588359304223847197739973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203725572869482564798493315 305588359304223847197739973)
              ·
                refine ⟨57297817369541971349576245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305588359304223847197739973 57297817369541971349576245)
                ·
                  refine ⟨5371670378394559814022773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57297817369541971349576245 5371670378394559814022773)
                  ·
                    refine ⟨503594097974489982564635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5371670378394559814022773 503594097974489982564635)
                    ·
                      rfl

theorem cell22_1471119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_1471119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471119 prefixEnd_1471119 := by exact prefixLift 1471119
  have htrace : WordTrace (prefixWord ++ tailWord_1471119) baseStart_1471119 baseEnd_1471119 := by
    simpa [prefixWord, tailWord_1471119, baseEnd_1471119] using wordTrace_append hprefix tailTrace_1471119
  have hstable : (prefixWord ++ tailWord_1471119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471119).length < 2 ^ (prefixWord ++ tailWord_1471119).sum := by decide
  have hdescent : baseEnd_1471119 < baseStart_1471119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471166 : List Nat := [4, 2, 1, 1, 2, 1, 2, 9]
def baseStart_1471166 : Nat := 118140960795 + 1471166 * 2 ^ 59
def prefixEnd_1471166 : Nat := 4983230072969 + 3 ^ 40 * 1471166 * 2
def baseEnd_1471166 : Nat := 55956687448333058515499

theorem tailTrace_1471166 : CollatzResearch.WordTrace tailWord_1471166 prefixEnd_1471166 55956687448333058515499 := by
  unfold tailWord_1471166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6707229023528038999308169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35771888125482874662976901 6707229023528038999308169)
  ·
    refine ⟨5030421767646029249481127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6707229023528038999308169 5030421767646029249481127)
    ·
      refine ⟨7545632651469043874221691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030421767646029249481127 7545632651469043874221691)
      ·
        refine ⟨11318448977203565811332537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7545632651469043874221691 11318448977203565811332537)
        ·
          refine ⟨8488836732902674358499403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11318448977203565811332537 8488836732902674358499403)
          ·
            refine ⟨12733255099354011537749105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488836732902674358499403 12733255099354011537749105)
            ·
              refine ⟨9549941324515508653311829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12733255099354011537749105 9549941324515508653311829)
              ·
                refine ⟨55956687448333058515499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9549941324515508653311829 55956687448333058515499)
                ·
                  rfl

theorem cell22_1471166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_1471166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471166 prefixEnd_1471166 := by exact prefixLift 1471166
  have htrace : WordTrace (prefixWord ++ tailWord_1471166) baseStart_1471166 baseEnd_1471166 := by
    simpa [prefixWord, tailWord_1471166, baseEnd_1471166] using wordTrace_append hprefix tailTrace_1471166
  have hstable : (prefixWord ++ tailWord_1471166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471166).length < 2 ^ (prefixWord ++ tailWord_1471166).sum := by decide
  have hdescent : baseEnd_1471166 < baseStart_1471166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471174 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1471174 : Nat := 118140960795 + 1471174 * 2 ^ 59
def prefixEnd_1471174 : Nat := 4983230072969 + 3 ^ 40 * 1471174 * 2
def baseEnd_1471174 : Nat := 503612925598488172439467

theorem tailTrace_1471174 : CollatzResearch.WordTrace tailWord_1471174 prefixEnd_1471174 503612925598488172439467 := by
  unfold tailWord_1471174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676816374131104042523643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35772082648130219573837717 1676816374131104042523643)
  ·
    refine ⟨2515224561196656063785465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676816374131104042523643 2515224561196656063785465)
    ·
      refine ⟨1886418420897492047839099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515224561196656063785465 1886418420897492047839099)
      ·
        refine ⟨2829627631346238071758649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886418420897492047839099 2829627631346238071758649)
        ·
          refine ⟨2122220723509678553818987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829627631346238071758649 2122220723509678553818987)
          ·
            refine ⟨3183331085264517830728481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122220723509678553818987 3183331085264517830728481)
            ·
              refine ⟨2387498313948388373046361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183331085264517830728481 2387498313948388373046361)
              ·
                refine ⟨1790623735461291279784771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387498313948388373046361 1790623735461291279784771)
                ·
                  refine ⟨2685935603191936919677157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790623735461291279784771 2685935603191936919677157)
                  ·
                    refine ⟨503612925598488172439467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2685935603191936919677157 503612925598488172439467)
                    ·
                      rfl

theorem cell22_1471174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1471174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471174 prefixEnd_1471174 := by exact prefixLift 1471174
  have htrace : WordTrace (prefixWord ++ tailWord_1471174) baseStart_1471174 baseEnd_1471174 := by
    simpa [prefixWord, tailWord_1471174, baseEnd_1471174] using wordTrace_append hprefix tailTrace_1471174
  have hstable : (prefixWord ++ tailWord_1471174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471174).length < 2 ^ (prefixWord ++ tailWord_1471174).sum := by decide
  have hdescent : baseEnd_1471174 < baseStart_1471174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471189 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 4]
def baseStart_1471189 : Nat := 118140960795 + 1471189 * 2 ^ 59
def prefixEnd_1471189 : Nat := 4983230072969 + 3 ^ 40 * 1471189 * 2
def baseEnd_1471189 : Nat := 167872686801677711104807

theorem tailTrace_1471189 : CollatzResearch.WordTrace tailWord_1471189 prefixEnd_1471189 167872686801677711104807 := by
  unfold tailWord_1471189
  simp only [CollatzResearch.WordTrace]
  refine ⟨53658671067140986922552621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35772447378093991281701747 53658671067140986922552621)
  ·
    refine ⟨20122001650177870095957233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53658671067140986922552621 20122001650177870095957233)
    ·
      refine ⟨15091501237633402571967925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20122001650177870095957233 15091501237633402571967925)
      ·
        refine ⟨1414828241028131491121993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15091501237633402571967925 1414828241028131491121993)
        ·
          refine ⟨1061121180771098618341495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414828241028131491121993 1061121180771098618341495)
          ·
            refine ⟨1591681771156647927512243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061121180771098618341495 1591681771156647927512243)
            ·
              refine ⟨2387522656734971891268365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591681771156647927512243 2387522656734971891268365)
              ·
                refine ⟨895320996275614459225637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2387522656734971891268365 895320996275614459225637)
                ·
                  refine ⟨167872686801677711104807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895320996275614459225637 167872686801677711104807)
                  ·
                    rfl

theorem cell22_1471189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_1471189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471189 prefixEnd_1471189 := by exact prefixLift 1471189
  have htrace : WordTrace (prefixWord ++ tailWord_1471189) baseStart_1471189 baseEnd_1471189 := by
    simpa [prefixWord, tailWord_1471189, baseEnd_1471189] using wordTrace_append hprefix tailTrace_1471189
  have hstable : (prefixWord ++ tailWord_1471189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471189).length < 2 ^ (prefixWord ++ tailWord_1471189).sum := by decide
  have hdescent : baseEnd_1471189 < baseStart_1471189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471211 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 5]
def baseStart_1471211 : Nat := 118140960795 + 1471211 * 2 ^ 59
def prefixEnd_1471211 : Nat := 4983230072969 + 3 ^ 40 * 1471211 * 2
def baseEnd_1471211 : Nat := 167875197151544136421451

theorem tailTrace_1471211 : CollatzResearch.WordTrace tailWord_1471211 prefixEnd_1471211 167875197151544136421451 := by
  unfold tailWord_1471211
  simp only [CollatzResearch.WordTrace]
  refine ⟨53659473473061284679853487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35772982315374189786568991 53659473473061284679853487)
  ·
    refine ⟨80489210209591927019780231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53659473473061284679853487 80489210209591927019780231)
    ·
      refine ⟨120733815314387890529670347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80489210209591927019780231 120733815314387890529670347)
      ·
        refine ⟨181100722971581835794505521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120733815314387890529670347 181100722971581835794505521)
        ·
          refine ⟨135825542228686376845879141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181100722971581835794505521 135825542228686376845879141)
          ·
            refine ⟨25467289167878695658602339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135825542228686376845879141 25467289167878695658602339)
            ·
              refine ⟨38200933751818043487903509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25467289167878695658602339 38200933751818043487903509)
              ·
                refine ⟨1790668769616470788495477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38200933751818043487903509 1790668769616470788495477)
                ·
                  refine ⟨167875197151544136421451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790668769616470788495477 167875197151544136421451)
                  ·
                    rfl

theorem cell22_1471211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].length) (baseStart_1471211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471211 prefixEnd_1471211 := by exact prefixLift 1471211
  have htrace : WordTrace (prefixWord ++ tailWord_1471211) baseStart_1471211 baseEnd_1471211 := by
    simpa [prefixWord, tailWord_1471211, baseEnd_1471211] using wordTrace_append hprefix tailTrace_1471211
  have hstable : (prefixWord ++ tailWord_1471211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471211).length < 2 ^ (prefixWord ++ tailWord_1471211).sum := by decide
  have hdescent : baseEnd_1471211 < baseStart_1471211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471215 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 3, 3]
def baseStart_1471215 : Nat := 118140960795 + 1471215 * 2 ^ 59
def prefixEnd_1471215 : Nat := 4983230072969 + 3 ^ 40 * 1471215 * 2
def baseEnd_1471215 : Nat := 503626960736377732164341

theorem tailTrace_1471215 : CollatzResearch.WordTrace tailWord_1471215 prefixEnd_1471215 503626960736377732164341 := by
  unfold tailWord_1471215
  simp only [CollatzResearch.WordTrace]
  refine ⟨53659619365046793362999099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35773079576697862241999399 53659619365046793362999099)
  ·
    refine ⟨80489429047570190044498649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53659619365046793362999099 80489429047570190044498649)
    ·
      refine ⟨60367071785677642533373987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80489429047570190044498649 60367071785677642533373987)
      ·
        refine ⟨90550607678516463800060981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60367071785677642533373987 90550607678516463800060981)
        ·
          refine ⟨8489119469860918481255717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90550607678516463800060981 8489119469860918481255717)
          ·
            refine ⟨1591709900598922215235447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8489119469860918481255717 1591709900598922215235447)
            ·
              refine ⟨2387564850898383322853171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591709900598922215235447 2387564850898383322853171)
              ·
                refine ⟨3581347276347574984279757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387564850898383322853171 3581347276347574984279757)
                ·
                  refine ⟨1343005228630340619104909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3581347276347574984279757 1343005228630340619104909)
                  ·
                    refine ⟨503626960736377732164341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343005228630340619104909 503626960736377732164341)
                    ·
                      rfl

theorem cell22_1471215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_1471215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471215 prefixEnd_1471215 := by exact prefixLift 1471215
  have htrace : WordTrace (prefixWord ++ tailWord_1471215) baseStart_1471215 baseEnd_1471215 := by
    simpa [prefixWord, tailWord_1471215, baseEnd_1471215] using wordTrace_append hprefix tailTrace_1471215
  have hstable : (prefixWord ++ tailWord_1471215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471215).length < 2 ^ (prefixWord ++ tailWord_1471215).sum := by decide
  have hdescent : baseEnd_1471215 < baseStart_1471215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471226 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1471226 : Nat := 118140960795 + 1471226 * 2 ^ 59
def prefixEnd_1471226 : Nat := 4983230072969 + 3 ^ 40 * 1471226 * 2
def baseEnd_1471226 : Nat := 503630726261177370139307

theorem tailTrace_1471226 : CollatzResearch.WordTrace tailWord_1471226 prefixEnd_1471226 503630726261177370139307 := by
  unfold tailWord_1471226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415005142001735560412383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35773347045337961494433021 13415005142001735560412383)
  ·
    refine ⟨20122507713002603340618575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13415005142001735560412383 20122507713002603340618575)
    ·
      refine ⟨30183761569503905010927863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20122507713002603340618575 30183761569503905010927863)
      ·
        refine ⟨45275642354255857516391795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30183761569503905010927863 45275642354255857516391795)
        ·
          refine ⟨67913463531383786274587693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45275642354255857516391795 67913463531383786274587693)
          ·
            refine ⟨25467548824268919852970385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67913463531383786274587693 25467548824268919852970385)
            ·
              refine ⟨19100661618201689889727789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25467548824268919852970385 19100661618201689889727789)
              ·
                refine ⟨7162748106825633708647921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19100661618201689889727789 7162748106825633708647921)
                ·
                  refine ⟨5372061080119225281485941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162748106825633708647921 5372061080119225281485941)
                  ·
                    refine ⟨503630726261177370139307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5372061080119225281485941 503630726261177370139307)
                    ·
                      rfl

theorem cell22_1471226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1471226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471226 prefixEnd_1471226 := by exact prefixLift 1471226
  have htrace : WordTrace (prefixWord ++ tailWord_1471226) baseStart_1471226 baseEnd_1471226 := by
    simpa [prefixWord, tailWord_1471226, baseEnd_1471226] using wordTrace_append hprefix tailTrace_1471226
  have hstable : (prefixWord ++ tailWord_1471226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471226).length < 2 ^ (prefixWord ++ tailWord_1471226).sum := by decide
  have hdescent : baseEnd_1471226 < baseStart_1471226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471228 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1471228 : Nat := 118140960795 + 1471228 * 2 ^ 59
def prefixEnd_1471228 : Nat := 4983230072969 + 3 ^ 40 * 1471228 * 2
def baseEnd_1471228 : Nat := 167877136967350010529767

theorem tailTrace_1471228 : CollatzResearch.WordTrace tailWord_1471228 prefixEnd_1471228 167877136967350010529767 := by
  unfold tailWord_1471228
  simp only [CollatzResearch.WordTrace]
  refine ⟨26830046756999848291611169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35773395675999797722148225 26830046756999848291611169)
  ·
    refine ⟨20122535067749886218708377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26830046756999848291611169 20122535067749886218708377)
    ·
      refine ⟨15091901300812414664031283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20122535067749886218708377 15091901300812414664031283)
      ·
        refine ⟨22637851951218621996046925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15091901300812414664031283 22637851951218621996046925)
        ·
          refine ⟨8489194481706983248517597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22637851951218621996046925 8489194481706983248517597)
          ·
            refine ⟨3183447930640118718194099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8489194481706983248517597 3183447930640118718194099)
            ·
              refine ⟨4775171895960178077291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183447930640118718194099 4775171895960178077291149)
              ·
                refine ⟨1790689460985066778984181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4775171895960178077291149 1790689460985066778984181)
                ·
                  refine ⟨167877136967350010529767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790689460985066778984181 167877136967350010529767)
                  ·
                    rfl

theorem cell22_1471228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1471228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471228 prefixEnd_1471228 := by exact prefixLift 1471228
  have htrace : WordTrace (prefixWord ++ tailWord_1471228) baseStart_1471228 baseEnd_1471228 := by
    simpa [prefixWord, tailWord_1471228, baseEnd_1471228] using wordTrace_append hprefix tailTrace_1471228
  have hstable : (prefixWord ++ tailWord_1471228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471228).length < 2 ^ (prefixWord ++ tailWord_1471228).sum := by decide
  have hdescent : baseEnd_1471228 < baseStart_1471228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471273 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 4]
def baseStart_1471273 : Nat := 118140960795 + 1471273 * 2 ^ 59
def prefixEnd_1471273 : Nat := 4983230072969 + 3 ^ 40 * 1471273 * 2
def baseEnd_1471273 : Nat := 167882271773894971404721

theorem tailTrace_1471273 : CollatzResearch.WordTrace tailWord_1471273 prefixEnd_1471273 167882271773894971404721 := by
  unfold tailWord_1471273
  simp only [CollatzResearch.WordTrace]
  refine ⟨53661734798836669268610473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35774489865891112845740315 53661734798836669268610473)
  ·
    refine ⟨40246301099127501951457855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53661734798836669268610473 40246301099127501951457855)
    ·
      refine ⟨60369451648691252927186783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40246301099127501951457855 60369451648691252927186783)
      ·
        refine ⟨90554177473036879390780175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60369451648691252927186783 90554177473036879390780175)
        ·
          refine ⟨135831266209555319086170263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90554177473036879390780175 135831266209555319086170263)
          ·
            refine ⟨203746899314332978629255395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135831266209555319086170263 203746899314332978629255395)
            ·
              refine ⟨305620348971499467943883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203746899314332978629255395 305620348971499467943883093)
              ·
                refine ⟨895372116127439847491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 305620348971499467943883093 895372116127439847491845)
                ·
                  refine ⟨167882271773894971404721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895372116127439847491845 167882271773894971404721)
                  ·
                    rfl

theorem cell22_1471273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_1471273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471273 prefixEnd_1471273 := by exact prefixLift 1471273
  have htrace : WordTrace (prefixWord ++ tailWord_1471273) baseStart_1471273 baseEnd_1471273 := by
    simpa [prefixWord, tailWord_1471273, baseEnd_1471273] using wordTrace_append hprefix tailTrace_1471273
  have hstable : (prefixWord ++ tailWord_1471273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471273).length < 2 ^ (prefixWord ++ tailWord_1471273).sum := by decide
  have hdescent : baseEnd_1471273 < baseStart_1471273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471277 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1471277 : Nat := 118140960795 + 1471277 * 2 ^ 59
def prefixEnd_1471277 : Nat := 4983230072969 + 3 ^ 40 * 1471277 * 2
def baseEnd_1471277 : Nat := 503648184603430237114151

theorem tailTrace_1471277 : CollatzResearch.WordTrace tailWord_1471277 prefixEnd_1471277 503648184603430237114151 := by
  unfold tailWord_1471277
  simp only [CollatzResearch.WordTrace]
  refine ⟨53661880690822177951756085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35774587127214785301170723 53661880690822177951756085)
  ·
    refine ⟨5030801314764579182977133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53661880690822177951756085 5030801314764579182977133)
    ·
      refine ⟨1886550493036717193616425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5030801314764579182977133 1886550493036717193616425)
      ·
        refine ⟨1414912869777537895212319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886550493036717193616425 1414912869777537895212319)
        ·
          refine ⟨2122369304666306842818479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414912869777537895212319 2122369304666306842818479)
          ·
            refine ⟨3183553956999460264227719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122369304666306842818479 3183553956999460264227719)
            ·
              refine ⟨4775330935499190396341579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183553956999460264227719 4775330935499190396341579)
              ·
                refine ⟨7162996403248785594512369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775330935499190396341579 7162996403248785594512369)
                ·
                  refine ⟨5372247302436589195884277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162996403248785594512369 5372247302436589195884277)
                  ·
                    refine ⟨503648184603430237114151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5372247302436589195884277 503648184603430237114151)
                    ·
                      rfl

theorem cell22_1471277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1471277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471277 prefixEnd_1471277 := by exact prefixLift 1471277
  have htrace : WordTrace (prefixWord ++ tailWord_1471277) baseStart_1471277 baseEnd_1471277 := by
    simpa [prefixWord, tailWord_1471277, baseEnd_1471277] using wordTrace_append hprefix tailTrace_1471277
  have hstable : (prefixWord ++ tailWord_1471277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471277).length < 2 ^ (prefixWord ++ tailWord_1471277).sum := by decide
  have hdescent : baseEnd_1471277 < baseStart_1471277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471288 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_1471288 : Nat := 118140960795 + 1471288 * 2 ^ 59
def prefixEnd_1471288 : Nat := 4983230072969 + 3 ^ 40 * 1471288 * 2
def baseEnd_1471288 : Nat := 503651950128229875089117

theorem tailTrace_1471288 : CollatzResearch.WordTrace tailWord_1471288 prefixEnd_1471288 503651950128229875089117 := by
  unfold tailWord_1471288
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831140946891163415203259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35774854595854884553604345 26831140946891163415203259)
  ·
    refine ⟨40246711420336745122804889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26831140946891163415203259 40246711420336745122804889)
    ·
      refine ⟨30185033565252558842103667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40246711420336745122804889 30185033565252558842103667)
      ·
        refine ⟨45277550347878838263155501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30185033565252558842103667 45277550347878838263155501)
        ·
          refine ⟨16979081380454564348683313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45277550347878838263155501 16979081380454564348683313)
          ·
            refine ⟨12734311035340923261512485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16979081380454564348683313 12734311035340923261512485)
            ·
              refine ⟨2387683319126423111533591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12734311035340923261512485 2387683319126423111533591)
              ·
                refine ⟨3581524978689634667300387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387683319126423111533591 3581524978689634667300387)
                ·
                  refine ⟨5372287468034452000950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581524978689634667300387 5372287468034452000950581)
                  ·
                    refine ⟨503651950128229875089117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5372287468034452000950581 503651950128229875089117)
                    ·
                      rfl

theorem cell22_1471288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_1471288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471288 prefixEnd_1471288 := by exact prefixLift 1471288
  have htrace : WordTrace (prefixWord ++ tailWord_1471288) baseStart_1471288 baseEnd_1471288 := by
    simpa [prefixWord, tailWord_1471288, baseEnd_1471288] using wordTrace_append hprefix tailTrace_1471288
  have hstable : (prefixWord ++ tailWord_1471288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471288).length < 2 ^ (prefixWord ++ tailWord_1471288).sum := by decide
  have hdescent : baseEnd_1471288 < baseStart_1471288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471322 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_1471322 : Nat := 118140960795 + 1471322 * 2 ^ 59
def prefixEnd_1471322 : Nat := 4983230072969 + 3 ^ 40 * 1471322 * 2
def baseEnd_1471322 : Nat := 503663589023065119739013

theorem tailTrace_1471322 : CollatzResearch.WordTrace tailWord_1471322 prefixEnd_1471322 503663589023065119739013 := by
  unfold tailWord_1471322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415880493914787659286055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35775681317106100424762813 13415880493914787659286055)
  ·
    refine ⟨20123820740872181488929083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13415880493914787659286055 20123820740872181488929083)
    ·
      refine ⟨30185731111308272233393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20123820740872181488929083 30185731111308272233393625)
      ·
        refine ⟨22639298333481204175045219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30185731111308272233393625 22639298333481204175045219)
        ·
          refine ⟨33958947500221806262567829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22639298333481204175045219 33958947500221806262567829)
          ·
            refine ⟨1591825664072897168557867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33958947500221806262567829 1591825664072897168557867)
            ·
              refine ⟨2387738496109345752836801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591825664072897168557867 2387738496109345752836801)
              ·
                refine ⟨1790803872082009314627601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387738496109345752836801 1790803872082009314627601)
                ·
                  refine ⟨1343102904061506985970701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790803872082009314627601 1343102904061506985970701)
                  ·
                    refine ⟨503663589023065119739013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343102904061506985970701 503663589023065119739013)
                    ·
                      rfl

theorem cell22_1471322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_1471322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471322 prefixEnd_1471322 := by exact prefixLift 1471322
  have htrace : WordTrace (prefixWord ++ tailWord_1471322) baseStart_1471322 baseEnd_1471322 := by
    simpa [prefixWord, tailWord_1471322, baseEnd_1471322] using wordTrace_append hprefix tailTrace_1471322
  have hstable : (prefixWord ++ tailWord_1471322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471322).length < 2 ^ (prefixWord ++ tailWord_1471322).sum := by decide
  have hdescent : baseEnd_1471322 < baseStart_1471322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471380 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1471380 : Nat := 118140960795 + 1471380 * 2 ^ 59
def prefixEnd_1471380 : Nat := 4983230072969 + 3 ^ 40 * 1471380 * 2
def baseEnd_1471380 : Nat := 167894481202790767262945

theorem tailTrace_1471380 : CollatzResearch.WordTrace tailWord_1471380 prefixEnd_1471380 167894481202790767262945 := by
  unfold tailWord_1471380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832818704724513271377797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35777091606299351028503729 26832818704724513271377797)
  ·
    refine ⟨5031153507135846238383337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26832818704724513271377797 5031153507135846238383337)
    ·
      refine ⟨3773365130351884678787503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5031153507135846238383337 3773365130351884678787503)
      ·
        refine ⟨5660047695527827018181255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773365130351884678787503 5660047695527827018181255)
        ·
          refine ⟨8490071543291740527271883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660047695527827018181255 8490071543291740527271883)
          ·
            refine ⟨12735107314937610790907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490071543291740527271883 12735107314937610790907825)
            ·
              refine ⟨9551330486203208093180869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12735107314937610790907825 9551330486203208093180869)
              ·
                refine ⟨1790874466163101517471413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9551330486203208093180869 1790874466163101517471413)
                ·
                  refine ⟨167894481202790767262945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1790874466163101517471413 167894481202790767262945)
                  ·
                    rfl

theorem cell22_1471380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1471380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471380 prefixEnd_1471380 := by exact prefixLift 1471380
  have htrace : WordTrace (prefixWord ++ tailWord_1471380) baseStart_1471380 baseEnd_1471380 := by
    simpa [prefixWord, tailWord_1471380, baseEnd_1471380] using wordTrace_append hprefix tailTrace_1471380
  have hstable : (prefixWord ++ tailWord_1471380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471380).length < 2 ^ (prefixWord ++ tailWord_1471380).sum := by decide
  have hdescent : baseEnd_1471380 < baseStart_1471380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471485 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1471485 : Nat := 118140960795 + 1471485 * 2 ^ 59
def prefixEnd_1471485 : Nat := 4983230072969 + 3 ^ 40 * 1471485 * 2
def baseEnd_1471485 : Nat := 503719387254187027913513

theorem tailTrace_1471485 : CollatzResearch.WordTrace tailWord_1471485 prefixEnd_1471485 503719387254187027913513 := by
  unfold tailWord_1471485
  simp only [CollatzResearch.WordTrace]
  refine ⟨53669467074068629475327909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35779644716045752983551939 53669467074068629475327909)
  ·
    refine ⟨10063025076387868026623983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53669467074068629475327909 10063025076387868026623983)
    ·
      refine ⟨15094537614581802039935975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10063025076387868026623983 15094537614581802039935975)
      ·
        refine ⟨22641806421872703059903963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094537614581802039935975 22641806421872703059903963)
        ·
          refine ⟨33962709632809054589855945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22641806421872703059903963 33962709632809054589855945)
          ·
            refine ⟨25472032224606790942391959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33962709632809054589855945 25472032224606790942391959)
            ·
              refine ⟨38208048336910186413587939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25472032224606790942391959 38208048336910186413587939)
              ·
                refine ⟨57312072505365279620381909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38208048336910186413587939 57312072505365279620381909)
                ·
                  refine ⟨1343251699344498741102701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57312072505365279620381909 1343251699344498741102701)
                  ·
                    refine ⟨503719387254187027913513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343251699344498741102701 503719387254187027913513)
                    ·
                      rfl

theorem cell22_1471485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1471485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471485 prefixEnd_1471485 := by exact prefixLift 1471485
  have htrace : WordTrace (prefixWord ++ tailWord_1471485) baseStart_1471485 baseEnd_1471485 := by
    simpa [prefixWord, tailWord_1471485, baseEnd_1471485] using wordTrace_append hprefix tailTrace_1471485
  have hstable : (prefixWord ++ tailWord_1471485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471485).length < 2 ^ (prefixWord ++ tailWord_1471485).sum := by decide
  have hdescent : baseEnd_1471485 < baseStart_1471485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471502 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1471502 : Nat := 118140960795 + 1471502 * 2 ^ 59
def prefixEnd_1471502 : Nat := 4983230072969 + 3 ^ 40 * 1471502 * 2
def baseEnd_1471502 : Nat := 503725206701604650238461

theorem tailTrace_1471502 : CollatzResearch.WordTrace tailWord_1471502 prefixEnd_1471502 503725206701604650238461 := by
  unfold tailWord_1471502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708760889375880172337095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35780058076671360919131173 6708760889375880172337095)
  ·
    refine ⟨10063141334063820258505643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708760889375880172337095 10063141334063820258505643)
    ·
      refine ⟨15094712001095730387758465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10063141334063820258505643 15094712001095730387758465)
      ·
        refine ⟨11321034000821797790818849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15094712001095730387758465 11321034000821797790818849)
        ·
          refine ⟨8490775500616348343114137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11321034000821797790818849 8490775500616348343114137)
          ·
            refine ⟨6368081625462261257335603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490775500616348343114137 6368081625462261257335603)
            ·
              refine ⟨9552122438193391886003405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368081625462261257335603 9552122438193391886003405)
              ·
                refine ⟨3582045914322521957251277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9552122438193391886003405 3582045914322521957251277)
                ·
                  refine ⟨1343267217870945733969229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3582045914322521957251277 1343267217870945733969229)
                  ·
                    refine ⟨503725206701604650238461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343267217870945733969229 503725206701604650238461)
                    ·
                      rfl

theorem cell22_1471502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1471502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471502 prefixEnd_1471502 := by exact prefixLift 1471502
  have htrace : WordTrace (prefixWord ++ tailWord_1471502) baseStart_1471502 baseEnd_1471502 := by
    simpa [prefixWord, tailWord_1471502, baseEnd_1471502] using wordTrace_append hprefix tailTrace_1471502
  have hstable : (prefixWord ++ tailWord_1471502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471502).length < 2 ^ (prefixWord ++ tailWord_1471502).sum := by decide
  have hdescent : baseEnd_1471502 < baseStart_1471502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471553 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1471553 : Nat := 118140960795 + 1471553 * 2 ^ 59
def prefixEnd_1471553 : Nat := 4983230072969 + 3 ^ 40 * 1471553 * 2
def baseEnd_1471553 : Nat := 503742665043857517213305

theorem tailTrace_1471553 : CollatzResearch.WordTrace tailWord_1471553 prefixEnd_1471553 503742665043857517213305 := by
  unfold tailWord_1471553
  simp only [CollatzResearch.WordTrace]
  refine ⟨53671947237822277088803313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35781298158548184725868875 53671947237822277088803313)
  ·
    refine ⟨40253960428366707816602485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53671947237822277088803313 40253960428366707816602485)
    ·
      refine ⟨3773808790159378857806483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40253960428366707816602485 3773808790159378857806483)
      ·
        refine ⟨5660713185239068286709725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773808790159378857806483 5660713185239068286709725)
        ·
          refine ⟨2122767444464650607516147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5660713185239068286709725 2122767444464650607516147)
          ·
            refine ⟨3184151166696975911274221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122767444464650607516147 3184151166696975911274221)
            ·
              refine ⟨1194056687511365966727833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184151166696975911274221 1194056687511365966727833)
              ·
                refine ⟨895542515633524475045875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194056687511365966727833 895542515633524475045875)
                ·
                  refine ⟨1343313773450286712568813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895542515633524475045875 1343313773450286712568813)
                  ·
                    refine ⟨503742665043857517213305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343313773450286712568813 503742665043857517213305)
                    ·
                      rfl

theorem cell22_1471553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1471553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471553 prefixEnd_1471553 := by exact prefixLift 1471553
  have htrace : WordTrace (prefixWord ++ tailWord_1471553) baseStart_1471553 baseEnd_1471553 := by
    simpa [prefixWord, tailWord_1471553, baseEnd_1471553] using wordTrace_append hprefix tailTrace_1471553
  have hstable : (prefixWord ++ tailWord_1471553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471553).length < 2 ^ (prefixWord ++ tailWord_1471553).sum := by decide
  have hdescent : baseEnd_1471553 < baseStart_1471553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471575 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1471575 : Nat := 118140960795 + 1471575 * 2 ^ 59
def prefixEnd_1471575 : Nat := 4983230072969 + 3 ^ 40 * 1471575 * 2
def baseEnd_1471575 : Nat := 503750196093456793163237

theorem tailTrace_1471575 : CollatzResearch.WordTrace tailWord_1471575 prefixEnd_1471575 503750196093456793163237 := by
  unfold tailWord_1471575
  simp only [CollatzResearch.WordTrace]
  refine ⟨53672749643742574846104179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35781833095828383230736119 53672749643742574846104179)
  ·
    refine ⟨80509124465613862269156269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53672749643742574846104179 80509124465613862269156269)
    ·
      refine ⟨30190921674605198350933601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80509124465613862269156269 30190921674605198350933601)
      ·
        refine ⟨22643191255953898763200201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30190921674605198350933601 22643191255953898763200201)
        ·
          refine ⟨16982393441965424072400151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22643191255953898763200201 16982393441965424072400151)
          ·
            refine ⟨25473590162948136108600227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16982393441965424072400151 25473590162948136108600227)
            ·
              refine ⟨38210385244422204162900341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25473590162948136108600227 38210385244422204162900341)
              ·
                refine ⟨3582223616664581640271907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38210385244422204162900341 3582223616664581640271907)
                ·
                  refine ⟨5373335424996872460407861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582223616664581640271907 5373335424996872460407861)
                  ·
                    refine ⟨503750196093456793163237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5373335424996872460407861 503750196093456793163237)
                    ·
                      rfl

theorem cell22_1471575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1471575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471575 prefixEnd_1471575 := by exact prefixLift 1471575
  have htrace : WordTrace (prefixWord ++ tailWord_1471575) baseStart_1471575 baseEnd_1471575 := by
    simpa [prefixWord, tailWord_1471575, baseEnd_1471575] using wordTrace_append hprefix tailTrace_1471575
  have hstable : (prefixWord ++ tailWord_1471575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471575).length < 2 ^ (prefixWord ++ tailWord_1471575).sum := by decide
  have hdescent : baseEnd_1471575 < baseStart_1471575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471667 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 5]
def baseStart_1471667 : Nat := 118140960795 + 1471667 * 2 ^ 59
def prefixEnd_1471667 : Nat := 4983230072969 + 3 ^ 40 * 1471667 * 2
def baseEnd_1471667 : Nat := 167927229857866406620985

theorem tailTrace_1471667 : CollatzResearch.WordTrace tailWord_1471667 prefixEnd_1471667 167927229857866406620985 := by
  unfold tailWord_1471667
  simp only [CollatzResearch.WordTrace]
  refine ⟨53676105159409274558453255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35784070106272849705635503 53676105159409274558453255)
  ·
    refine ⟨80514157739113911837679883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53676105159409274558453255 80514157739113911837679883)
    ·
      refine ⟨120771236608670867756519825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80514157739113911837679883 120771236608670867756519825)
      ·
        refine ⟨90578427456503150817389869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120771236608670867756519825 90578427456503150817389869)
        ·
          refine ⟨33966910296188681556521201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90578427456503150817389869 33966910296188681556521201)
          ·
            refine ⟨25475182722141511167390901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33966910296188681556521201 25475182722141511167390901)
            ·
              refine ⟨2388298380200766671942897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25475182722141511167390901 2388298380200766671942897)
              ·
                refine ⟨1791223785150575003957173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388298380200766671942897 1791223785150575003957173)
                ·
                  refine ⟨167927229857866406620985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791223785150575003957173 167927229857866406620985)
                  ·
                    rfl

theorem cell22_1471667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].length) (baseStart_1471667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471667 prefixEnd_1471667 := by exact prefixLift 1471667
  have htrace : WordTrace (prefixWord ++ tailWord_1471667) baseStart_1471667 baseEnd_1471667 := by
    simpa [prefixWord, tailWord_1471667, baseEnd_1471667] using wordTrace_append hprefix tailTrace_1471667
  have hstable : (prefixWord ++ tailWord_1471667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471667).length < 2 ^ (prefixWord ++ tailWord_1471667).sum := by decide
  have hdescent : baseEnd_1471667 < baseStart_1471667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471695 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 8]
def baseStart_1471695 : Nat := 118140960795 + 1471695 * 2 ^ 59
def prefixEnd_1471695 : Nat := 4983230072969 + 3 ^ 40 * 1471695 * 2
def baseEnd_1471695 : Nat := 167930424848605493387623

theorem tailTrace_1471695 : CollatzResearch.WordTrace tailWord_1471695 prefixEnd_1471695 167930424848605493387623 := by
  unfold tailWord_1471695
  simp only [CollatzResearch.WordTrace]
  refine ⟨53677126403307835340472539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35784750935538556893648359 53677126403307835340472539)
  ·
    refine ⟨80515689604961753010708809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53677126403307835340472539 80515689604961753010708809)
    ·
      refine ⟨60386767203721314758031607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80515689604961753010708809 60386767203721314758031607)
      ·
        refine ⟨90580150805581972137047411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60386767203721314758031607 90580150805581972137047411)
        ·
          refine ⟨135870226208372958205571117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90580150805581972137047411 135870226208372958205571117)
          ·
            refine ⟨50951334828139859327089169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135870226208372958205571117 50951334828139859327089169)
            ·
              refine ⟨38213501121104894495316877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50951334828139859327089169 38213501121104894495316877)
              ·
                refine ⟨14330062920414335435743829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38213501121104894495316877 14330062920414335435743829)
                ·
                  refine ⟨167930424848605493387623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14330062920414335435743829 167930424848605493387623)
                  ·
                    rfl

theorem cell22_1471695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_1471695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471695 prefixEnd_1471695 := by exact prefixLift 1471695
  have htrace : WordTrace (prefixWord ++ tailWord_1471695) baseStart_1471695 baseEnd_1471695 := by
    simpa [prefixWord, tailWord_1471695, baseEnd_1471695] using wordTrace_append hprefix tailTrace_1471695
  have hstable : (prefixWord ++ tailWord_1471695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471695).length < 2 ^ (prefixWord ++ tailWord_1471695).sum := by decide
  have hdescent : baseEnd_1471695 < baseStart_1471695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471774 : List Nat := [4, 3, 2, 1, 12]
def baseStart_1471774 : Nat := 118140960795 + 1471774 * 2 ^ 59
def prefixEnd_1471774 : Nat := 4983230072969 + 3 ^ 40 * 1471774 * 2
def baseEnd_1471774 : Nat := 2073326410947681512089

theorem tailTrace_1471774 : CollatzResearch.WordTrace tailWord_1471774 prefixEnd_1471774 2073326410947681512089 := by
  unfold tailWord_1471774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710000971252703979074797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35786671846681087888398917 6710000971252703979074797)
  ·
    refine ⟨2516250364219763992153049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6710000971252703979074797 2516250364219763992153049)
    ·
      refine ⟨1887187773164822994114787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2516250364219763992153049 1887187773164822994114787)
      ·
        refine ⟨2830781659747234491172181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887187773164822994114787 2830781659747234491172181)
        ·
          refine ⟨2073326410947681512089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2830781659747234491172181 2073326410947681512089)
          ·
            rfl

theorem cell22_1471774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 12].length) (baseStart_1471774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471774 prefixEnd_1471774 := by exact prefixLift 1471774
  have htrace : WordTrace (prefixWord ++ tailWord_1471774) baseStart_1471774 baseEnd_1471774 := by
    simpa [prefixWord, tailWord_1471774, baseEnd_1471774] using wordTrace_append hprefix tailTrace_1471774
  have hstable : (prefixWord ++ tailWord_1471774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471774).length < 2 ^ (prefixWord ++ tailWord_1471774).sum := by decide
  have hdescent : baseEnd_1471774 < baseStart_1471774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471778 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1471778 : Nat := 118140960795 + 1471778 * 2 ^ 59
def prefixEnd_1471778 : Nat := 4983230072969 + 3 ^ 40 * 1471778 * 2
def baseEnd_1471778 : Nat := 503819687142031930337615

theorem tailTrace_1471778 : CollatzResearch.WordTrace tailWord_1471778 prefixEnd_1471778 503819687142031930337615 := by
  unfold tailWord_1471778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420038415501785128935997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35786769108004760343829325 13420038415501785128935997)
  ·
    refine ⟨5032514405813169423350999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13420038415501785128935997 5032514405813169423350999)
    ·
      refine ⟨7548771608719754135026499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5032514405813169423350999 7548771608719754135026499)
      ·
        refine ⟨11323157413079631202539749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548771608719754135026499 11323157413079631202539749)
        ·
          refine ⟨2123092014952430850476203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11323157413079631202539749 2123092014952430850476203)
          ·
            refine ⟨3184638022428646275714305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123092014952430850476203 3184638022428646275714305)
            ·
              refine ⟨2388478516821484706785729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184638022428646275714305 2388478516821484706785729)
              ·
                refine ⟨1791358887616113530089297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388478516821484706785729 1791358887616113530089297)
                ·
                  refine ⟨1343519165712085147566973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791358887616113530089297 1343519165712085147566973)
                  ·
                    refine ⟨503819687142031930337615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343519165712085147566973 503819687142031930337615)
                    ·
                      rfl

theorem cell22_1471778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1471778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471778 prefixEnd_1471778 := by exact prefixLift 1471778
  have htrace : WordTrace (prefixWord ++ tailWord_1471778) baseStart_1471778 baseEnd_1471778 := by
    simpa [prefixWord, tailWord_1471778, baseEnd_1471778] using wordTrace_append hprefix tailTrace_1471778
  have hstable : (prefixWord ++ tailWord_1471778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471778).length < 2 ^ (prefixWord ++ tailWord_1471778).sum := by decide
  have hdescent : baseEnd_1471778 < baseStart_1471778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471806 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1471806 : Nat := 118140960795 + 1471806 * 2 ^ 59
def prefixEnd_1471806 : Nat := 4983230072969 + 3 ^ 40 * 1471806 * 2
def baseEnd_1471806 : Nat := 503829272114249190637529

theorem tailTrace_1471806 : CollatzResearch.WordTrace tailWord_1471806 prefixEnd_1471806 503829272114249190637529 := by
  unfold tailWord_1471806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710146863238212662220409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35787449937270467531842181 6710146863238212662220409)
  ·
    refine ⟨5032610147428659496665307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6710146863238212662220409 5032610147428659496665307)
    ·
      refine ⟨7548915221142989244997961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5032610147428659496665307 7548915221142989244997961)
      ·
        refine ⟨5661686415857241933748471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7548915221142989244997961 5661686415857241933748471)
        ·
          refine ⟨8492529623785862900622707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661686415857241933748471 8492529623785862900622707)
          ·
            refine ⟨12738794435678794350934061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492529623785862900622707 12738794435678794350934061)
            ·
              refine ⟨4777047913379547881600273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12738794435678794350934061 4777047913379547881600273)
              ·
                refine ⟨3582785935034660911200205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777047913379547881600273 3582785935034660911200205)
                ·
                  refine ⟨1343544725637997841700077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3582785935034660911200205 1343544725637997841700077)
                  ·
                    refine ⟨503829272114249190637529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343544725637997841700077 503829272114249190637529)
                    ·
                      rfl

theorem cell22_1471806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1471806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471806 prefixEnd_1471806 := by exact prefixLift 1471806
  have htrace : WordTrace (prefixWord ++ tailWord_1471806) baseStart_1471806 baseEnd_1471806 := by
    simpa [prefixWord, tailWord_1471806, baseEnd_1471806] using wordTrace_append hprefix tailTrace_1471806
  have hstable : (prefixWord ++ tailWord_1471806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471806).length < 2 ^ (prefixWord ++ tailWord_1471806).sum := by decide
  have hdescent : baseEnd_1471806 < baseStart_1471806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471898 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_1471898 : Nat := 118140960795 + 1471898 * 2 ^ 59
def prefixEnd_1471898 : Nat := 4983230072969 + 3 ^ 40 * 1471898 * 2
def baseEnd_1471898 : Nat := 167953588531463872445749

theorem tailTrace_1471898 : CollatzResearch.WordTrace tailWord_1471898 prefixEnd_1471898 167953588531463872445749 := by
  unfold tailWord_1471898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421132605393100252528087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35789686947714934006741565 13421132605393100252528087)
  ·
    refine ⟨20131698908089650378792131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13421132605393100252528087 20131698908089650378792131)
    ·
      refine ⟨30197548362134475568188197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20131698908089650378792131 30197548362134475568188197)
      ·
        refine ⟨5662040317900214169035287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30197548362134475568188197 5662040317900214169035287)
        ·
          refine ⟨8493060476850321253552931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662040317900214169035287 8493060476850321253552931)
          ·
            refine ⟨12739590715275481880329397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493060476850321253552931 12739590715275481880329397)
            ·
              refine ⟨1194336629557076426280881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12739590715275481880329397 1194336629557076426280881)
              ·
                refine ⟨895752472167807319710661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194336629557076426280881 895752472167807319710661)
                ·
                  refine ⟨167953588531463872445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895752472167807319710661 167953588531463872445749)
                  ·
                    rfl

theorem cell22_1471898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_1471898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471898 prefixEnd_1471898 := by exact prefixLift 1471898
  have htrace : WordTrace (prefixWord ++ tailWord_1471898) baseStart_1471898 baseEnd_1471898 := by
    simpa [prefixWord, tailWord_1471898, baseEnd_1471898] using wordTrace_append hprefix tailTrace_1471898
  have hstable : (prefixWord ++ tailWord_1471898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471898).length < 2 ^ (prefixWord ++ tailWord_1471898).sum := by decide
  have hdescent : baseEnd_1471898 < baseStart_1471898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471969 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1471969 : Nat := 118140960795 + 1471969 * 2 ^ 59
def prefixEnd_1471969 : Nat := 4983230072969 + 3 ^ 40 * 1471969 * 2
def baseEnd_1471969 : Nat := 503885070345371098812029

theorem tailTrace_1471969 : CollatzResearch.WordTrace tailWord_1471969 prefixEnd_1471969 503885070345371098812029 := by
  unfold tailWord_1471969
  simp only [CollatzResearch.WordTrace]
  refine ⟨53687120004315180135946961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35791413336210120090631307 53687120004315180135946961)
  ·
    refine ⟨40265340003236385101960221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53687120004315180135946961 40265340003236385101960221)
    ·
      refine ⟨15099502501213644413235083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40265340003236385101960221 15099502501213644413235083)
      ·
        refine ⟨22649253751820466619852625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15099502501213644413235083 22649253751820466619852625)
        ·
          refine ⟨16986940313865349964889469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22649253751820466619852625 16986940313865349964889469)
          ·
            refine ⟨6370102617699506236833551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16986940313865349964889469 6370102617699506236833551)
            ·
              refine ⟨9555153926549259355250327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370102617699506236833551 9555153926549259355250327)
              ·
                refine ⟨14332730889823889032875491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9555153926549259355250327 14332730889823889032875491)
                ·
                  refine ⟨21499096334735833549313237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14332730889823889032875491 21499096334735833549313237)
                  ·
                    refine ⟨503885070345371098812029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21499096334735833549313237 503885070345371098812029)
                    ·
                      rfl

theorem cell22_1471969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1471969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471969 prefixEnd_1471969 := by exact prefixLift 1471969
  have htrace : WordTrace (prefixWord ++ tailWord_1471969) baseStart_1471969 baseEnd_1471969 := by
    simpa [prefixWord, tailWord_1471969, baseEnd_1471969] using wordTrace_append hprefix tailTrace_1471969
  have hstable : (prefixWord ++ tailWord_1471969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471969).length < 2 ^ (prefixWord ++ tailWord_1471969).sum := by decide
  have hdescent : baseEnd_1471969 < baseStart_1471969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471971 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 5]
def baseStart_1471971 : Nat := 118140960795 + 1471971 * 2 ^ 59
def prefixEnd_1471971 : Nat := 4983230072969 + 3 ^ 40 * 1471971 * 2
def baseEnd_1471971 : Nat := 167961918328747920087341

theorem tailTrace_1471971 : CollatzResearch.WordTrace tailWord_1471971 prefixEnd_1471971 167961918328747920087341 := by
  unfold tailWord_1471971
  simp only [CollatzResearch.WordTrace]
  refine ⟨53687192950307934477519767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35791461966871956318346511 53687192950307934477519767)
  ·
    refine ⟨80530789425461901716279651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53687192950307934477519767 80530789425461901716279651)
    ·
      refine ⟨120796184138192852574419477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80530789425461901716279651 120796184138192852574419477)
      ·
        refine ⟨5662321131477789964425913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120796184138192852574419477 5662321131477789964425913)
        ·
          refine ⟨4246740848608342473319435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662321131477789964425913 4246740848608342473319435)
          ·
            refine ⟨6370111272912513709979153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246740848608342473319435 6370111272912513709979153)
            ·
              refine ⟨4777583454684385282484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370111272912513709979153 4777583454684385282484365)
              ·
                refine ⟨1791593795506644480931637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4777583454684385282484365 1791593795506644480931637)
                ·
                  refine ⟨167961918328747920087341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791593795506644480931637 167961918328747920087341)
                  ·
                    rfl

theorem cell22_1471971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].length) (baseStart_1471971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1471971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1471971 prefixEnd_1471971 := by exact prefixLift 1471971
  have htrace : WordTrace (prefixWord ++ tailWord_1471971) baseStart_1471971 baseEnd_1471971 := by
    simpa [prefixWord, tailWord_1471971, baseEnd_1471971] using wordTrace_append hprefix tailTrace_1471971
  have hstable : (prefixWord ++ tailWord_1471971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471971).length < 2 ^ (prefixWord ++ tailWord_1471971).sum := by decide
  have hdescent : baseEnd_1471971 < baseStart_1471971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472031 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_1472031 : Nat := 118140960795 + 1472031 * 2 ^ 59
def prefixEnd_1472031 : Nat := 4983230072969 + 3 ^ 40 * 1472031 * 2
def baseEnd_1472031 : Nat := 503906294212423603761839

theorem tailTrace_1472031 : CollatzResearch.WordTrace tailWord_1472031 prefixEnd_1472031 503906294212423603761839 := by
  unfold tailWord_1472031
  simp only [CollatzResearch.WordTrace]
  refine ⟨53689381330090564724703947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35792920886727043149802631 53689381330090564724703947)
  ·
    refine ⟨80534071995135847087055921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53689381330090564724703947 80534071995135847087055921)
    ·
      refine ⟨60400553996351885315291941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80534071995135847087055921 60400553996351885315291941)
      ·
        refine ⟨11325103874315978496617239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60400553996351885315291941 11325103874315978496617239)
        ·
          refine ⟨16987655811473967744925859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325103874315978496617239 16987655811473967744925859)
          ·
            refine ⟨25481483717210951617388789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16987655811473967744925859 25481483717210951617388789)
            ·
              refine ⟨2388889098488526714130199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25481483717210951617388789 2388889098488526714130199)
              ·
                refine ⟨3583333647732790071195299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388889098488526714130199 3583333647732790071195299)
                ·
                  refine ⟨5375000471599185106792949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583333647732790071195299 5375000471599185106792949)
                  ·
                    refine ⟨503906294212423603761839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5375000471599185106792949 503906294212423603761839)
                    ·
                      rfl

theorem cell22_1472031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_1472031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472031 prefixEnd_1472031 := by exact prefixLift 1472031
  have htrace : WordTrace (prefixWord ++ tailWord_1472031) baseStart_1472031 baseEnd_1472031 := by
    simpa [prefixWord, tailWord_1472031, baseEnd_1472031] using wordTrace_append hprefix tailTrace_1472031
  have hstable : (prefixWord ++ tailWord_1472031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472031).length < 2 ^ (prefixWord ++ tailWord_1472031).sum := by decide
  have hdescent : baseEnd_1472031 < baseStart_1472031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472082 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1472082 : Nat := 118140960795 + 1472082 * 2 ^ 59
def prefixEnd_1472082 : Nat := 4983230072969 + 3 ^ 40 * 1472082 * 2
def baseEnd_1472082 : Nat := 503923752554676470736683

theorem tailTrace_1472082 : CollatzResearch.WordTrace tailWord_1472082 prefixEnd_1472082 503923752554676470736683 := by
  unfold tailWord_1472082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422810363226450108702625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35794160968603866956540333 13422810363226450108702625)
  ·
    refine ⟨10067107772419837581526969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13422810363226450108702625 10067107772419837581526969)
    ·
      refine ⟨7550330829314878186145227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10067107772419837581526969 7550330829314878186145227)
      ·
        refine ⟨11325496243972317279217841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550330829314878186145227 11325496243972317279217841)
        ·
          refine ⟨8494122182979237959413381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11325496243972317279217841 8494122182979237959413381)
          ·
            refine ⟨1592647909308607117390009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8494122182979237959413381 1592647909308607117390009)
            ·
              refine ⟨1194485931981455338042507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592647909308607117390009 1194485931981455338042507)
              ·
                refine ⟨1791728897972183007063761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194485931981455338042507 1791728897972183007063761)
                ·
                  refine ⟨1343796673479137255297821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791728897972183007063761 1343796673479137255297821)
                  ·
                    refine ⟨503923752554676470736683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343796673479137255297821 503923752554676470736683)
                    ·
                      rfl

theorem cell22_1472082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1472082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472082 prefixEnd_1472082 := by exact prefixLift 1472082
  have htrace : WordTrace (prefixWord ++ tailWord_1472082) baseStart_1472082 baseEnd_1472082 := by
    simpa [prefixWord, tailWord_1472082, baseEnd_1472082] using wordTrace_append hprefix tailTrace_1472082
  have hstable : (prefixWord ++ tailWord_1472082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472082).length < 2 ^ (prefixWord ++ tailWord_1472082).sum := by decide
  have hdescent : baseEnd_1472082 < baseStart_1472082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472086 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1472086 : Nat := 118140960795 + 1472086 * 2 ^ 59
def prefixEnd_1472086 : Nat := 4983230072969 + 3 ^ 40 * 1472086 * 2
def baseEnd_1472086 : Nat := 503925121836421793636671

theorem tailTrace_1472086 : CollatzResearch.WordTrace tailWord_1472086 prefixEnd_1472086 503925121836421793636671 := by
  unfold tailWord_1472086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355711709055706819872257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35794258229927539411970741 3355711709055706819872257)
  ·
    refine ⟨2516783781791780114904193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3355711709055706819872257 2516783781791780114904193)
    ·
      refine ⟨1887587836343835086178145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2516783781791780114904193 1887587836343835086178145)
      ·
        refine ⟨1415690877257876314633609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1887587836343835086178145 1415690877257876314633609)
        ·
          refine ⟨1061768157943407235975207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415690877257876314633609 1061768157943407235975207)
          ·
            refine ⟨1592652236915110853962811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061768157943407235975207 1592652236915110853962811)
            ·
              refine ⟨2388978355372666280944217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592652236915110853962811 2388978355372666280944217)
              ·
                refine ⟨1791733766529499710708163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388978355372666280944217 1791733766529499710708163)
                ·
                  refine ⟨2687600649794249566062245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791733766529499710708163 2687600649794249566062245)
                  ·
                    refine ⟨503925121836421793636671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2687600649794249566062245 503925121836421793636671)
                    ·
                      rfl

theorem cell22_1472086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1472086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472086 prefixEnd_1472086 := by exact prefixLift 1472086
  have htrace : WordTrace (prefixWord ++ tailWord_1472086) baseStart_1472086 baseEnd_1472086 := by
    simpa [prefixWord, tailWord_1472086, baseEnd_1472086] using wordTrace_append hprefix tailTrace_1472086
  have hstable : (prefixWord ++ tailWord_1472086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472086).length < 2 ^ (prefixWord ++ tailWord_1472086).sum := by decide
  have hdescent : baseEnd_1472086 < baseStart_1472086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472121 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_1472121 : Nat := 118140960795 + 1472121 * 2 ^ 59
def prefixEnd_1472121 : Nat := 4983230072969 + 3 ^ 40 * 1472121 * 2
def baseEnd_1472121 : Nat := 503937103051693369011563

theorem tailTrace_1472121 : CollatzResearch.WordTrace tailWord_1472121 prefixEnd_1472121 503937103051693369011563 := by
  unfold tailWord_1472121
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692663899764510095480217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35795109266509673396986811 53692663899764510095480217)
  ·
    refine ⟨40269497924823382571610163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53692663899764510095480217 40269497924823382571610163)
    ·
      refine ⟨60404246887235073857415245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40269497924823382571610163 60404246887235073857415245)
      ·
        refine ⟨22651592582713152696530717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60404246887235073857415245 22651592582713152696530717)
        ·
          refine ⟨8494347218517432261199019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22651592582713152696530717 8494347218517432261199019)
          ·
            refine ⟨12741520827776148391798529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8494347218517432261199019 12741520827776148391798529)
            ·
              refine ⟨9556140620832111293848897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12741520827776148391798529 9556140620832111293848897)
              ·
                refine ⟨7167105465624083470386673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9556140620832111293848897 7167105465624083470386673)
                ·
                  refine ⟨5375329099218062602790005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167105465624083470386673 5375329099218062602790005)
                  ·
                    refine ⟨503937103051693369011563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5375329099218062602790005 503937103051693369011563)
                    ·
                      rfl

theorem cell22_1472121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_1472121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472121 prefixEnd_1472121 := by exact prefixLift 1472121
  have htrace : WordTrace (prefixWord ++ tailWord_1472121) baseStart_1472121 baseEnd_1472121 := by
    simpa [prefixWord, tailWord_1472121, baseEnd_1472121] using wordTrace_append hprefix tailTrace_1472121
  have hstable : (prefixWord ++ tailWord_1472121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472121).length < 2 ^ (prefixWord ++ tailWord_1472121).sum := by decide
  have hdescent : baseEnd_1472121 < baseStart_1472121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472138 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1472138 : Nat := 118140960795 + 1472138 * 2 ^ 59
def prefixEnd_1472138 : Nat := 4983230072969 + 3 ^ 40 * 1472138 * 2
def baseEnd_1472138 : Nat := 503942922499110991336511

theorem tailTrace_1472138 : CollatzResearch.WordTrace tailWord_1472138 prefixEnd_1472138 503942922499110991336511 := by
  unfold tailWord_1472138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13423320985175730499712267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35795522627135281332566045 13423320985175730499712267)
  ·
    refine ⟨20134981477763595749568401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13423320985175730499712267 20134981477763595749568401)
    ·
      refine ⟨15101236108322696812176301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20134981477763595749568401 15101236108322696812176301)
      ·
        refine ⟨5662963540621011304566113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15101236108322696812176301 5662963540621011304566113)
        ·
          refine ⟨4247222655465758478424585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662963540621011304566113 4247222655465758478424585)
          ·
            refine ⟨3185416991599318858818439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247222655465758478424585 3185416991599318858818439)
            ·
              refine ⟨4778125487398978288227659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185416991599318858818439 4778125487398978288227659)
              ·
                refine ⟨7167188231098467432341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4778125487398978288227659 7167188231098467432341489)
                ·
                  refine ⟨5375391173323850574256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7167188231098467432341489 5375391173323850574256117)
                  ·
                    refine ⟨503942922499110991336511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5375391173323850574256117 503942922499110991336511)
                    ·
                      rfl

theorem cell22_1472138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1472138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472138 prefixEnd_1472138 := by exact prefixLift 1472138
  have htrace : WordTrace (prefixWord ++ tailWord_1472138) baseStart_1472138 baseEnd_1472138 := by
    simpa [prefixWord, tailWord_1472138, baseEnd_1472138] using wordTrace_append hprefix tailTrace_1472138
  have hstable : (prefixWord ++ tailWord_1472138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472138).length < 2 ^ (prefixWord ++ tailWord_1472138).sum := by decide
  have hdescent : baseEnd_1472138 < baseStart_1472138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472151 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 8]
def baseStart_1472151 : Nat := 118140960795 + 1472151 * 2 ^ 59
def prefixEnd_1472151 : Nat := 4983230072969 + 3 ^ 40 * 1472151 * 2
def baseEnd_1472151 : Nat := 167982457554927763587157

theorem tailTrace_1472151 : CollatzResearch.WordTrace tailWord_1472151 prefixEnd_1472151 167982457554927763587157 := by
  unfold tailWord_1472151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53693758089655825219072307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35795838726437216812714871 53693758089655825219072307)
  ·
    refine ⟨80540637134483737828608461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53693758089655825219072307 80540637134483737828608461)
    ·
      refine ⟨30202738925431401685728173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80540637134483737828608461 30202738925431401685728173)
      ·
        refine ⟨11326027097036775632148065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30202738925431401685728173 11326027097036775632148065)
        ·
          refine ⟨8494520322777581724111049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11326027097036775632148065 8494520322777581724111049)
          ·
            refine ⟨6370890242083186293083287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8494520322777581724111049 6370890242083186293083287)
            ·
              refine ⟨9556335363124779439624931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370890242083186293083287 9556335363124779439624931)
              ·
                refine ⟨14334503044687169159437397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9556335363124779439624931 14334503044687169159437397)
                ·
                  refine ⟨167982457554927763587157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14334503044687169159437397 167982457554927763587157)
                  ·
                    rfl

theorem cell22_1472151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_1472151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472151 prefixEnd_1472151 := by exact prefixLift 1472151
  have htrace : WordTrace (prefixWord ++ tailWord_1472151) baseStart_1472151 baseEnd_1472151 := by
    simpa [prefixWord, tailWord_1472151, baseEnd_1472151] using wordTrace_append hprefix tailTrace_1472151
  have hstable : (prefixWord ++ tailWord_1472151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472151).length < 2 ^ (prefixWord ++ tailWord_1472151).sum := by decide
  have hdescent : baseEnd_1472151 < baseStart_1472151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472174 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_1472174 : Nat := 118140960795 + 1472174 * 2 ^ 59
def prefixEnd_1472174 : Nat := 4983230072969 + 3 ^ 40 * 1472174 * 2
def baseEnd_1472174 : Nat := 167985082011606299145467

theorem tailTrace_1472174 : CollatzResearch.WordTrace tailWord_1472174 prefixEnd_1472174 167985082011606299145467 := by
  unfold tailWord_1472174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711824621071562518394947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35796397979048333431439717 6711824621071562518394947)
  ·
    refine ⟨10067736931607343777592421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6711824621071562518394947 10067736931607343777592421)
    ·
      refine ⟨1887700674676376958298579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10067736931607343777592421 1887700674676376958298579)
      ·
        refine ⟨2831551012014565437447869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887700674676376958298579 2831551012014565437447869)
        ·
          refine ⟨1061831629505462039042951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2831551012014565437447869 1061831629505462039042951)
          ·
            refine ⟨1592747444258193058564427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061831629505462039042951 1592747444258193058564427)
            ·
              refine ⟨2389121166387289587846641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592747444258193058564427 2389121166387289587846641)
              ·
                refine ⟨1791840874790467190884981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2389121166387289587846641 1791840874790467190884981)
                ·
                  refine ⟨167985082011606299145467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791840874790467190884981 167985082011606299145467)
                  ·
                    rfl

theorem cell22_1472174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_1472174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472174 prefixEnd_1472174 := by exact prefixLift 1472174
  have htrace : WordTrace (prefixWord ++ tailWord_1472174) baseStart_1472174 baseEnd_1472174 := by
    simpa [prefixWord, tailWord_1472174, baseEnd_1472174] using wordTrace_append hprefix tailTrace_1472174
  have hstable : (prefixWord ++ tailWord_1472174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472174).length < 2 ^ (prefixWord ++ tailWord_1472174).sum := by decide
  have hdescent : baseEnd_1472174 < baseStart_1472174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472296 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1472296 : Nat := 118140960795 + 1472296 * 2 ^ 59
def prefixEnd_1472296 : Nat := 4983230072969 + 3 ^ 40 * 1472296 * 2
def baseEnd_1472296 : Nat := 503997009128051245886027

theorem tailTrace_1472296 : CollatzResearch.WordTrace tailWord_1472296 prefixEnd_1472296 503997009128051245886027 := by
  unfold tailWord_1472296
  simp only [CollatzResearch.WordTrace]
  refine ⟨26849523337065257491550371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35799364449420343322067161 26849523337065257491550371)
  ·
    refine ⟨40274285005597886237325557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26849523337065257491550371 40274285005597886237325557)
    ·
      refine ⟨3775714219274801834749271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40274285005597886237325557 3775714219274801834749271)
      ·
        refine ⟨5663571328912202752123907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775714219274801834749271 5663571328912202752123907)
        ·
          refine ⟨8495356993368304128185861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663571328912202752123907 8495356993368304128185861)
          ·
            refine ⟨1592879436256557024034849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8495356993368304128185861 1592879436256557024034849)
            ·
              refine ⟨1194659577192417768026137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592879436256557024034849 1194659577192417768026137)
              ·
                refine ⟨895994682894313326019603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194659577192417768026137 895994682894313326019603)
                ·
                  refine ⟨1343992024341469989029405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895994682894313326019603 1343992024341469989029405)
                  ·
                    refine ⟨503997009128051245886027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1343992024341469989029405 503997009128051245886027)
                    ·
                      rfl

theorem cell22_1472296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1472296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472296 prefixEnd_1472296 := by exact prefixLift 1472296
  have htrace : WordTrace (prefixWord ++ tailWord_1472296) baseStart_1472296 baseEnd_1472296 := by
    simpa [prefixWord, tailWord_1472296, baseEnd_1472296] using wordTrace_append hprefix tailTrace_1472296
  have hstable : (prefixWord ++ tailWord_1472296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472296).length < 2 ^ (prefixWord ++ tailWord_1472296).sum := by decide
  have hdescent : baseEnd_1472296 < baseStart_1472296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472337 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 4]
def baseStart_1472337 : Nat := 118140960795 + 1472337 * 2 ^ 59
def prefixEnd_1472337 : Nat := 4983230072969 + 3 ^ 40 * 1472337 * 2
def baseEnd_1472337 : Nat := 168003681421980268536967

theorem tailTrace_1472337 : CollatzResearch.WordTrace tailWord_1472337 prefixEnd_1472337 168003681421980268536967 := by
  unfold tailWord_1472337
  simp only [CollatzResearch.WordTrace]
  refine ⟨53700542066981978985343265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35800361377987985990228843 53700542066981978985343265)
  ·
    refine ⟨40275406550236484239007449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53700542066981978985343265 40275406550236484239007449)
    ·
      refine ⟨30206554912677363179255587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40275406550236484239007449 30206554912677363179255587)
      ·
        refine ⟨45309832369016044768883381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30206554912677363179255587 45309832369016044768883381)
        ·
          refine ⟨4247796784595254197082817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45309832369016044768883381 4247796784595254197082817)
          ·
            refine ⟨3185847588446440647812113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247796784595254197082817 3185847588446440647812113)
            ·
              refine ⟨2389385691334830485859085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185847588446440647812113 2389385691334830485859085)
              ·
                refine ⟨896019634250561432197157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2389385691334830485859085 896019634250561432197157)
                ·
                  refine ⟨168003681421980268536967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896019634250561432197157 168003681421980268536967)
                  ·
                    rfl

theorem cell22_1472337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_1472337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472337 prefixEnd_1472337 := by exact prefixLift 1472337
  have htrace : WordTrace (prefixWord ++ tailWord_1472337) baseStart_1472337 baseEnd_1472337 := by
    simpa [prefixWord, tailWord_1472337, baseEnd_1472337] using wordTrace_append hprefix tailTrace_1472337
  have hstable : (prefixWord ++ tailWord_1472337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472337).length < 2 ^ (prefixWord ++ tailWord_1472337).sum := by decide
  have hdescent : baseEnd_1472337 < baseStart_1472337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472352 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_1472352 : Nat := 118140960795 + 1472352 * 2 ^ 59
def prefixEnd_1472352 : Nat := 4983230072969 + 3 ^ 40 * 1472352 * 2
def baseEnd_1472352 : Nat := 504016179072485766485855

theorem tailTrace_1472352 : CollatzResearch.WordTrace tailWord_1472352 prefixEnd_1472352 504016179072485766485855 := by
  unfold tailWord_1472352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26850544580963818273569655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35800726107951757698092873 26850544580963818273569655)
  ·
    refine ⟨40275816871445727410354483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26850544580963818273569655 40275816871445727410354483)
    ·
      refine ⟨60413725307168591115531725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40275816871445727410354483 60413725307168591115531725)
      ·
        refine ⟨22655146990188221668324397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60413725307168591115531725 22655146990188221668324397)
        ·
          refine ⟨8495680121320583125621649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22655146990188221668324397 8495680121320583125621649)
          ·
            refine ⟨6371760090990437344216237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8495680121320583125621649 6371760090990437344216237)
            ·
              refine ⟨2389410034121414004081089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6371760090990437344216237 2389410034121414004081089)
              ·
                refine ⟨1792057525591060503060817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2389410034121414004081089 1792057525591060503060817)
                ·
                  refine ⟨1344043144193295377295613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1792057525591060503060817 1344043144193295377295613)
                  ·
                    refine ⟨504016179072485766485855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344043144193295377295613 504016179072485766485855)
                    ·
                      rfl

theorem cell22_1472352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_1472352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472352 prefixEnd_1472352 := by exact prefixLift 1472352
  have htrace : WordTrace (prefixWord ++ tailWord_1472352) baseStart_1472352 baseEnd_1472352 := by
    simpa [prefixWord, tailWord_1472352, baseEnd_1472352] using wordTrace_append hprefix tailTrace_1472352
  have hstable : (prefixWord ++ tailWord_1472352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472352).length < 2 ^ (prefixWord ++ tailWord_1472352).sum := by decide
  have hdescent : baseEnd_1472352 < baseStart_1472352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472378 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1472378 : Nat := 118140960795 + 1472378 * 2 ^ 59
def prefixEnd_1472378 : Nat := 4983230072969 + 3 ^ 40 * 1472378 * 2
def baseEnd_1472378 : Nat := 504025079403830365335775

theorem tailTrace_1472378 : CollatzResearch.WordTrace tailWord_1472378 prefixEnd_1472378 504025079403830365335775 := by
  unfold tailWord_1472378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425509364958360746896447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35801358306555628658390525 13425509364958360746896447)
  ·
    refine ⟨20138264047437541120344671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13425509364958360746896447 20138264047437541120344671)
    ·
      refine ⟨30207396071156311680517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20138264047437541120344671 30207396071156311680517007)
      ·
        refine ⟨45311094106734467520775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30207396071156311680517007 45311094106734467520775511)
        ·
          refine ⟨67966641160101701281163267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45311094106734467520775511 67966641160101701281163267)
          ·
            refine ⟨101949961740152551921744901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67966641160101701281163267 101949961740152551921744901)
            ·
              refine ⟨19115617826278603485327169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101949961740152551921744901 19115617826278603485327169)
              ·
                refine ⟨14336713369708952613995377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19115617826278603485327169 14336713369708952613995377)
                ·
                  refine ⟨10752535027281714460496533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14336713369708952613995377 10752535027281714460496533)
                  ·
                    refine ⟨504025079403830365335775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10752535027281714460496533 504025079403830365335775)
                    ·
                      rfl

theorem cell22_1472378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1472378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472378 prefixEnd_1472378 := by exact prefixLift 1472378
  have htrace : WordTrace (prefixWord ++ tailWord_1472378) baseStart_1472378 baseEnd_1472378 := by
    simpa [prefixWord, tailWord_1472378, baseEnd_1472378] using wordTrace_append hprefix tailTrace_1472378
  have hstable : (prefixWord ++ tailWord_1472378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472378).length < 2 ^ (prefixWord ++ tailWord_1472378).sum := by decide
  have hdescent : baseEnd_1472378 < baseStart_1472378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472382 : List Nat := [4, 2, 3, 1, 1, 2, 1, 8]
def baseStart_1472382 : Nat := 118140960795 + 1472382 * 2 ^ 59
def prefixEnd_1472382 : Nat := 4983230072969 + 3 ^ 40 * 1472382 * 2
def baseEnd_1472382 : Nat := 56002938742841743137307

theorem tailTrace_1472382 : CollatzResearch.WordTrace tailWord_1472382 prefixEnd_1472382 56002938742841743137307 := by
  unfold tailWord_1472382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712772918977368958841425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35801455567879301113820933 6712772918977368958841425)
  ·
    refine ⟨5034579689233026719131069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6712772918977368958841425 5034579689233026719131069)
    ·
      refine ⟨1887967383462385019674151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5034579689233026719131069 1887967383462385019674151)
      ·
        refine ⟨2831951075193577529511227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887967383462385019674151 2831951075193577529511227)
        ·
          refine ⟨4247926612790366294266841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831951075193577529511227 4247926612790366294266841)
          ·
            refine ⟨3185944959592774720700131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247926612790366294266841 3185944959592774720700131)
            ·
              refine ⟨4778917439389162081050197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185944959592774720700131 4778917439389162081050197)
              ·
                refine ⟨56002938742841743137307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4778917439389162081050197 56002938742841743137307)
                ·
                  rfl

theorem cell22_1472382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_1472382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472382 prefixEnd_1472382 := by exact prefixLift 1472382
  have htrace : WordTrace (prefixWord ++ tailWord_1472382) baseStart_1472382 baseEnd_1472382 := by
    simpa [prefixWord, tailWord_1472382, baseEnd_1472382] using wordTrace_append hprefix tailTrace_1472382
  have hstable : (prefixWord ++ tailWord_1472382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472382).length < 2 ^ (prefixWord ++ tailWord_1472382).sum := by decide
  have hdescent : baseEnd_1472382 < baseStart_1472382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472393 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 9]
def baseStart_1472393 : Nat := 118140960795 + 1472393 * 2 ^ 59
def prefixEnd_1472393 : Nat := 4983230072969 + 3 ^ 40 * 1472393 * 2
def baseEnd_1472393 : Nat := 168010071403458442070243

theorem tailTrace_1472393 : CollatzResearch.WordTrace tailWord_1472393 prefixEnd_1472393 168010071403458442070243 := by
  unfold tailWord_1472393
  simp only [CollatzResearch.WordTrace]
  refine ⟨53702584554779100549381833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35801723036519400366254555 53702584554779100549381833)
  ·
    refine ⟨40276938416084325412036375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53702584554779100549381833 40276938416084325412036375)
    ·
      refine ⟨60415407624126488118054563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40276938416084325412036375 60415407624126488118054563)
      ·
        refine ⟨90623111436189732177081845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60415407624126488118054563 90623111436189732177081845)
        ·
          refine ⟨8495916697142787391601423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90623111436189732177081845 8495916697142787391601423)
          ·
            refine ⟨12743875045714181087402135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8495916697142787391601423 12743875045714181087402135)
            ·
              refine ⟨19115812568571271631103203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12743875045714181087402135 19115812568571271631103203)
              ·
                refine ⟨28673718852856907446654805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19115812568571271631103203 28673718852856907446654805)
                ·
                  refine ⟨168010071403458442070243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28673718852856907446654805 168010071403458442070243)
                  ·
                    rfl

theorem cell22_1472393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_1472393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472393 prefixEnd_1472393 := by exact prefixLift 1472393
  have htrace : WordTrace (prefixWord ++ tailWord_1472393) baseStart_1472393 baseEnd_1472393 := by
    simpa [prefixWord, tailWord_1472393, baseEnd_1472393] using wordTrace_append hprefix tailTrace_1472393
  have hstable : (prefixWord ++ tailWord_1472393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472393).length < 2 ^ (prefixWord ++ tailWord_1472393).sum := by decide
  have hdescent : baseEnd_1472393 < baseStart_1472393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472410 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1472410 : Nat := 118140960795 + 1472410 * 2 ^ 59
def prefixEnd_1472410 : Nat := 4983230072969 + 3 ^ 40 * 1472410 * 2
def baseEnd_1472410 : Nat := 168012011219264316178559

theorem tailTrace_1472410 : CollatzResearch.WordTrace tailWord_1472410 prefixEnd_1472410 168012011219264316178559 := by
  unfold tailWord_1472410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425801148929378113187671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35802136397145008301833789 13425801148929378113187671)
  ·
    refine ⟨20138701723394067169781507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13425801148929378113187671 20138701723394067169781507)
    ·
      refine ⟨30208052585091100754672261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20138701723394067169781507 30208052585091100754672261)
      ·
        refine ⟨5664009859704581391501049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30208052585091100754672261 5664009859704581391501049)
        ·
          refine ⟨4248007394778436043625787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5664009859704581391501049 4248007394778436043625787)
          ·
            refine ⟨6372011092167654065438681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248007394778436043625787 6372011092167654065438681)
            ·
              refine ⟨4779008319125740549079011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372011092167654065438681 4779008319125740549079011)
              ·
                refine ⟨7168512478688610823618517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779008319125740549079011 7168512478688610823618517)
                ·
                  refine ⟨168012011219264316178559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7168512478688610823618517 168012011219264316178559)
                  ·
                    rfl

theorem cell22_1472410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1472410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472410 prefixEnd_1472410 := by exact prefixLift 1472410
  have htrace : WordTrace (prefixWord ++ tailWord_1472410) baseStart_1472410 baseEnd_1472410 := by
    simpa [prefixWord, tailWord_1472410, baseEnd_1472410] using wordTrace_append hprefix tailTrace_1472410
  have hstable : (prefixWord ++ tailWord_1472410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472410).length < 2 ^ (prefixWord ++ tailWord_1472410).sum := by decide
  have hdescent : baseEnd_1472410 < baseStart_1472410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472440 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_1472440 : Nat := 118140960795 + 1472440 * 2 ^ 59
def prefixEnd_1472440 : Nat := 4983230072969 + 3 ^ 40 * 1472440 * 2
def baseEnd_1472440 : Nat := 504046303270882870285585

theorem tailTrace_1472440 : CollatzResearch.WordTrace tailWord_1472440 prefixEnd_1472440 504046303270882870285585 := by
  unfold tailWord_1472440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852149392804413788171387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35802865857072551717561849 26852149392804413788171387)
  ·
    refine ⟨40278224089206620682257081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26852149392804413788171387 40278224089206620682257081)
    ·
      refine ⟨30208668066904965511692811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40278224089206620682257081 30208668066904965511692811)
      ·
        refine ⟨45313002100357448267539217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30208668066904965511692811 45313002100357448267539217)
        ·
          refine ⟨33984751575268086200654413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45313002100357448267539217 33984751575268086200654413)
          ·
            refine ⟨12744281840725532325245405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33984751575268086200654413 12744281840725532325245405)
            ·
              refine ⟨4779105690272074621967027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12744281840725532325245405 4779105690272074621967027)
              ·
                refine ⟨7168658535408111932950541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779105690272074621967027 7168658535408111932950541)
                ·
                  refine ⟨2688246950778041974856453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7168658535408111932950541 2688246950778041974856453)
                  ·
                    refine ⟨504046303270882870285585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688246950778041974856453 504046303270882870285585)
                    ·
                      rfl

theorem cell22_1472440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_1472440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472440 prefixEnd_1472440 := by exact prefixLift 1472440
  have htrace : WordTrace (prefixWord ++ tailWord_1472440) baseStart_1472440 baseEnd_1472440 := by
    simpa [prefixWord, tailWord_1472440, baseEnd_1472440] using wordTrace_append hprefix tailTrace_1472440
  have hstable : (prefixWord ++ tailWord_1472440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472440).length < 2 ^ (prefixWord ++ tailWord_1472440).sum := by decide
  have hdescent : baseEnd_1472440 < baseStart_1472440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472472 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_1472472 : Nat := 118140960795 + 1472472 * 2 ^ 59
def prefixEnd_1472472 : Nat := 4983230072969 + 3 ^ 40 * 1472472 * 2
def baseEnd_1472472 : Nat := 168019085841615151161829

theorem tailTrace_1472472 : CollatzResearch.WordTrace tailWord_1472472 prefixEnd_1472472 168019085841615151161829 := by
  unfold tailWord_1472472
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852732960746448520753835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35803643947661931361005113 26852732960746448520753835)
  ·
    refine ⟨40279099441119672781130753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26852732960746448520753835 40279099441119672781130753)
    ·
      refine ⟨30209324580839754585848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40279099441119672781130753 30209324580839754585848065)
      ·
        refine ⟨22656993435629815939386049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30209324580839754585848065 22656993435629815939386049)
        ·
          refine ⟨16992745076722361954539537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22656993435629815939386049 16992745076722361954539537)
          ·
            refine ⟨12744558807541771465904653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16992745076722361954539537 12744558807541771465904653)
            ·
              refine ⟨4779209552828164299714245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12744558807541771465904653 4779209552828164299714245)
              ·
                refine ⟨896101791155280806196421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4779209552828164299714245 896101791155280806196421)
                ·
                  refine ⟨168019085841615151161829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896101791155280806196421 168019085841615151161829)
                  ·
                    rfl

theorem cell22_1472472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_1472472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472472 prefixEnd_1472472 := by exact prefixLift 1472472
  have htrace : WordTrace (prefixWord ++ tailWord_1472472) baseStart_1472472 baseEnd_1472472 := by
    simpa [prefixWord, tailWord_1472472, baseEnd_1472472] using wordTrace_append hprefix tailTrace_1472472
  have hstable : (prefixWord ++ tailWord_1472472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472472).length < 2 ^ (prefixWord ++ tailWord_1472472).sum := by decide
  have hdescent : baseEnd_1472472 < baseStart_1472472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472476 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1472476 : Nat := 118140960795 + 1472476 * 2 ^ 59
def prefixEnd_1472476 : Nat := 4983230072969 + 3 ^ 40 * 1472476 * 2
def baseEnd_1472476 : Nat := 504058626806590776385475

theorem tailTrace_1472476 : CollatzResearch.WordTrace tailWord_1472476 prefixEnd_1472476 504058626806590776385475 := by
  unfold tailWord_1472476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852805906739202862326641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35803741208985603816435521 26852805906739202862326641)
  ·
    refine ⟨20139604430054402146744981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26852805906739202862326641 20139604430054402146744981)
    ·
      refine ⟨944043957658800100628671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20139604430054402146744981 944043957658800100628671)
      ·
        refine ⟨1416065936488200150943007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944043957658800100628671 1416065936488200150943007)
        ·
          refine ⟨2124098904732300226414511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416065936488200150943007 2124098904732300226414511)
          ·
            refine ⟨3186148357098450339621767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124098904732300226414511 3186148357098450339621767)
            ·
              refine ⟨4779222535647675509432651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186148357098450339621767 4779222535647675509432651)
              ·
                refine ⟨7168833803471513264148977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779222535647675509432651 7168833803471513264148977)
                ·
                  refine ⟨5376625352603634948111733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7168833803471513264148977 5376625352603634948111733)
                  ·
                    refine ⟨504058626806590776385475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5376625352603634948111733 504058626806590776385475)
                    ·
                      rfl

theorem cell22_1472476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1472476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472476 prefixEnd_1472476 := by exact prefixLift 1472476
  have htrace : WordTrace (prefixWord ++ tailWord_1472476) baseStart_1472476 baseEnd_1472476 := by
    simpa [prefixWord, tailWord_1472476, baseEnd_1472476] using wordTrace_append hprefix tailTrace_1472476
  have hstable : (prefixWord ++ tailWord_1472476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472476).length < 2 ^ (prefixWord ++ tailWord_1472476).sum := by decide
  have hdescent : baseEnd_1472476 < baseStart_1472476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472551 : List Nat := [1, 1, 7, 1, 2, 2, 2, 6]
def baseStart_1472551 : Nat := 118140960795 + 1472551 * 2 ^ 59
def prefixEnd_1472551 : Nat := 4983230072969 + 3 ^ 40 * 1472551 * 2
def baseEnd_1472551 : Nat := 56009366759923953417805

theorem tailTrace_1472551 : CollatzResearch.WordTrace tailWord_1472551 prefixEnd_1472551 56009366759923953417805 := by
  unfold tailWord_1472551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53708347288206693533633507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35805564858804462355755671 53708347288206693533633507)
  ·
    refine ⟨80562520932310040300450261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53708347288206693533633507 80562520932310040300450261)
    ·
      refine ⟨1888184084351016569541803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80562520932310040300450261 1888184084351016569541803)
      ·
        refine ⟨2832276126526524854312705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888184084351016569541803 2832276126526524854312705)
        ·
          refine ⟨2124207094894893640734529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832276126526524854312705 2124207094894893640734529)
          ·
            refine ⟨1593155321171170230550897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124207094894893640734529 1593155321171170230550897)
            ·
              refine ⟨1194866490878377672913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593155321171170230550897 1194866490878377672913173)
              ·
                refine ⟨56009366759923953417805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1194866490878377672913173 56009366759923953417805)
                ·
                  rfl

theorem cell22_1472551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 6].length) (baseStart_1472551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472551 prefixEnd_1472551 := by exact prefixLift 1472551
  have htrace : WordTrace (prefixWord ++ tailWord_1472551) baseStart_1472551 baseEnd_1472551 := by
    simpa [prefixWord, tailWord_1472551, baseEnd_1472551] using wordTrace_append hprefix tailTrace_1472551
  have hstable : (prefixWord ++ tailWord_1472551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472551).length < 2 ^ (prefixWord ++ tailWord_1472551).sum := by decide
  have hdescent : baseEnd_1472551 < baseStart_1472551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472626 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_1472626 : Nat := 118140960795 + 1472626 * 2 ^ 59
def prefixEnd_1472626 : Nat := 4983230072969 + 3 ^ 40 * 1472626 * 2
def baseEnd_1472626 : Nat := 504109974872040385135015

theorem tailTrace_1472626 : CollatzResearch.WordTrace tailWord_1472626 prefixEnd_1472626 504109974872040385135015 := by
  unfold tailWord_1472626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13427770690733745335653433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35807388508623320895075821 13427770690733745335653433)
  ·
    refine ⟨10070828018050309001740075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13427770690733745335653433 10070828018050309001740075)
    ·
      refine ⟨15106242027075463502610113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10070828018050309001740075 15106242027075463502610113)
      ·
        refine ⟨11329681520306597626957585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15106242027075463502610113 11329681520306597626957585)
        ·
          refine ⟨8497261140229948220218189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11329681520306597626957585 8497261140229948220218189)
          ·
            refine ⟨3186472927586230582581821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8497261140229948220218189 3186472927586230582581821)
            ·
              refine ⟨1194927347844836468468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186472927586230582581821 1194927347844836468468183)
              ·
                refine ⟨1792391021767254702702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194927347844836468468183 1792391021767254702702275)
                ·
                  refine ⟨2688586532650882054053413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792391021767254702702275 2688586532650882054053413)
                  ·
                    refine ⟨504109974872040385135015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688586532650882054053413 504109974872040385135015)
                    ·
                      rfl

theorem cell22_1472626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_1472626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472626 prefixEnd_1472626 := by exact prefixLift 1472626
  have htrace : WordTrace (prefixWord ++ tailWord_1472626) baseStart_1472626 baseEnd_1472626 := by
    simpa [prefixWord, tailWord_1472626, baseEnd_1472626] using wordTrace_append hprefix tailTrace_1472626
  have hstable : (prefixWord ++ tailWord_1472626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472626).length < 2 ^ (prefixWord ++ tailWord_1472626).sum := by decide
  have hdescent : baseEnd_1472626 < baseStart_1472626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472641 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 4]
def baseStart_1472641 : Nat := 118140960795 + 1472641 * 2 ^ 59
def prefixEnd_1472641 : Nat := 4983230072969 + 3 ^ 40 * 1472641 * 2
def baseEnd_1472641 : Nat := 168038369892861782003323

theorem tailTrace_1472641 : CollatzResearch.WordTrace tailWord_1472641 prefixEnd_1472641 168038369892861782003323 := by
  unfold tailWord_1472641
  simp only [CollatzResearch.WordTrace]
  refine ⟨53711629857880638904409777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35807753238587092602939851 53711629857880638904409777)
  ·
    refine ⟨40283722393410479178307333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53711629857880638904409777 40283722393410479178307333)
    ·
      refine ⟨7553197948764464845932625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40283722393410479178307333 7553197948764464845932625)
      ·
        refine ⟨5664898461573348634449469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7553197948764464845932625 5664898461573348634449469)
        ·
          refine ⟨2124336923090005737918551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5664898461573348634449469 2124336923090005737918551)
          ·
            refine ⟨3186505384635008606877827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124336923090005737918551 3186505384635008606877827)
            ·
              refine ⟨4779758076952512910316741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186505384635008606877827 4779758076952512910316741)
              ·
                refine ⟨896204639428596170684389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4779758076952512910316741 896204639428596170684389)
                ·
                  refine ⟨168038369892861782003323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896204639428596170684389 168038369892861782003323)
                  ·
                    rfl

theorem cell22_1472641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_1472641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472641 prefixEnd_1472641 := by exact prefixLift 1472641
  have htrace : WordTrace (prefixWord ++ tailWord_1472641) baseStart_1472641 baseEnd_1472641 := by
    simpa [prefixWord, tailWord_1472641, baseEnd_1472641] using wordTrace_append hprefix tailTrace_1472641
  have hstable : (prefixWord ++ tailWord_1472641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472641).length < 2 ^ (prefixWord ++ tailWord_1472641).sum := by decide
  have hdescent : baseEnd_1472641 < baseStart_1472641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472669 : List Nat := [1, 4, 2, 1, 1, 4, 3, 6]
def baseStart_1472669 : Nat := 118140960795 + 1472669 * 2 ^ 59
def prefixEnd_1472669 : Nat := 4983230072969 + 3 ^ 40 * 1472669 * 2
def baseEnd_1472669 : Nat := 56013854961200289589987

theorem tailTrace_1472669 : CollatzResearch.WordTrace tailWord_1472669 prefixEnd_1472669 56013854961200289589987 := by
  unfold tailWord_1472669
  simp only [CollatzResearch.WordTrace]
  refine ⟨53712651101779199686429061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35808434067852799790952707 53712651101779199686429061)
  ·
    refine ⟨10071122081583599941205449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53712651101779199686429061 10071122081583599941205449)
    ·
      refine ⟨7553341561187699955904087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10071122081583599941205449 7553341561187699955904087)
      ·
        refine ⟨11330012341781549933856131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553341561187699955904087 11330012341781549933856131)
        ·
          refine ⟨16995018512672324900784197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330012341781549933856131 16995018512672324900784197)
          ·
            refine ⟨3186565971126060918897037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16995018512672324900784197 3186565971126060918897037)
            ·
              refine ⟨1194962239172272844586389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186565971126060918897037 1194962239172272844586389)
              ·
                refine ⟨56013854961200289589987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1194962239172272844586389 56013854961200289589987)
                ·
                  rfl

theorem cell22_1472669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 6].length) (baseStart_1472669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472669 prefixEnd_1472669 := by exact prefixLift 1472669
  have htrace : WordTrace (prefixWord ++ tailWord_1472669) baseStart_1472669 baseEnd_1472669 := by
    simpa [prefixWord, tailWord_1472669, baseEnd_1472669] using wordTrace_append hprefix tailTrace_1472669
  have hstable : (prefixWord ++ tailWord_1472669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472669).length < 2 ^ (prefixWord ++ tailWord_1472669).sum := by decide
  have hdescent : baseEnd_1472669 < baseStart_1472669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472671 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 2, 4]
def baseStart_1472671 : Nat := 118140960795 + 1472671 * 2 ^ 59
def prefixEnd_1472671 : Nat := 4983230072969 + 3 ^ 40 * 1472671 * 2
def baseEnd_1472671 : Nat := 504125379291675267759877

theorem tailTrace_1472671 : CollatzResearch.WordTrace tailWord_1472671 prefixEnd_1472671 504125379291675267759877 := by
  unfold tailWord_1472671
  simp only [CollatzResearch.WordTrace]
  refine ⟨53712724047771954028001867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35808482698514636018667911 53712724047771954028001867)
  ·
    refine ⟨80569086071657931042002801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53712724047771954028001867 80569086071657931042002801)
    ·
      refine ⟨60426814553743448281502101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80569086071657931042002801 60426814553743448281502101)
      ·
        refine ⟨2832506932206724138195411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60426814553743448281502101 2832506932206724138195411)
        ·
          refine ⟨4248760398310086207293117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832506932206724138195411 4248760398310086207293117)
          ·
            refine ⟨1593285149366282327734919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4248760398310086207293117 1593285149366282327734919)
            ·
              refine ⟨2389927724049423491602379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593285149366282327734919 2389927724049423491602379)
              ·
                refine ⟨3584891586074135237403569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389927724049423491602379 3584891586074135237403569)
                ·
                  refine ⟨2688668689555601428052677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584891586074135237403569 2688668689555601428052677)
                  ·
                    refine ⟨504125379291675267759877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688668689555601428052677 504125379291675267759877)
                    ·
                      rfl

theorem cell22_1472671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_1472671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472671 prefixEnd_1472671 := by exact prefixLift 1472671
  have htrace : WordTrace (prefixWord ++ tailWord_1472671) baseStart_1472671 baseEnd_1472671 := by
    simpa [prefixWord, tailWord_1472671, baseEnd_1472671] using wordTrace_append hprefix tailTrace_1472671
  have hstable : (prefixWord ++ tailWord_1472671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472671).length < 2 ^ (prefixWord ++ tailWord_1472671).sum := by decide
  have hdescent : baseEnd_1472671 < baseStart_1472671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472686 : List Nat := [4, 1, 4, 2, 1, 1, 9]
def baseStart_1472686 : Nat := 118140960795 + 1472686 * 2 ^ 59
def prefixEnd_1472686 : Nat := 4983230072969 + 3 ^ 40 * 1472686 * 2
def baseEnd_1472686 : Nat := 18671500522156304764253

theorem tailTrace_1472686 : CollatzResearch.WordTrace tailWord_1472686 prefixEnd_1472686 18671500522156304764253 := by
  unfold tailWord_1472686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714158892839701448724739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35808847428478407726531941 6714158892839701448724739)
  ·
    refine ⟨10071238339259552173087109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714158892839701448724739 10071238339259552173087109)
    ·
      refine ⟨1888357188611166032453833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10071238339259552173087109 1888357188611166032453833)
      ·
        refine ⟨1416267891458374524340375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888357188611166032453833 1416267891458374524340375)
        ·
          refine ⟨2124401837187561786510563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416267891458374524340375 2124401837187561786510563)
          ·
            refine ⟨3186602755781342679765845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124401837187561786510563 3186602755781342679765845)
            ·
              refine ⟨18671500522156304764253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3186602755781342679765845 18671500522156304764253)
              ·
                rfl

theorem cell22_1472686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 9].length) (baseStart_1472686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472686 prefixEnd_1472686 := by exact prefixLift 1472686
  have htrace : WordTrace (prefixWord ++ tailWord_1472686) baseStart_1472686 baseEnd_1472686 := by
    simpa [prefixWord, tailWord_1472686, baseEnd_1472686] using wordTrace_append hprefix tailTrace_1472686
  have hstable : (prefixWord ++ tailWord_1472686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472686).length < 2 ^ (prefixWord ++ tailWord_1472686).sum := by decide
  have hdescent : baseEnd_1472686 < baseStart_1472686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472697 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 7]
def baseStart_1472697 : Nat := 118140960795 + 1472697 * 2 ^ 59
def prefixEnd_1472697 : Nat := 4983230072969 + 3 ^ 40 * 1472697 * 2
def baseEnd_1472697 : Nat := 168044759874339955536599

theorem tailTrace_1472697 : CollatzResearch.WordTrace tailWord_1472697 prefixEnd_1472697 168044759874339955536599 := by
  unfold tailWord_1472697
  simp only [CollatzResearch.WordTrace]
  refine ⟨53713672345677760468448345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35809114897118506978965563 53713672345677760468448345)
  ·
    refine ⟨40285254259258320351336259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53713672345677760468448345 40285254259258320351336259)
    ·
      refine ⟨60427881388887480527004389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40285254259258320351336259 60427881388887480527004389)
      ·
        refine ⟨11330227760416402598813323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60427881388887480527004389 11330227760416402598813323)
        ·
          refine ⟨16995341640624603898219985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330227760416402598813323 16995341640624603898219985)
          ·
            refine ⟨12746506230468452923664989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16995341640624603898219985 12746506230468452923664989)
            ·
              refine ⟨4779939836425669846374371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12746506230468452923664989 4779939836425669846374371)
              ·
                refine ⟨7169909754638504769561557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779939836425669846374371 7169909754638504769561557)
                ·
                  refine ⟨168044759874339955536599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7169909754638504769561557 168044759874339955536599)
                  ·
                    rfl

theorem cell22_1472697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_1472697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472697 prefixEnd_1472697 := by exact prefixLift 1472697
  have htrace : WordTrace (prefixWord ++ tailWord_1472697) baseStart_1472697 baseEnd_1472697 := by
    simpa [prefixWord, tailWord_1472697, baseEnd_1472697] using wordTrace_append hprefix tailTrace_1472697
  have hstable : (prefixWord ++ tailWord_1472697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472697).length < 2 ^ (prefixWord ++ tailWord_1472697).sum := by decide
  have hdescent : baseEnd_1472697 < baseStart_1472697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472789 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1472789 : Nat := 118140960795 + 1472789 * 2 ^ 59
def prefixEnd_1472789 : Nat := 4983230072969 + 3 ^ 40 * 1472789 * 2
def baseEnd_1472789 : Nat := 504165773103162293309515

theorem tailTrace_1472789 : CollatzResearch.WordTrace tailWord_1472789 prefixEnd_1472789 504165773103162293309515 := by
  unfold tailWord_1472789
  simp only [CollatzResearch.WordTrace]
  refine ⟨53717027861344460180797421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35811351907562973453864947 53717027861344460180797421)
  ·
    refine ⟨20143885448004172567799033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53717027861344460180797421 20143885448004172567799033)
    ·
      refine ⟨15107914086003129425849275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20143885448004172567799033 15107914086003129425849275)
      ·
        refine ⟨22661871129004694138773913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15107914086003129425849275 22661871129004694138773913)
        ·
          refine ⟨16996403346753520604080435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661871129004694138773913 16996403346753520604080435)
          ·
            refine ⟨25494605020130280906120653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16996403346753520604080435 25494605020130280906120653)
            ·
              refine ⟨9560476882548855339795245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25494605020130280906120653 9560476882548855339795245)
              ·
                refine ⟨3585178830955820752423217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9560476882548855339795245 3585178830955820752423217)
                ·
                  refine ⟨2688884123216865564317413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585178830955820752423217 2688884123216865564317413)
                  ·
                    refine ⟨504165773103162293309515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688884123216865564317413 504165773103162293309515)
                    ·
                      rfl

theorem cell22_1472789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1472789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472789 prefixEnd_1472789 := by exact prefixLift 1472789
  have htrace : WordTrace (prefixWord ++ tailWord_1472789) baseStart_1472789 baseEnd_1472789 := by
    simpa [prefixWord, tailWord_1472789, baseEnd_1472789] using wordTrace_append hprefix tailTrace_1472789
  have hstable : (prefixWord ++ tailWord_1472789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472789).length < 2 ^ (prefixWord ++ tailWord_1472789).sum := by decide
  have hdescent : baseEnd_1472789 < baseStart_1472789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472866 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1472866 : Nat := 118140960795 + 1472866 * 2 ^ 59
def prefixEnd_1472866 : Nat := 4983230072969 + 3 ^ 40 * 1472866 * 2
def baseEnd_1472866 : Nat := 168064043925586586378093

theorem tailTrace_1472866 : CollatzResearch.WordTrace tailWord_1472866 prefixEnd_1472866 168064043925586586378093 := by
  unfold tailWord_1472866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429959070516375582837613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35813224188043668220900301 13429959070516375582837613)
  ·
    refine ⟨5036234651443640843564105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13429959070516375582837613 5036234651443640843564105)
    ·
      refine ⟨3777175988582730632673079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5036234651443640843564105 3777175988582730632673079)
      ·
        refine ⟨5665763982874095949009619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777175988582730632673079 5665763982874095949009619)
        ·
          refine ⟨8498645974311143923514429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665763982874095949009619 8498645974311143923514429)
          ·
            refine ⟨3186992240366678971317911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8498645974311143923514429 3186992240366678971317911)
            ·
              refine ⟨4780488360550018456976867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186992240366678971317911 4780488360550018456976867)
              ·
                refine ⟨7170732540825027685465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780488360550018456976867 7170732540825027685465301)
                ·
                  refine ⟨168064043925586586378093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7170732540825027685465301 168064043925586586378093)
                  ·
                    rfl

theorem cell22_1472866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1472866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472866 prefixEnd_1472866 := by exact prefixLift 1472866
  have htrace : WordTrace (prefixWord ++ tailWord_1472866) baseStart_1472866 baseEnd_1472866 := by
    simpa [prefixWord, tailWord_1472866, baseEnd_1472866] using wordTrace_append hprefix tailTrace_1472866
  have hstable : (prefixWord ++ tailWord_1472866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472866).length < 2 ^ (prefixWord ++ tailWord_1472866).sum := by decide
  have hdescent : baseEnd_1472866 < baseStart_1472866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472879 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_1472879 : Nat := 118140960795 + 1472879 * 2 ^ 59
def prefixEnd_1472879 : Nat := 4983230072969 + 3 ^ 40 * 1472879 * 2
def baseEnd_1472879 : Nat := 504196581942432058559239

theorem tailTrace_1472879 : CollatzResearch.WordTrace tailWord_1472879 prefixEnd_1472879 504196581942432058559239 := by
  unfold tailWord_1472879
  simp only [CollatzResearch.WordTrace]
  refine ⟨53720310431018405551573691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35813540287345603701049127 53720310431018405551573691)
  ·
    refine ⟨80580465646527608327360537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53720310431018405551573691 80580465646527608327360537)
    ·
      refine ⟨60435349234895706245520403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80580465646527608327360537 60435349234895706245520403)
      ·
        refine ⟨90653023852343559368280605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60435349234895706245520403 90653023852343559368280605)
        ·
          refine ⟨33994883944628834763105227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90653023852343559368280605 33994883944628834763105227)
          ·
            refine ⟨50992325916943252144657841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33994883944628834763105227 50992325916943252144657841)
            ·
              refine ⟨38244244437707439108493381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50992325916943252144657841 38244244437707439108493381)
              ·
                refine ⟨7170795832070144832842509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38244244437707439108493381 7170795832070144832842509)
                ·
                  refine ⟨2689048437026304312315941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170795832070144832842509 2689048437026304312315941)
                  ·
                    refine ⟨504196581942432058559239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689048437026304312315941 504196581942432058559239)
                    ·
                      rfl

theorem cell22_1472879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_1472879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472879 prefixEnd_1472879 := by exact prefixLift 1472879
  have htrace : WordTrace (prefixWord ++ tailWord_1472879) baseStart_1472879 baseEnd_1472879 := by
    simpa [prefixWord, tailWord_1472879, baseEnd_1472879] using wordTrace_append hprefix tailTrace_1472879
  have hstable : (prefixWord ++ tailWord_1472879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472879).length < 2 ^ (prefixWord ++ tailWord_1472879).sum := by decide
  have hdescent : baseEnd_1472879 < baseStart_1472879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1472954 : Nat := 118140960795 + 1472954 * 2 ^ 59
def prefixEnd_1472954 : Nat := 4983230072969 + 3 ^ 40 * 1472954 * 2
def baseEnd_1472954 : Nat := 504222255975156862934009

theorem tailTrace_1472954 : CollatzResearch.WordTrace tailWord_1472954 prefixEnd_1472954 504222255975156862934009 := by
  unfold tailWord_1472954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430761476436673340138479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35815363937164462240369277 13430761476436673340138479)
  ·
    refine ⟨20146142214655010010207719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13430761476436673340138479 20146142214655010010207719)
    ·
      refine ⟨30219213321982515015311579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20146142214655010010207719 30219213321982515015311579)
      ·
        refine ⟨45328819982973772522967369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30219213321982515015311579 45328819982973772522967369)
        ·
          refine ⟨33996614987230329392225527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45328819982973772522967369 33996614987230329392225527)
          ·
            refine ⟨50994922480845494088338291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33996614987230329392225527 50994922480845494088338291)
            ·
              refine ⟨76492383721268241132507437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50994922480845494088338291 76492383721268241132507437)
              ·
                refine ⟨28684643895475590424690289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76492383721268241132507437 28684643895475590424690289)
                ·
                  refine ⟨21513482921606692818517717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28684643895475590424690289 21513482921606692818517717)
                  ·
                    refine ⟨504222255975156862934009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21513482921606692818517717 504222255975156862934009)
                    ·
                      rfl

theorem cell22_1472954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1472954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472954 prefixEnd_1472954 := by exact prefixLift 1472954
  have htrace : WordTrace (prefixWord ++ tailWord_1472954) baseStart_1472954 baseEnd_1472954 := by
    simpa [prefixWord, tailWord_1472954, baseEnd_1472954] using wordTrace_append hprefix tailTrace_1472954
  have hstable : (prefixWord ++ tailWord_1472954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472954).length < 2 ^ (prefixWord ++ tailWord_1472954).sum := by decide
  have hdescent : baseEnd_1472954 < baseStart_1472954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472956 : List Nat := [2, 2, 2, 4, 1, 1, 2, 8]
def baseStart_1472956 : Nat := 118140960795 + 1472956 * 2 ^ 59
def prefixEnd_1472956 : Nat := 4983230072969 + 3 ^ 40 * 1472956 * 2
def baseEnd_1472956 : Nat := 56024771179558836042667

theorem tailTrace_1472956 : CollatzResearch.WordTrace tailWord_1472956 prefixEnd_1472956 56024771179558836042667 := by
  unfold tailWord_1472956
  simp only [CollatzResearch.WordTrace]
  refine ⟨26861559425869723851063361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35815412567826298468084481 26861559425869723851063361)
  ·
    refine ⟨20146169569402292888297521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26861559425869723851063361 20146169569402292888297521)
    ·
      refine ⟨15109627177051719666223141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20146169569402292888297521 15109627177051719666223141)
      ·
        refine ⟨2833055095697197437416839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15109627177051719666223141 2833055095697197437416839)
        ·
          refine ⟨4249582643545796156125259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833055095697197437416839 4249582643545796156125259)
          ·
            refine ⟨6374373965318694234187889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249582643545796156125259 6374373965318694234187889)
            ·
              refine ⟨4780780473989020675640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6374373965318694234187889 4780780473989020675640917)
              ·
                refine ⟨56024771179558836042667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4780780473989020675640917 56024771179558836042667)
                ·
                  rfl

theorem cell22_1472956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_1472956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1472956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1472956 prefixEnd_1472956 := by exact prefixLift 1472956
  have htrace : WordTrace (prefixWord ++ tailWord_1472956) baseStart_1472956 baseEnd_1472956 := by
    simpa [prefixWord, tailWord_1472956, baseEnd_1472956] using wordTrace_append hprefix tailTrace_1472956
  have hstable : (prefixWord ++ tailWord_1472956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472956).length < 2 ^ (prefixWord ++ tailWord_1472956).sum := by decide
  have hdescent : baseEnd_1472956 < baseStart_1472956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473005 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_1473005 : Nat := 118140960795 + 1473005 * 2 ^ 59
def prefixEnd_1473005 : Nat := 4983230072969 + 3 ^ 40 * 1473005 * 2
def baseEnd_1473005 : Nat := 504239714317409729908853

theorem tailTrace_1473005 : CollatzResearch.WordTrace tailWord_1473005 prefixEnd_1473005 504239714317409729908853 := by
  unfold tailWord_1473005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53724906028561929070660469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35816604019041286047106979 53724906028561929070660469)
  ·
    refine ⟨5036709940177680850374419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53724906028561929070660469 5036709940177680850374419)
    ·
      refine ⟨7555064910266521275561629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036709940177680850374419 7555064910266521275561629)
      ·
        refine ⟨2833149341349945478335611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7555064910266521275561629 2833149341349945478335611)
        ·
          refine ⟨4249724012024918217503417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833149341349945478335611 4249724012024918217503417)
          ·
            refine ⟨3187293009018688663127563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4249724012024918217503417 3187293009018688663127563)
            ·
              refine ⟨4780939513528032994691345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187293009018688663127563 4780939513528032994691345)
              ·
                refine ⟨3585704635146024746018509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780939513528032994691345 3585704635146024746018509)
                ·
                  refine ⟨1344639238179759279756941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3585704635146024746018509 1344639238179759279756941)
                  ·
                    refine ⟨504239714317409729908853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344639238179759279756941 504239714317409729908853)
                    ·
                      rfl

theorem cell22_1473005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_1473005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473005 prefixEnd_1473005 := by exact prefixLift 1473005
  have htrace : WordTrace (prefixWord ++ tailWord_1473005) baseStart_1473005 baseEnd_1473005 := by
    simpa [prefixWord, tailWord_1473005, baseEnd_1473005] using wordTrace_append hprefix tailTrace_1473005
  have hstable : (prefixWord ++ tailWord_1473005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473005).length < 2 ^ (prefixWord ++ tailWord_1473005).sum := by decide
  have hdescent : baseEnd_1473005 < baseStart_1473005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473093 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_1473093 : Nat := 118140960795 + 1473093 * 2 ^ 59
def prefixEnd_1473093 : Nat := 4983230072969 + 3 ^ 40 * 1473093 * 2
def baseEnd_1473093 : Nat := 504269838515806833708583

theorem tailTrace_1473093 : CollatzResearch.WordTrace tailWord_1473093 prefixEnd_1473093 504269838515806833708583 := by
  unfold tailWord_1473093
  simp only [CollatzResearch.WordTrace]
  refine ⟨53728115652243120099863933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35818743768162080066575955 53728115652243120099863933)
  ·
    refine ⟨20148043369591170037448975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53728115652243120099863933 20148043369591170037448975)
    ·
      refine ⟨30222065054386755056173463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20148043369591170037448975 30222065054386755056173463)
      ·
        refine ⟨45333097581580132584260195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30222065054386755056173463 45333097581580132584260195)
        ·
          refine ⟨67999646372370198876390293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45333097581580132584260195 67999646372370198876390293)
          ·
            refine ⟨3187483423704853072330795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67999646372370198876390293 3187483423704853072330795)
            ·
              refine ⟨4781225135557279608496193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187483423704853072330795 4781225135557279608496193)
              ·
                refine ⟨3585918851667959706372145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781225135557279608496193 3585918851667959706372145)
                ·
                  refine ⟨2689439138750969779779109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585918851667959706372145 2689439138750969779779109)
                  ·
                    refine ⟨504269838515806833708583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689439138750969779779109 504269838515806833708583)
                    ·
                      rfl

theorem cell22_1473093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_1473093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473093 prefixEnd_1473093 := by exact prefixLift 1473093
  have htrace : WordTrace (prefixWord ++ tailWord_1473093) baseStart_1473093 baseEnd_1473093 := by
    simpa [prefixWord, tailWord_1473093, baseEnd_1473093] using wordTrace_append hprefix tailTrace_1473093
  have hstable : (prefixWord ++ tailWord_1473093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473093).length < 2 ^ (prefixWord ++ tailWord_1473093).sum := by decide
  have hdescent : baseEnd_1473093 < baseStart_1473093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473108 : List Nat := [2, 4, 1, 1, 1, 4, 2, 7]
def baseStart_1473108 : Nat := 118140960795 + 1473108 * 2 ^ 59
def prefixEnd_1473108 : Nat := 4983230072969 + 3 ^ 40 * 1473108 * 2
def baseEnd_1473108 : Nat := 56030552591372421620393

theorem tailTrace_1473108 : CollatzResearch.WordTrace tailWord_1473108 prefixEnd_1473108 56030552591372421620393 := by
  unfold tailWord_1473108
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864331373594388830829989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35819108498125851774439985 26864331373594388830829989)
  ·
    refine ⟨5037062132548947905780623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26864331373594388830829989 5037062132548947905780623)
    ·
      refine ⟨7555593198823421858670935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5037062132548947905780623 7555593198823421858670935)
      ·
        refine ⟨11333389798235132788006403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7555593198823421858670935 11333389798235132788006403)
        ·
          refine ⟨17000084697352699182009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11333389798235132788006403 17000084697352699182009605)
          ·
            refine ⟨3187515880753631096626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17000084697352699182009605 3187515880753631096626801)
            ·
              refine ⟨2390636910565223322470101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187515880753631096626801 2390636910565223322470101)
              ·
                refine ⟨56030552591372421620393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2390636910565223322470101 56030552591372421620393)
                ·
                  rfl

theorem cell22_1473108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_1473108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473108 prefixEnd_1473108 := by exact prefixLift 1473108
  have htrace : WordTrace (prefixWord ++ tailWord_1473108) baseStart_1473108 baseEnd_1473108 := by
    simpa [prefixWord, tailWord_1473108, baseEnd_1473108] using wordTrace_append hprefix tailTrace_1473108
  have hstable : (prefixWord ++ tailWord_1473108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473108).length < 2 ^ (prefixWord ++ tailWord_1473108).sum := by decide
  have hdescent : baseEnd_1473108 < baseStart_1473108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473123 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 5, 3]
def baseStart_1473123 : Nat := 118140960795 + 1473123 * 2 ^ 59
def prefixEnd_1473123 : Nat := 4983230072969 + 3 ^ 40 * 1473123 * 2
def baseEnd_1473123 : Nat := 504280108128896755458491

theorem tailTrace_1473123 : CollatzResearch.WordTrace tailWord_1473123 prefixEnd_1473123 504280108128896755458491 := by
  unfold tailWord_1473123
  simp only [CollatzResearch.WordTrace]
  refine ⟨53729209842134435223456023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35819473228089623482304015 53729209842134435223456023)
  ·
    refine ⟨80593814763201652835184035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53729209842134435223456023 80593814763201652835184035)
    ·
      refine ⟨120890722144802479252776053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80593814763201652835184035 120890722144802479252776053)
      ·
        refine ⟨11333505201075232429947755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120890722144802479252776053 11333505201075232429947755)
        ·
          refine ⟨17000257801612848644921633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11333505201075232429947755 17000257801612848644921633)
          ·
            refine ⟨12750193351209636483691225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17000257801612848644921633 12750193351209636483691225)
            ·
              refine ⟨9562645013407227362768419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12750193351209636483691225 9562645013407227362768419)
              ·
                refine ⟨14343967520110841044152629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9562645013407227362768419 14343967520110841044152629)
                ·
                  refine ⟨1344746955010391347889309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14343967520110841044152629 1344746955010391347889309)
                  ·
                    refine ⟨504280108128896755458491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344746955010391347889309 504280108128896755458491)
                    ·
                      rfl

theorem cell22_1473123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].length) (baseStart_1473123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473123 prefixEnd_1473123 := by exact prefixLift 1473123
  have htrace : WordTrace (prefixWord ++ tailWord_1473123) baseStart_1473123 baseEnd_1473123 := by
    simpa [prefixWord, tailWord_1473123, baseEnd_1473123] using wordTrace_append hprefix tailTrace_1473123
  have hstable : (prefixWord ++ tailWord_1473123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473123).length < 2 ^ (prefixWord ++ tailWord_1473123).sum := by decide
  have hdescent : baseEnd_1473123 < baseStart_1473123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473157 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1473157 : Nat := 118140960795 + 1473157 * 2 ^ 59
def prefixEnd_1473157 : Nat := 4983230072969 + 3 ^ 40 * 1473157 * 2
def baseEnd_1473157 : Nat := 504291747023732000108387

theorem tailTrace_1473157 : CollatzResearch.WordTrace tailWord_1473157 prefixEnd_1473157 504291747023732000108387 := by
  unfold tailWord_1473157
  simp only [CollatzResearch.WordTrace]
  refine ⟨53730449924011259030193725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35820299949340839353462483 53730449924011259030193725)
  ·
    refine ⟨20148918721504222136322647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53730449924011259030193725 20148918721504222136322647)
    ·
      refine ⟨30223378082256333204483971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20148918721504222136322647 30223378082256333204483971)
      ·
        refine ⟨45335067123384499806725957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30223378082256333204483971 45335067123384499806725957)
        ·
          refine ⟨8500325085634593713761117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45335067123384499806725957 8500325085634593713761117)
          ·
            refine ⟨3187621907112972642660419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8500325085634593713761117 3187621907112972642660419)
            ·
              refine ⟨4781432860669458963990629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187621907112972642660419 4781432860669458963990629)
              ·
                refine ⟨896518661375523555748243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4781432860669458963990629 896518661375523555748243)
                ·
                  refine ⟨1344777992063285333622365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896518661375523555748243 1344777992063285333622365)
                  ·
                    refine ⟨504291747023732000108387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344777992063285333622365 504291747023732000108387)
                    ·
                      rfl

theorem cell22_1473157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1473157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473157 prefixEnd_1473157 := by exact prefixLift 1473157
  have htrace : WordTrace (prefixWord ++ tailWord_1473157) baseStart_1473157 baseEnd_1473157 := by
    simpa [prefixWord, tailWord_1473157, baseEnd_1473157] using wordTrace_append hprefix tailTrace_1473157
  have hstable : (prefixWord ++ tailWord_1473157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473157).length < 2 ^ (prefixWord ++ tailWord_1473157).sum := by decide
  have hdescent : baseEnd_1473157 < baseStart_1473157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473170 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1473170 : Nat := 118140960795 + 1473170 * 2 ^ 59
def prefixEnd_1473170 : Nat := 4983230072969 + 3 ^ 40 * 1473170 * 2
def baseEnd_1473170 : Nat := 168098732396468099844449

theorem tailTrace_1473170 : CollatzResearch.WordTrace tailWord_1473170 prefixEnd_1473170 168098732396468099844449 := by
  unfold tailWord_1473170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432731018241040562604241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35820616048642774833611309 13432731018241040562604241)
  ·
    refine ⟨10074548263680780421953181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13432731018241040562604241 10074548263680780421953181)
    ·
      refine ⟨3777955598880292658232443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10074548263680780421953181 3777955598880292658232443)
      ·
        refine ⟨5666933398320438987348665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777955598880292658232443 5666933398320438987348665)
        ·
          refine ⟨4250200048740329240511499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5666933398320438987348665 4250200048740329240511499)
          ·
            refine ⟨6375300073110493860767249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250200048740329240511499 6375300073110493860767249)
            ·
              refine ⟨4781475054832870395575437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375300073110493860767249 4781475054832870395575437)
              ·
                refine ⟨1793053145562326398340789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4781475054832870395575437 1793053145562326398340789)
                ·
                  refine ⟨168098732396468099844449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1793053145562326398340789 168098732396468099844449)
                  ·
                    rfl

theorem cell22_1473170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1473170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473170 prefixEnd_1473170 := by exact prefixLift 1473170
  have htrace : WordTrace (prefixWord ++ tailWord_1473170) baseStart_1473170 baseEnd_1473170 := by
    simpa [prefixWord, tailWord_1473170, baseEnd_1473170] using wordTrace_append hprefix tailTrace_1473170
  have hstable : (prefixWord ++ tailWord_1473170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473170).length < 2 ^ (prefixWord ++ tailWord_1473170).sum := by decide
  have hdescent : baseEnd_1473170 < baseStart_1473170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473191 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1473191 : Nat := 118140960795 + 1473191 * 2 ^ 59
def prefixEnd_1473191 : Nat := 4983230072969 + 3 ^ 40 * 1473191 * 2
def baseEnd_1473191 : Nat := 504303385918567244758283

theorem tailTrace_1473191 : CollatzResearch.WordTrace tailWord_1473191 prefixEnd_1473191 504303385918567244758283 := by
  unfold tailWord_1473191
  simp only [CollatzResearch.WordTrace]
  refine ⟨53731690005888082836931427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35821126670592055224620951 53731690005888082836931427)
  ·
    refine ⟨80597535008832124255397141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53731690005888082836931427 80597535008832124255397141)
    ·
      refine ⟨3778009453539005824471741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80597535008832124255397141 3778009453539005824471741)
      ·
        refine ⟨1416753545077127184176903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3778009453539005824471741 1416753545077127184176903)
        ·
          refine ⟨2125130317615690776265355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416753545077127184176903 2125130317615690776265355)
          ·
            refine ⟨3187695476423536164398033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125130317615690776265355 3187695476423536164398033)
            ·
              refine ⟨2390771607317652123298525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187695476423536164398033 2390771607317652123298525)
              ·
                refine ⟨896539352744119546236947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2390771607317652123298525 896539352744119546236947)
                ·
                  refine ⟨1344809029116179319355421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896539352744119546236947 1344809029116179319355421)
                  ·
                    refine ⟨504303385918567244758283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344809029116179319355421 504303385918567244758283)
                    ·
                      rfl

theorem cell22_1473191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1473191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473191 prefixEnd_1473191 := by exact prefixLift 1473191
  have htrace : WordTrace (prefixWord ++ tailWord_1473191) baseStart_1473191 baseEnd_1473191 := by
    simpa [prefixWord, tailWord_1473191, baseEnd_1473191] using wordTrace_append hprefix tailTrace_1473191
  have hstable : (prefixWord ++ tailWord_1473191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473191).length < 2 ^ (prefixWord ++ tailWord_1473191).sum := by decide
  have hdescent : baseEnd_1473191 < baseStart_1473191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473215 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 4]
def baseStart_1473215 : Nat := 118140960795 + 1473215 * 2 ^ 59
def prefixEnd_1473215 : Nat := 4983230072969 + 3 ^ 40 * 1473215 * 2
def baseEnd_1473215 : Nat := 168103867203013060719403

theorem tailTrace_1473215 : CollatzResearch.WordTrace tailWord_1473215 prefixEnd_1473215 168103867203013060719403 := by
  unfold tailWord_1473215
  simp only [CollatzResearch.WordTrace]
  refine ⟨53732565357801134935805099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35821710238534089957203399 53732565357801134935805099)
  ·
    refine ⟨80598848036701702403707649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53732565357801134935805099 80598848036701702403707649)
    ·
      refine ⟨60449136027526276802780737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80598848036701702403707649 60449136027526276802780737)
      ·
        refine ⟨45336852020644707602085553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60449136027526276802780737 45336852020644707602085553)
        ·
          refine ⟨34002639015483530701564165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45336852020644707602085553 34002639015483530701564165)
          ·
            refine ⟨6375494815403162006543281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34002639015483530701564165 6375494815403162006543281)
            ·
              refine ⟨4781621111552371504907461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375494815403162006543281 4781621111552371504907461)
              ·
                refine ⟨896553958416069657170149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4781621111552371504907461 896553958416069657170149)
                ·
                  refine ⟨168103867203013060719403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896553958416069657170149 168103867203013060719403)
                  ·
                    rfl

theorem cell22_1473215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 4].length) (baseStart_1473215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473215 prefixEnd_1473215 := by exact prefixLift 1473215
  have htrace : WordTrace (prefixWord ++ tailWord_1473215) baseStart_1473215 baseEnd_1473215 := by
    simpa [prefixWord, tailWord_1473215, baseEnd_1473215] using wordTrace_append hprefix tailTrace_1473215
  have hstable : (prefixWord ++ tailWord_1473215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473215).length < 2 ^ (prefixWord ++ tailWord_1473215).sum := by decide
  have hdescent : baseEnd_1473215 < baseStart_1473215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473230 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1473230 : Nat := 118140960795 + 1473230 * 2 ^ 59
def prefixEnd_1473230 : Nat := 4983230072969 + 3 ^ 40 * 1473230 * 2
def baseEnd_1473230 : Nat := 504316736415584143033163

theorem tailTrace_1473230 : CollatzResearch.WordTrace tailWord_1473230 prefixEnd_1473230 504316736415584143033163 := by
  unfold tailWord_1473230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716639056593349062200143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35822074968497861665067429 6716639056593349062200143)
  ·
    refine ⟨10074958584890023593300215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716639056593349062200143 10074958584890023593300215)
    ·
      refine ⟨15112437877335035389950323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10074958584890023593300215 15112437877335035389950323)
      ·
        refine ⟨22668656816002553084925485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15112437877335035389950323 22668656816002553084925485)
        ·
          refine ⟨8500746306000957406847057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22668656816002553084925485 8500746306000957406847057)
          ·
            refine ⟨6375559729500718055135293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8500746306000957406847057 6375559729500718055135293)
            ·
              refine ⟨2390834898562769270675735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6375559729500718055135293 2390834898562769270675735)
              ·
                refine ⟨3586252347844153906013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390834898562769270675735 3586252347844153906013603)
                ·
                  refine ⟨5379378521766230859020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586252347844153906013603 5379378521766230859020405)
                  ·
                    refine ⟨504316736415584143033163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5379378521766230859020405 504316736415584143033163)
                    ·
                      rfl

theorem cell22_1473230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1473230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473230 prefixEnd_1473230 := by exact prefixLift 1473230
  have htrace : WordTrace (prefixWord ++ tailWord_1473230) baseStart_1473230 baseEnd_1473230 := by
    simpa [prefixWord, tailWord_1473230, baseEnd_1473230] using wordTrace_append hprefix tailTrace_1473230
  have hstable : (prefixWord ++ tailWord_1473230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473230).length < 2 ^ (prefixWord ++ tailWord_1473230).sum := by decide
  have hdescent : baseEnd_1473230 < baseStart_1473230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473320 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1473320 : Nat := 118140960795 + 1473320 * 2 ^ 59
def prefixEnd_1473320 : Nat := 4983230072969 + 3 ^ 40 * 1473320 * 2
def baseEnd_1473320 : Nat := 504347545254853908282887

theorem tailTrace_1473320 : CollatzResearch.WordTrace tailWord_1473320 prefixEnd_1473320 504347545254853908282887 := by
  unfold tailWord_1473320
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868197511210368934188707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35824263348280491912251609 26868197511210368934188707)
  ·
    refine ⟨40302296266815553401283061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26868197511210368934188707 40302296266815553401283061)
    ·
      refine ⟨3778340275013958131370287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40302296266815553401283061 3778340275013958131370287)
      ·
        refine ⟨5667510412520937197055431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778340275013958131370287 5667510412520937197055431)
        ·
          refine ⟨8501265618781405795583147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5667510412520937197055431 8501265618781405795583147)
          ·
            refine ⟨12751898428172108693374721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8501265618781405795583147 12751898428172108693374721)
            ·
              refine ⟨9563923821129081520031041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12751898428172108693374721 9563923821129081520031041)
              ·
                refine ⟨7172942865846811140023281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563923821129081520031041 7172942865846811140023281)
                ·
                  refine ⟨5379707149385108355017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172942865846811140023281 5379707149385108355017461)
                  ·
                    refine ⟨504347545254853908282887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5379707149385108355017461 504347545254853908282887)
                    ·
                      rfl

theorem cell22_1473320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1473320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473320 prefixEnd_1473320 := by exact prefixLift 1473320
  have htrace : WordTrace (prefixWord ++ tailWord_1473320) baseStart_1473320 baseEnd_1473320 := by
    simpa [prefixWord, tailWord_1473320, baseEnd_1473320] using wordTrace_append hprefix tailTrace_1473320
  have hstable : (prefixWord ++ tailWord_1473320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473320).length < 2 ^ (prefixWord ++ tailWord_1473320).sum := by decide
  have hdescent : baseEnd_1473320 < baseStart_1473320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473326 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1473326 : Nat := 118140960795 + 1473326 * 2 ^ 59
def prefixEnd_1473326 : Nat := 4983230072969 + 3 ^ 40 * 1473326 * 2
def baseEnd_1473326 : Nat := 504349599177471892632869

theorem tailTrace_1473326 : CollatzResearch.WordTrace tailWord_1473326 prefixEnd_1473326 504349599177471892632869 := by
  unfold tailWord_1473326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6717076732549875111636979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35824409240266000595397221 6717076732549875111636979)
  ·
    refine ⟨10075615098824812667455469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6717076732549875111636979 10075615098824812667455469)
    ·
      refine ⟨3778355662059304750295801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10075615098824812667455469 3778355662059304750295801)
      ·
        refine ⟨2833766746544478562721851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778355662059304750295801 2833766746544478562721851)
        ·
          refine ⟨4250650119816717844082777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833766746544478562721851 4250650119816717844082777)
          ·
            refine ⟨3187987589862538383062083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4250650119816717844082777 3187987589862538383062083)
            ·
              refine ⟨4781981384793807574593125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187987589862538383062083 4781981384793807574593125)
              ·
                refine ⟨896621509648838920236211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4781981384793807574593125 896621509648838920236211)
                ·
                  refine ⟨1344932264473258380354317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896621509648838920236211 1344932264473258380354317)
                  ·
                    refine ⟨504349599177471892632869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1344932264473258380354317 504349599177471892632869)
                    ·
                      rfl

theorem cell22_1473326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1473326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473326 prefixEnd_1473326 := by exact prefixLift 1473326
  have htrace : WordTrace (prefixWord ++ tailWord_1473326) baseStart_1473326 baseEnd_1473326 := by
    simpa [prefixWord, tailWord_1473326, baseEnd_1473326] using wordTrace_append hprefix tailTrace_1473326
  have hstable : (prefixWord ++ tailWord_1473326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473326).length < 2 ^ (prefixWord ++ tailWord_1473326).sum := by decide
  have hdescent : baseEnd_1473326 < baseStart_1473326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473365 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1473365 : Nat := 118140960795 + 1473365 * 2 ^ 59
def prefixEnd_1473365 : Nat := 4983230072969 + 3 ^ 40 * 1473365 * 2
def baseEnd_1473365 : Nat := 504362949674488790907749

theorem tailTrace_1473365 : CollatzResearch.WordTrace tailWord_1473365 prefixEnd_1473365 504362949674488790907749 := by
  unfold tailWord_1473365
  simp only [CollatzResearch.WordTrace]
  refine ⟨53738036307257710553765549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35825357538171807035843699 53738036307257710553765549)
  ·
    refine ⟨20151763615221641457662081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53738036307257710553765549 20151763615221641457662081)
    ·
      refine ⟨15113822711416231093246561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20151763615221641457662081 15113822711416231093246561)
      ·
        refine ⟨11335367033562173319934921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15113822711416231093246561 11335367033562173319934921)
        ·
          refine ⟨8501525275171629989951191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11335367033562173319934921 8501525275171629989951191)
          ·
            refine ⟨12752287912757444984926787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8501525275171629989951191 12752287912757444984926787)
            ·
              refine ⟨19128431869136167477390181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12752287912757444984926787 19128431869136167477390181)
              ·
                refine ⟨3586580975463031402010659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19128431869136167477390181 3586580975463031402010659)
                ·
                  refine ⟨5379871463194547103015989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586580975463031402010659 5379871463194547103015989)
                  ·
                    refine ⟨504362949674488790907749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5379871463194547103015989 504362949674488790907749)
                    ·
                      rfl

theorem cell22_1473365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1473365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473365 prefixEnd_1473365 := by exact prefixLift 1473365
  have htrace : WordTrace (prefixWord ++ tailWord_1473365) baseStart_1473365 baseEnd_1473365 := by
    simpa [prefixWord, tailWord_1473365, baseEnd_1473365] using wordTrace_append hprefix tailTrace_1473365
  have hstable : (prefixWord ++ tailWord_1473365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473365).length < 2 ^ (prefixWord ++ tailWord_1473365).sum := by decide
  have hdescent : baseEnd_1473365 < baseStart_1473365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473367 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 4]
def baseStart_1473367 : Nat := 118140960795 + 1473367 * 2 ^ 59
def prefixEnd_1473367 : Nat := 4983230072969 + 3 ^ 40 * 1473367 * 2
def baseEnd_1473367 : Nat := 168121211438453817452581

theorem tailTrace_1473367 : CollatzResearch.WordTrace tailWord_1473367 prefixEnd_1473367 168121211438453817452581 := by
  unfold tailWord_1473367
  simp only [CollatzResearch.WordTrace]
  refine ⟨53738109253250464895338355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35825406168833643263558903 53738109253250464895338355)
  ·
    refine ⟨80607163879875697343007533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53738109253250464895338355 80607163879875697343007533)
    ·
      refine ⟨30227686454953386503627825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80607163879875697343007533 30227686454953386503627825)
      ·
        refine ⟨22670764841215039877720869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30227686454953386503627825 22670764841215039877720869)
        ·
          refine ⟨4250768407727819977072663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22670764841215039877720869 4250768407727819977072663)
          ·
            refine ⟨6376152611591729965608995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250768407727819977072663 6376152611591729965608995)
            ·
              refine ⟨9564228917387594948413493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376152611591729965608995 9564228917387594948413493)
              ·
                refine ⟨896646461005087026413765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9564228917387594948413493 896646461005087026413765)
                ·
                  refine ⟨168121211438453817452581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 896646461005087026413765 168121211438453817452581)
                  ·
                    rfl

theorem cell22_1473367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 4].length) (baseStart_1473367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473367 prefixEnd_1473367 := by exact prefixLift 1473367
  have htrace : WordTrace (prefixWord ++ tailWord_1473367) baseStart_1473367 baseEnd_1473367 := by
    simpa [prefixWord, tailWord_1473367, baseEnd_1473367] using wordTrace_append hprefix tailTrace_1473367
  have hstable : (prefixWord ++ tailWord_1473367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473367).length < 2 ^ (prefixWord ++ tailWord_1473367).sum := by decide
  have hdescent : baseEnd_1473367 < baseStart_1473367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473369 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_1473369 : Nat := 118140960795 + 1473369 * 2 ^ 59
def prefixEnd_1473369 : Nat := 4983230072969 + 3 ^ 40 * 1473369 * 2
def baseEnd_1473369 : Nat := 504364318956234113807737

theorem tailTrace_1473369 : CollatzResearch.WordTrace tailWord_1473369 prefixEnd_1473369 504364318956234113807737 := by
  unfold tailWord_1473369
  simp only [CollatzResearch.WordTrace]
  refine ⟨53738182199243219236911161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35825454799495479491274107 53738182199243219236911161)
  ·
    refine ⟨40303636649432414427683371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53738182199243219236911161 40303636649432414427683371)
    ·
      refine ⟨60455454974148621641525057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40303636649432414427683371 60455454974148621641525057)
      ·
        refine ⟨45341591230611466231143793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60455454974148621641525057 45341591230611466231143793)
        ·
          refine ⟨34006193422958599673357845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45341591230611466231143793 34006193422958599673357845)
          ·
            refine ⟨1594040316701184359688649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34006193422958599673357845 1594040316701184359688649)
            ·
              refine ⟨1195530237525888269766487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594040316701184359688649 1195530237525888269766487)
              ·
                refine ⟨1793295356288832404649731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195530237525888269766487 1793295356288832404649731)
                ·
                  refine ⟨2689943034433248606974597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793295356288832404649731 2689943034433248606974597)
                  ·
                    refine ⟨504364318956234113807737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689943034433248606974597 504364318956234113807737)
                    ·
                      rfl

theorem cell22_1473369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_1473369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473369 prefixEnd_1473369 := by exact prefixLift 1473369
  have htrace : WordTrace (prefixWord ++ tailWord_1473369) baseStart_1473369 baseEnd_1473369 := by
    simpa [prefixWord, tailWord_1473369, baseEnd_1473369] using wordTrace_append hprefix tailTrace_1473369
  have hstable : (prefixWord ++ tailWord_1473369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473369).length < 2 ^ (prefixWord ++ tailWord_1473369).sum := by decide
  have hdescent : baseEnd_1473369 < baseStart_1473369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473440 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_1473440 : Nat := 118140960795 + 1473440 * 2 ^ 59
def prefixEnd_1473440 : Nat := 4983230072969 + 3 ^ 40 * 1473440 * 2
def baseEnd_1473440 : Nat := 168129541235737865094173

theorem tailTrace_1473440 : CollatzResearch.WordTrace tailWord_1473440 prefixEnd_1473440 168129541235737865094173 := by
  unfold tailWord_1473440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26870385890992999181372887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35827181187990665575163849 26870385890992999181372887)
  ·
    refine ⟨40305578836489498772059331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26870385890992999181372887 40305578836489498772059331)
    ·
      refine ⟨60458368254734248158088997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40305578836489498772059331 60458368254734248158088997)
      ·
        refine ⟨11335944047762671529641687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60458368254734248158088997 11335944047762671529641687)
        ·
          refine ⟨17003916071644007294462531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11335944047762671529641687 17003916071644007294462531)
          ·
            refine ⟨25505874107466010941693797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17003916071644007294462531 25505874107466010941693797)
            ·
              refine ⟨4782351395149877051567587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25505874107466010941693797 4782351395149877051567587)
              ·
                refine ⟨7173527092724815577351381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782351395149877051567587 7173527092724815577351381)
                ·
                  refine ⟨168129541235737865094173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7173527092724815577351381 168129541235737865094173)
                  ·
                    rfl

theorem cell22_1473440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_1473440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473440 prefixEnd_1473440 := by exact prefixLift 1473440
  have htrace : WordTrace (prefixWord ++ tailWord_1473440) baseStart_1473440 baseEnd_1473440 := by
    simpa [prefixWord, tailWord_1473440, baseEnd_1473440] using wordTrace_append hprefix tailTrace_1473440
  have hstable : (prefixWord ++ tailWord_1473440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473440).length < 2 ^ (prefixWord ++ tailWord_1473440).sum := by decide
  have hdescent : baseEnd_1473440 < baseStart_1473440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473530 : List Nat := [3, 1, 1, 1, 1, 2, 1, 12]
def baseStart_1473530 : Nat := 118140960795 + 1473530 * 2 ^ 59
def prefixEnd_1473530 : Nat := 4983230072969 + 3 ^ 40 * 1473530 * 2
def baseEnd_1473530 : Nat := 56046603616275928948027

theorem tailTrace_1473530 : CollatzResearch.WordTrace tailWord_1473530 prefixEnd_1473530 56046603616275928948027 := by
  unfold tailWord_1473530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436013587914985933380511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35829369567773295822348029 13436013587914985933380511)
  ·
    refine ⟨20154020381872478900070767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13436013587914985933380511 20154020381872478900070767)
    ·
      refine ⟨30231030572808718350106151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20154020381872478900070767 30231030572808718350106151)
      ·
        refine ⟨45346545859213077525159227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30231030572808718350106151 45346545859213077525159227)
        ·
          refine ⟨68019818788819616287738841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45346545859213077525159227 68019818788819616287738841)
          ·
            refine ⟨51014864091614712215804131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68019818788819616287738841 51014864091614712215804131)
            ·
              refine ⟨76522296137422068323706197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51014864091614712215804131 76522296137422068323706197)
              ·
                refine ⟨56046603616275928948027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 76522296137422068323706197 56046603616275928948027)
                ·
                  rfl

theorem cell22_1473530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_1473530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473530 prefixEnd_1473530 := by exact prefixLift 1473530
  have htrace : WordTrace (prefixWord ++ tailWord_1473530) baseStart_1473530 baseEnd_1473530 := by
    simpa [prefixWord, tailWord_1473530, baseEnd_1473530] using wordTrace_append hprefix tailTrace_1473530
  have hstable : (prefixWord ++ tailWord_1473530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473530).length < 2 ^ (prefixWord ++ tailWord_1473530).sum := by decide
  have hdescent : baseEnd_1473530 < baseStart_1473530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473532 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1473532 : Nat := 118140960795 + 1473532 * 2 ^ 59
def prefixEnd_1473532 : Nat := 4983230072969 + 3 ^ 40 * 1473532 * 2
def baseEnd_1473532 : Nat := 504420117187356021982237

theorem tailTrace_1473532 : CollatzResearch.WordTrace tailWord_1473532 prefixEnd_1473532 504420117187356021982237 := by
  unfold tailWord_1473532
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872063648826349037547425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35829418198435132050063233 26872063648826349037547425)
  ·
    refine ⟨20154047736619761778160569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26872063648826349037547425 20154047736619761778160569)
    ·
      refine ⟨15115535802464821333620427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20154047736619761778160569 15115535802464821333620427)
      ·
        refine ⟨22673303703697232000430641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115535802464821333620427 22673303703697232000430641)
        ·
          refine ⟨17004977777772924000322981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22673303703697232000430641 17004977777772924000322981)
          ·
            refine ⟨3188433333332423250060559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17004977777772924000322981 3188433333332423250060559)
            ·
              refine ⟨4782649999998634875090839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188433333332423250060559 4782649999998634875090839)
              ·
                refine ⟨7173974999997952312636259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782649999998634875090839 7173974999997952312636259)
                ·
                  refine ⟨10760962499996928468954389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7173974999997952312636259 10760962499996928468954389)
                  ·
                    refine ⟨504420117187356021982237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10760962499996928468954389 504420117187356021982237)
                    ·
                      rfl

theorem cell22_1473532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1473532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473532 prefixEnd_1473532 := by exact prefixLift 1473532
  have htrace : WordTrace (prefixWord ++ tailWord_1473532) baseStart_1473532 baseEnd_1473532 := by
    simpa [prefixWord, tailWord_1473532, baseEnd_1473532] using wordTrace_append hprefix tailTrace_1473532
  have hstable : (prefixWord ++ tailWord_1473532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473532).length < 2 ^ (prefixWord ++ tailWord_1473532).sum := by decide
  have hdescent : baseEnd_1473532 < baseStart_1473532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473538 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1473538 : Nat := 118140960795 + 1473538 * 2 ^ 59
def prefixEnd_1473538 : Nat := 4983230072969 + 3 ^ 40 * 1473538 * 2
def baseEnd_1473538 : Nat := 504422171109974006332219

theorem tailTrace_1473538 : CollatzResearch.WordTrace tailWord_1473538 prefixEnd_1473538 504422171109974006332219 := by
  unfold tailWord_1473538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436086533907740274953317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35829564090420640733208845 13436086533907740274953317)
  ·
    refine ⟨2519266225107701301553747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13436086533907740274953317 2519266225107701301553747)
    ·
      refine ⟨3778899337661551952330621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519266225107701301553747 3778899337661551952330621)
      ·
        refine ⟨1417087251623081982123983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3778899337661551952330621 1417087251623081982123983)
        ·
          refine ⟨2125630877434622973185975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417087251623081982123983 2125630877434622973185975)
          ·
            refine ⟨3188446316151934459778963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125630877434622973185975 3188446316151934459778963)
            ·
              refine ⟨4782669474227901689668445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188446316151934459778963 4782669474227901689668445)
              ·
                refine ⟨1793501052835463133625667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4782669474227901689668445 1793501052835463133625667)
                ·
                  refine ⟨2690251579253194700438501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793501052835463133625667 2690251579253194700438501)
                  ·
                    refine ⟨504422171109974006332219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2690251579253194700438501 504422171109974006332219)
                    ·
                      rfl

theorem cell22_1473538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1473538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473538 prefixEnd_1473538 := by exact prefixLift 1473538
  have htrace : WordTrace (prefixWord ++ tailWord_1473538) baseStart_1473538 baseEnd_1473538 := by
    simpa [prefixWord, tailWord_1473538, baseEnd_1473538] using wordTrace_append hprefix tailTrace_1473538
  have hstable : (prefixWord ++ tailWord_1473538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473538).length < 2 ^ (prefixWord ++ tailWord_1473538).sum := by decide
  have hdescent : baseEnd_1473538 < baseStart_1473538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473545 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_1473545 : Nat := 118140960795 + 1473545 * 2 ^ 59
def prefixEnd_1473545 : Nat := 4983230072969 + 3 ^ 40 * 1473545 * 2
def baseEnd_1473545 : Nat := 504424567353028321407197

theorem tailTrace_1473545 : CollatzResearch.WordTrace tailWord_1473545 prefixEnd_1473545 504424567353028321407197 := by
  unfold tailWord_1473545
  simp only [CollatzResearch.WordTrace]
  refine ⟨53744601446605601295318089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35829734297737067530212059 53744601446605601295318089)
  ·
    refine ⟨40308451084954200971488567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53744601446605601295318089 40308451084954200971488567)
    ·
      refine ⟨60462676627431301457232851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40308451084954200971488567 60462676627431301457232851)
      ·
        refine ⟨90694014941146952185849277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60462676627431301457232851 90694014941146952185849277)
        ·
          refine ⟨34010255602930107069693479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90694014941146952185849277 34010255602930107069693479)
          ·
            refine ⟨51015383404395160604540219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34010255602930107069693479 51015383404395160604540219)
            ·
              refine ⟨76523075106592740906810329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51015383404395160604540219 76523075106592740906810329)
              ·
                refine ⟨57392306329944555680107747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76523075106592740906810329 57392306329944555680107747)
                ·
                  refine ⟨86088459494916833520161621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57392306329944555680107747 86088459494916833520161621)
                  ·
                    refine ⟨504424567353028321407197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86088459494916833520161621 504424567353028321407197)
                    ·
                      rfl

theorem cell22_1473545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_1473545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473545 prefixEnd_1473545 := by exact prefixLift 1473545
  have htrace : WordTrace (prefixWord ++ tailWord_1473545) baseStart_1473545 baseEnd_1473545 := by
    simpa [prefixWord, tailWord_1473545, baseEnd_1473545] using wordTrace_append hprefix tailTrace_1473545
  have hstable : (prefixWord ++ tailWord_1473545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473545).length < 2 ^ (prefixWord ++ tailWord_1473545).sum := by decide
  have hdescent : baseEnd_1473545 < baseStart_1473545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473568 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_1473568 : Nat := 118140960795 + 1473568 * 2 ^ 59
def prefixEnd_1473568 : Nat := 4983230072969 + 3 ^ 40 * 1473568 * 2
def baseEnd_1473568 : Nat := 504432440723063928082127

theorem tailTrace_1473568 : CollatzResearch.WordTrace tailWord_1473568 prefixEnd_1473568 504432440723063928082127 := by
  unfold tailWord_1473568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872720162761138111702679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35830293550348184148936905 26872720162761138111702679)
  ·
    refine ⟨40309080244141707167554019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872720162761138111702679 40309080244141707167554019)
    ·
      refine ⟨60463620366212560751331029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40309080244141707167554019 60463620366212560751331029)
      ·
        refine ⟨1417116102333106892609321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 60463620366212560751331029 1417116102333106892609321)
        ·
          refine ⟨1062837076749830169456991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1417116102333106892609321 1062837076749830169456991)
          ·
            refine ⟨1594255615124745254185487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062837076749830169456991 1594255615124745254185487)
            ·
              refine ⟨2391383422687117881278231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594255615124745254185487 2391383422687117881278231)
              ·
                refine ⟨3587075134030676821917347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391383422687117881278231 3587075134030676821917347)
                ·
                  refine ⟨5380612701046015232876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587075134030676821917347 5380612701046015232876021)
                  ·
                    refine ⟨504432440723063928082127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5380612701046015232876021 504432440723063928082127)
                    ·
                      rfl

theorem cell22_1473568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_1473568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473568 prefixEnd_1473568 := by exact prefixLift 1473568
  have htrace : WordTrace (prefixWord ++ tailWord_1473568) baseStart_1473568 baseEnd_1473568 := by
    simpa [prefixWord, tailWord_1473568, baseEnd_1473568] using wordTrace_append hprefix tailTrace_1473568
  have hstable : (prefixWord ++ tailWord_1473568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473568).length < 2 ^ (prefixWord ++ tailWord_1473568).sum := by decide
  have hdescent : baseEnd_1473568 < baseStart_1473568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473592 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_1473592 : Nat := 118140960795 + 1473592 * 2 ^ 59
def prefixEnd_1473592 : Nat := 4983230072969 + 3 ^ 40 * 1473592 * 2
def baseEnd_1473592 : Nat := 168146885471178621827351

theorem tailTrace_1473592 : CollatzResearch.WordTrace tailWord_1473592 prefixEnd_1473592 168146885471178621827351 := by
  unfold tailWord_1473592
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873157838717664161139515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35830877118290218881519353 26873157838717664161139515)
  ·
    refine ⟨40309736758076496241709273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26873157838717664161139515 40309736758076496241709273)
    ·
      refine ⟨30232302568557372181281955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40309736758076496241709273 30232302568557372181281955)
      ·
        refine ⟨45348453852836058271922933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30232302568557372181281955 45348453852836058271922933)
        ·
          refine ⟨4251417548703380462992775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45348453852836058271922933 4251417548703380462992775)
          ·
            refine ⟨6377126323055070694489163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251417548703380462992775 6377126323055070694489163)
            ·
              refine ⟨9565689484582606041733745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377126323055070694489163 9565689484582606041733745)
              ·
                refine ⟨7174267113436954531300309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565689484582606041733745 7174267113436954531300309)
                ·
                  refine ⟨168146885471178621827351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7174267113436954531300309 168146885471178621827351)
                  ·
                    rfl

theorem cell22_1473592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_1473592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473592 prefixEnd_1473592 := by exact prefixLift 1473592
  have htrace : WordTrace (prefixWord ++ tailWord_1473592) baseStart_1473592 baseEnd_1473592 := by
    simpa [prefixWord, tailWord_1473592, baseEnd_1473592] using wordTrace_append hprefix tailTrace_1473592
  have hstable : (prefixWord ++ tailWord_1473592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473592).length < 2 ^ (prefixWord ++ tailWord_1473592).sum := by decide
  have hdescent : baseEnd_1473592 < baseStart_1473592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473613 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1473613 : Nat := 118140960795 + 1473613 * 2 ^ 59
def prefixEnd_1473613 : Nat := 4983230072969 + 3 ^ 40 * 1473613 * 2
def baseEnd_1473613 : Nat := 504447845142698810706989

theorem tailTrace_1473613 : CollatzResearch.WordTrace tailWord_1473613 prefixEnd_1473613 504447845142698810706989 := by
  unfold tailWord_1473613
  simp only [CollatzResearch.WordTrace]
  refine ⟨53747081610359248908793493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35831387740239499272528995 53747081610359248908793493)
  ·
    refine ⟨2519394450485589792599695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53747081610359248908793493 2519394450485589792599695)
    ·
      refine ⟨3779091675728384688899543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519394450485589792599695 3779091675728384688899543)
      ·
        refine ⟨5668637513592577033349315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779091675728384688899543 5668637513592577033349315)
        ·
          refine ⟨8502956270388865550023973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668637513592577033349315 8502956270388865550023973)
          ·
            refine ⟨1594304300697912290629495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8502956270388865550023973 1594304300697912290629495)
            ·
              refine ⟨2391456451046868435944243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594304300697912290629495 2391456451046868435944243)
              ·
                refine ⟨3587184676570302653916365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391456451046868435944243 3587184676570302653916365)
                ·
                  refine ⟨1345194253713863495218637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3587184676570302653916365 1345194253713863495218637)
                  ·
                    refine ⟨504447845142698810706989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345194253713863495218637 504447845142698810706989)
                    ·
                      rfl

theorem cell22_1473613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1473613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473613 prefixEnd_1473613 := by exact prefixLift 1473613
  have htrace : WordTrace (prefixWord ++ tailWord_1473613) baseStart_1473613 baseEnd_1473613 := by
    simpa [prefixWord, tailWord_1473613, baseEnd_1473613] using wordTrace_append hprefix tailTrace_1473613
  have hstable : (prefixWord ++ tailWord_1473613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473613).length < 2 ^ (prefixWord ++ tailWord_1473613).sum := by decide
  have hdescent : baseEnd_1473613 < baseStart_1473613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473637 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1473637 : Nat := 118140960795 + 1473637 * 2 ^ 59
def prefixEnd_1473637 : Nat := 4983230072969 + 3 ^ 40 * 1473637 * 2
def baseEnd_1473637 : Nat := 168152020277723582702305

theorem tailTrace_1473637 : CollatzResearch.WordTrace tailWord_1473637 prefixEnd_1473637 168152020277723582702305 := by
  unfold tailWord_1473637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53747956962272301007667165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35831971308181534005111443 53747956962272301007667165)
  ·
    refine ⟨20155483860852112877875187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53747956962272301007667165 20155483860852112877875187)
    ·
      refine ⟨30233225791278169316812781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20155483860852112877875187 30233225791278169316812781)
      ·
        refine ⟨11337459671729313493804793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30233225791278169316812781 11337459671729313493804793)
        ·
          refine ⟨8503094753796985120353595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337459671729313493804793 8503094753796985120353595)
          ·
            refine ⟨12754642130695477680530393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503094753796985120353595 12754642130695477680530393)
            ·
              refine ⟨9565981598021608260397795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12754642130695477680530393 9565981598021608260397795)
              ·
                refine ⟨14348972397032412390596693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9565981598021608260397795 14348972397032412390596693)
                ·
                  refine ⟨168152020277723582702305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14348972397032412390596693 168152020277723582702305)
                  ·
                    rfl

theorem cell22_1473637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1473637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473637 prefixEnd_1473637 := by exact prefixLift 1473637
  have htrace : WordTrace (prefixWord ++ tailWord_1473637) baseStart_1473637 baseEnd_1473637 := by
    simpa [prefixWord, tailWord_1473637, baseEnd_1473637] using wordTrace_append hprefix tailTrace_1473637
  have hstable : (prefixWord ++ tailWord_1473637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473637).length < 2 ^ (prefixWord ++ tailWord_1473637).sum := by decide
  have hdescent : baseEnd_1473637 < baseStart_1473637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473639 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1473639 : Nat := 118140960795 + 1473639 * 2 ^ 59
def prefixEnd_1473639 : Nat := 4983230072969 + 3 ^ 40 * 1473639 * 2
def baseEnd_1473639 : Nat := 504456745474043409556909

theorem tailTrace_1473639 : CollatzResearch.WordTrace tailWord_1473639 prefixEnd_1473639 504456745474043409556909 := by
  unfold tailWord_1473639
  simp only [CollatzResearch.WordTrace]
  refine ⟨53748029908265055349239971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35832019938843370232826647 53748029908265055349239971)
  ·
    refine ⟨80622044862397583023859957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53748029908265055349239971 80622044862397583023859957)
    ·
      refine ⟨7558316705849773408486871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80622044862397583023859957 7558316705849773408486871)
      ·
        refine ⟨11337475058774660112730307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558316705849773408486871 11337475058774660112730307)
        ·
          refine ⟨17006212588161990169095461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11337475058774660112730307 17006212588161990169095461)
          ·
            refine ⟨3188664860280373156705399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17006212588161990169095461 3188664860280373156705399)
            ·
              refine ⟨4782997290420559735058099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188664860280373156705399 4782997290420559735058099)
              ·
                refine ⟨7174495935630839602587149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782997290420559735058099 7174495935630839602587149)
                ·
                  refine ⟨2690435975861564850970181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7174495935630839602587149 2690435975861564850970181)
                  ·
                    refine ⟨504456745474043409556909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2690435975861564850970181 504456745474043409556909)
                    ·
                      rfl

theorem cell22_1473639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1473639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473639 prefixEnd_1473639 := by exact prefixLift 1473639
  have htrace : WordTrace (prefixWord ++ tailWord_1473639) baseStart_1473639 baseEnd_1473639 := by
    simpa [prefixWord, tailWord_1473639, baseEnd_1473639] using wordTrace_append hprefix tailTrace_1473639
  have hstable : (prefixWord ++ tailWord_1473639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473639).length < 2 ^ (prefixWord ++ tailWord_1473639).sum := by decide
  have hdescent : baseEnd_1473639 < baseStart_1473639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473701 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_1473701 : Nat := 118140960795 + 1473701 * 2 ^ 59
def prefixEnd_1473701 : Nat := 4983230072969 + 3 ^ 40 * 1473701 * 2
def baseEnd_1473701 : Nat := 504477969341095914506719

theorem tailTrace_1473701 : CollatzResearch.WordTrace tailWord_1473701 prefixEnd_1473701 504477969341095914506719 := by
  unfold tailWord_1473701
  simp only [CollatzResearch.WordTrace]
  refine ⟨53750291234040439937996957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35833527489360293291997971 53750291234040439937996957)
  ·
    refine ⟨20156359212765164976748859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53750291234040439937996957 20156359212765164976748859)
    ·
      refine ⟨30234538819147747465123289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20156359212765164976748859 30234538819147747465123289)
      ·
        refine ⟨22675904114360810598842467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30234538819147747465123289 22675904114360810598842467)
        ·
          refine ⟨34013856171541215898263701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22675904114360810598842467 34013856171541215898263701)
          ·
            refine ⟨1594399508040994495231111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34013856171541215898263701 1594399508040994495231111)
            ·
              refine ⟨2391599262061491742846667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594399508040994495231111 2391599262061491742846667)
              ·
                refine ⟨3587398893092237614270001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391599262061491742846667 3587398893092237614270001)
                ·
                  refine ⟨2690549169819178210702501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3587398893092237614270001 2690549169819178210702501)
                  ·
                    refine ⟨504477969341095914506719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2690549169819178210702501 504477969341095914506719)
                    ·
                      rfl

theorem cell22_1473701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_1473701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473701 prefixEnd_1473701 := by exact prefixLift 1473701
  have htrace : WordTrace (prefixWord ++ tailWord_1473701) baseStart_1473701 baseEnd_1473701 := by
    simpa [prefixWord, tailWord_1473701, baseEnd_1473701] using wordTrace_append hprefix tailTrace_1473701
  have hstable : (prefixWord ++ tailWord_1473701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473701).length < 2 ^ (prefixWord ++ tailWord_1473701).sum := by decide
  have hdescent : baseEnd_1473701 < baseStart_1473701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473712 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_1473712 : Nat := 118140960795 + 1473712 * 2 ^ 59
def prefixEnd_1473712 : Nat := 4983230072969 + 3 ^ 40 * 1473712 * 2
def baseEnd_1473712 : Nat := 504481734865895552481685

theorem tailTrace_1473712 : CollatzResearch.WordTrace tailWord_1473712 prefixEnd_1473712 504481734865895552481685 := by
  unfold tailWord_1473712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26875346218500294408323695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35833794958000392544431593 26875346218500294408323695)
  ·
    refine ⟨40313019327750441612485543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26875346218500294408323695 40313019327750441612485543)
    ·
      refine ⟨60469528991625662418728315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40313019327750441612485543 60469528991625662418728315)
      ·
        refine ⟨90704293487438493628092473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60469528991625662418728315 90704293487438493628092473)
        ·
          refine ⟨68028220115578870221069355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90704293487438493628092473 68028220115578870221069355)
          ·
            refine ⟨102042330173368305331604033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68028220115578870221069355 102042330173368305331604033)
            ·
              refine ⟨76531747630026228998703025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102042330173368305331604033 76531747630026228998703025)
              ·
                refine ⟨57398810722519671749027269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76531747630026228998703025 57398810722519671749027269)
                ·
                  refine ⟨10762277010472438452942613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57398810722519671749027269 10762277010472438452942613)
                  ·
                    refine ⟨504481734865895552481685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10762277010472438452942613 504481734865895552481685)
                    ·
                      rfl

theorem cell22_1473712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_1473712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473712 prefixEnd_1473712 := by exact prefixLift 1473712
  have htrace : WordTrace (prefixWord ++ tailWord_1473712) baseStart_1473712 baseEnd_1473712 := by
    simpa [prefixWord, tailWord_1473712, baseEnd_1473712] using wordTrace_append hprefix tailTrace_1473712
  have hstable : (prefixWord ++ tailWord_1473712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473712).length < 2 ^ (prefixWord ++ tailWord_1473712).sum := by decide
  have hdescent : baseEnd_1473712 < baseStart_1473712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473750 : List Nat := [5, 2, 1, 2, 2, 2, 2, 6]
def baseStart_1473750 : Nat := 118140960795 + 1473750 * 2 ^ 59
def prefixEnd_1473750 : Nat := 4983230072969 + 3 ^ 40 * 1473750 * 2
def baseEnd_1473750 : Nat := 56054971449164013336841

theorem tailTrace_1473750 : CollatzResearch.WordTrace tailWord_1473750 prefixEnd_1473750 56054971449164013336841 := by
  unfold tailWord_1473750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359504900678932581658169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35834718940575280871020469 3359504900678932581658169)
  ·
    refine ⟨2519628675509199436243627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3359504900678932581658169 2519628675509199436243627)
    ·
      refine ⟨3779443013263799154365441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519628675509199436243627 3779443013263799154365441)
      ·
        refine ⟨2834582259947849365774081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779443013263799154365441 2834582259947849365774081)
        ·
          refine ⟨2125936694960887024330561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834582259947849365774081 2125936694960887024330561)
          ·
            refine ⟨1594452521220665268247921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125936694960887024330561 1594452521220665268247921)
            ·
              refine ⟨1195839390915498951185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594452521220665268247921 1195839390915498951185941)
              ·
                refine ⟨56054971449164013336841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1195839390915498951185941 56054971449164013336841)
                ·
                  rfl

theorem cell22_1473750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_1473750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473750 prefixEnd_1473750 := by exact prefixLift 1473750
  have htrace : WordTrace (prefixWord ++ tailWord_1473750) baseStart_1473750 baseEnd_1473750 := by
    simpa [prefixWord, tailWord_1473750, baseEnd_1473750] using wordTrace_append hprefix tailTrace_1473750
  have hstable : (prefixWord ++ tailWord_1473750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473750).length < 2 ^ (prefixWord ++ tailWord_1473750).sum := by decide
  have hdescent : baseEnd_1473750 < baseStart_1473750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473821 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1473821 : Nat := 118140960795 + 1473821 * 2 ^ 59
def prefixEnd_1473821 : Nat := 4983230072969 + 3 ^ 40 * 1473821 * 2
def baseEnd_1473821 : Nat := 504519047793455601506351

theorem tailTrace_1473821 : CollatzResearch.WordTrace tailWord_1473821 prefixEnd_1473821 504519047793455601506351 := by
  unfold tailWord_1473821
  simp only [CollatzResearch.WordTrace]
  refine ⟨53754667993605700432365317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35836445329070466954910211 53754667993605700432365317)
  ·
    refine ⟨10079000248801068831068497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53754667993605700432365317 10079000248801068831068497)
    ·
      refine ⟨7559250186600801623301373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10079000248801068831068497 7559250186600801623301373)
      ·
        refine ⟨2834718819975300608738015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7559250186600801623301373 2834718819975300608738015)
        ·
          refine ⟨4252078229962950913107023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834718819975300608738015 4252078229962950913107023)
          ·
            refine ⟨6378117344944426369660535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252078229962950913107023 6378117344944426369660535)
            ·
              refine ⟨9567176017416639554490803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378117344944426369660535 9567176017416639554490803)
              ·
                refine ⟨14350764026124959331736205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567176017416639554490803 14350764026124959331736205)
                ·
                  refine ⟨5381536509796859749401077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14350764026124959331736205 5381536509796859749401077)
                  ·
                    refine ⟨504519047793455601506351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5381536509796859749401077 504519047793455601506351)
                    ·
                      rfl

theorem cell22_1473821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1473821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473821 prefixEnd_1473821 := by exact prefixLift 1473821
  have htrace : WordTrace (prefixWord ++ tailWord_1473821) baseStart_1473821 baseEnd_1473821 := by
    simpa [prefixWord, tailWord_1473821, baseEnd_1473821] using wordTrace_append hprefix tailTrace_1473821
  have hstable : (prefixWord ++ tailWord_1473821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473821).length < 2 ^ (prefixWord ++ tailWord_1473821).sum := by decide
  have hdescent : baseEnd_1473821 < baseStart_1473821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473864 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1473864 : Nat := 118140960795 + 1473864 * 2 ^ 59
def prefixEnd_1473864 : Nat := 4983230072969 + 3 ^ 40 * 1473864 * 2
def baseEnd_1473864 : Nat := 504533767572217822681219

theorem tailTrace_1473864 : CollatzResearch.WordTrace tailWord_1473864 prefixEnd_1473864 504533767572217822681219 := by
  unfold tailWord_1473864
  simp only [CollatzResearch.WordTrace]
  refine ⟨26878118166224959388090323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35837490888299945850787097 26878118166224959388090323)
  ·
    refine ⟨40317177249337439082135485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26878118166224959388090323 40317177249337439082135485)
    ·
      refine ⟨15118941468501539655800807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40317177249337439082135485 15118941468501539655800807)
      ·
        refine ⟨22678412202752309483701211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118941468501539655800807 22678412202752309483701211)
        ·
          refine ⟨34017618304128464225551817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22678412202752309483701211 34017618304128464225551817)
          ·
            refine ⟨25513213728096348169163863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34017618304128464225551817 25513213728096348169163863)
            ·
              refine ⟨38269820592144522253745795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25513213728096348169163863 38269820592144522253745795)
              ·
                refine ⟨57404730888216783380618693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38269820592144522253745795 57404730888216783380618693)
                ·
                  refine ⟨10763387041540646883866005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57404730888216783380618693 10763387041540646883866005)
                  ·
                    refine ⟨504533767572217822681219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10763387041540646883866005 504533767572217822681219)
                    ·
                      rfl

theorem cell22_1473864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1473864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473864 prefixEnd_1473864 := by exact prefixLift 1473864
  have htrace : WordTrace (prefixWord ++ tailWord_1473864) baseStart_1473864 baseEnd_1473864 := by
    simpa [prefixWord, tailWord_1473864, baseEnd_1473864] using wordTrace_append hprefix tailTrace_1473864
  have hstable : (prefixWord ++ tailWord_1473864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473864).length < 2 ^ (prefixWord ++ tailWord_1473864).sum := by decide
  have hdescent : baseEnd_1473864 < baseStart_1473864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473885 : List Nat := [1, 4, 5, 1, 1, 1, 9]
def baseStart_1473885 : Nat := 118140960795 + 1473885 * 2 ^ 59
def prefixEnd_1473885 : Nat := 4983230072969 + 3 ^ 40 * 1473885 * 2
def baseEnd_1473885 : Nat := 18686702085236324737265

theorem tailTrace_1473885 : CollatzResearch.WordTrace tailWord_1473885 prefixEnd_1473885 18686702085236324737265 := by
  unfold tailWord_1473885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757002265373839362695109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35838001510249226241796739 53757002265373839362695109)
  ·
    refine ⟨10079437924757594880505333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53757002265373839362695109 10079437924757594880505333)
    ·
      refine ⟨944947305446024520047375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10079437924757594880505333 944947305446024520047375)
      ·
        refine ⟨1417420958169036780071063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944947305446024520047375 1417420958169036780071063)
        ·
          refine ⟨2126131437253555170106595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417420958169036780071063 2126131437253555170106595)
          ·
            refine ⟨3189197155880332755159893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126131437253555170106595 3189197155880332755159893)
            ·
              refine ⟨18686702085236324737265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3189197155880332755159893 18686702085236324737265)
              ·
                rfl

theorem cell22_1473885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 9].length) (baseStart_1473885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473885 prefixEnd_1473885 := by exact prefixLift 1473885
  have htrace : WordTrace (prefixWord ++ tailWord_1473885) baseStart_1473885 baseEnd_1473885 := by
    simpa [prefixWord, tailWord_1473885, baseEnd_1473885] using wordTrace_append hprefix tailTrace_1473885
  have hstable : (prefixWord ++ tailWord_1473885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473885).length < 2 ^ (prefixWord ++ tailWord_1473885).sum := by decide
  have hdescent : baseEnd_1473885 < baseStart_1473885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473900 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_1473900 : Nat := 118140960795 + 1473900 * 2 ^ 59
def prefixEnd_1473900 : Nat := 4983230072969 + 3 ^ 40 * 1473900 * 2
def baseEnd_1473900 : Nat := 504546091107925728781109

theorem tailTrace_1473900 : CollatzResearch.WordTrace tailWord_1473900 prefixEnd_1473900 504546091107925728781109 := by
  unfold tailWord_1473900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26878774680159748462245577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35838366240212997949660769 26878774680159748462245577)
  ·
    refine ⟨20159081010119811346684183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26878774680159748462245577 20159081010119811346684183)
    ·
      refine ⟨30238621515179717020026275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20159081010119811346684183 30238621515179717020026275)
      ·
        refine ⟨45357932272769575530039413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30238621515179717020026275 45357932272769575530039413)
        ·
          refine ⟨4252306150572147705941195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45357932272769575530039413 4252306150572147705941195)
          ·
            refine ⟨6378459225858221558911793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252306150572147705941195 6378459225858221558911793)
            ·
              refine ⟨4783844419393666169183845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6378459225858221558911793 4783844419393666169183845)
              ·
                refine ⟨896970828636312406721971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4783844419393666169183845 896970828636312406721971)
                ·
                  refine ⟨1345456242954468610082957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896970828636312406721971 1345456242954468610082957)
                  ·
                    refine ⟨504546091107925728781109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345456242954468610082957 504546091107925728781109)
                    ·
                      rfl

theorem cell22_1473900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_1473900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473900 prefixEnd_1473900 := by exact prefixLift 1473900
  have htrace : WordTrace (prefixWord ++ tailWord_1473900) baseStart_1473900 baseEnd_1473900 := by
    simpa [prefixWord, tailWord_1473900, baseEnd_1473900] using wordTrace_append hprefix tailTrace_1473900
  have hstable : (prefixWord ++ tailWord_1473900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473900).length < 2 ^ (prefixWord ++ tailWord_1473900).sum := by decide
  have hdescent : baseEnd_1473900 < baseStart_1473900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473934 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1473934 : Nat := 118140960795 + 1473934 * 2 ^ 59
def prefixEnd_1473934 : Nat := 4983230072969 + 3 ^ 40 * 1473934 * 2
def baseEnd_1473934 : Nat := 504557730002760973431005

theorem tailTrace_1473934 : CollatzResearch.WordTrace tailWord_1473934 prefixEnd_1473934 504557730002760973431005 := by
  unfold tailWord_1473934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719848680274540091403607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35839192961464213820819237 6719848680274540091403607)
  ·
    refine ⟨10079773020411810137105411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6719848680274540091403607 10079773020411810137105411)
    ·
      refine ⟨15119659530617715205658117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10079773020411810137105411 15119659530617715205658117)
      ·
        refine ⟨2834936161990821601060897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15119659530617715205658117 2834936161990821601060897)
        ·
          refine ⟨2126202121493116200795673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834936161990821601060897 2126202121493116200795673)
          ·
            refine ⟨1594651591119837150596755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2126202121493116200795673 1594651591119837150596755)
            ·
              refine ⟨2391977386679755725895133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594651591119837150596755 2391977386679755725895133)
              ·
                refine ⟨896991520004908397210675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2391977386679755725895133 896991520004908397210675)
                ·
                  refine ⟨1345487280007362595816013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896991520004908397210675 1345487280007362595816013)
                  ·
                    refine ⟨504557730002760973431005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345487280007362595816013 504557730002760973431005)
                    ·
                      rfl

theorem cell22_1473934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1473934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473934 prefixEnd_1473934 := by exact prefixLift 1473934
  have htrace : WordTrace (prefixWord ++ tailWord_1473934) baseStart_1473934 baseEnd_1473934 := by
    simpa [prefixWord, tailWord_1473934, baseEnd_1473934] using wordTrace_append hprefix tailTrace_1473934
  have hstable : (prefixWord ++ tailWord_1473934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473934).length < 2 ^ (prefixWord ++ tailWord_1473934).sum := by decide
  have hdescent : baseEnd_1473934 < baseStart_1473934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473977 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_1473977 : Nat := 118140960795 + 1473977 * 2 ^ 59
def prefixEnd_1473977 : Nat := 4983230072969 + 3 ^ 40 * 1473977 * 2
def baseEnd_1473977 : Nat := 504572449781523194605873

theorem tailTrace_1473977 : CollatzResearch.WordTrace tailWord_1473977 prefixEnd_1473977 504572449781523194605873 := by
  unfold tailWord_1473977
  simp only [CollatzResearch.WordTrace]
  refine ⟨53760357781040539075044185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35840238520693692716696123 53760357781040539075044185)
  ·
    refine ⟨40320268335780404306283139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53760357781040539075044185 40320268335780404306283139)
    ·
      refine ⟨60480402503670606459424709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40320268335780404306283139 60480402503670606459424709)
      ·
        refine ⟨11340075469438238711142133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60480402503670606459424709 11340075469438238711142133)
        ·
          refine ⟨1063132075259834879169575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11340075469438238711142133 1063132075259834879169575)
          ·
            refine ⟨1594698112889752318754363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063132075259834879169575 1594698112889752318754363)
            ·
              refine ⟨2392047169334628478131545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594698112889752318754363 2392047169334628478131545)
              ·
                refine ⟨1794035377000971358598659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392047169334628478131545 1794035377000971358598659)
                ·
                  refine ⟨2691053065501457037897989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794035377000971358598659 2691053065501457037897989)
                  ·
                    refine ⟨504572449781523194605873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691053065501457037897989 504572449781523194605873)
                    ·
                      rfl

theorem cell22_1473977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_1473977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1473977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1473977 prefixEnd_1473977 := by exact prefixLift 1473977
  have htrace : WordTrace (prefixWord ++ tailWord_1473977) baseStart_1473977 baseEnd_1473977 := by
    simpa [prefixWord, tailWord_1473977, baseEnd_1473977] using wordTrace_append hprefix tailTrace_1473977
  have hstable : (prefixWord ++ tailWord_1473977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473977).length < 2 ^ (prefixWord ++ tailWord_1473977).sum := by decide
  have hdescent : baseEnd_1473977 < baseStart_1473977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474157 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1474157 : Nat := 118140960795 + 1474157 * 2 ^ 59
def prefixEnd_1474157 : Nat := 4983230072969 + 3 ^ 40 * 1474157 * 2
def baseEnd_1474157 : Nat := 504634067460062725105321

theorem tailTrace_1474157 : CollatzResearch.WordTrace tailWord_1474157 prefixEnd_1474157 504634067460062725105321 := by
  unfold tailWord_1474157
  simp only [CollatzResearch.WordTrace]
  refine ⟨53766922920388429816596725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35844615280258953211064483 53766922920388429816596725)
  ·
    refine ⟨5040649023786415295305943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53766922920388429816596725 5040649023786415295305943)
    ·
      refine ⟨7560973535679622942958915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040649023786415295305943 7560973535679622942958915)
      ·
        refine ⟨11341460303519434414438373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560973535679622942958915 11341460303519434414438373)
        ·
          refine ⟨2126523806909893952707195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11341460303519434414438373 2126523806909893952707195)
          ·
            refine ⟨3189785710364840929060793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126523806909893952707195 3189785710364840929060793)
            ·
              refine ⟨2392339282773630696795595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189785710364840929060793 2392339282773630696795595)
              ·
                refine ⟨3588508924160446045193393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392339282773630696795595 3588508924160446045193393)
                ·
                  refine ⟨2691381693120334533895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588508924160446045193393 2691381693120334533895045)
                  ·
                    refine ⟨504634067460062725105321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691381693120334533895045 504634067460062725105321)
                    ·
                      rfl

theorem cell22_1474157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1474157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474157 prefixEnd_1474157 := by exact prefixLift 1474157
  have htrace : WordTrace (prefixWord ++ tailWord_1474157) baseStart_1474157 baseEnd_1474157 := by
    simpa [prefixWord, tailWord_1474157, baseEnd_1474157] using wordTrace_append hprefix tailTrace_1474157
  have hstable : (prefixWord ++ tailWord_1474157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474157).length < 2 ^ (prefixWord ++ tailWord_1474157).sum := by decide
  have hdescent : baseEnd_1474157 < baseStart_1474157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474187 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 1, 3]
def baseStart_1474187 : Nat := 118140960795 + 1474187 * 2 ^ 59
def prefixEnd_1474187 : Nat := 4983230072969 + 3 ^ 40 * 1474187 * 2
def baseEnd_1474187 : Nat := 504644337073152646855229

theorem tailTrace_1474187 : CollatzResearch.WordTrace tailWord_1474187 prefixEnd_1474187 504644337073152646855229 := by
  unfold tailWord_1474187
  simp only [CollatzResearch.WordTrace]
  refine ⟨53768017110279744940188815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35845344740186496626792543 53768017110279744940188815)
  ·
    refine ⟨80652025665419617410283223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53768017110279744940188815 80652025665419617410283223)
    ·
      refine ⟨120978038498129426115424835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80652025665419617410283223 120978038498129426115424835)
      ·
        refine ⟨181467057747194139173137253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120978038498129426115424835 181467057747194139173137253)
        ·
          refine ⟨34025073327598901094963235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181467057747194139173137253 34025073327598901094963235)
          ·
            refine ⟨51037609991398351642444853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34025073327598901094963235 51037609991398351642444853)
            ·
              refine ⟨4784775936693595466479205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51037609991398351642444853 4784775936693595466479205)
              ·
                refine ⟨897145488130049149964851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4784775936693595466479205 897145488130049149964851)
                ·
                  refine ⟨1345718232195073724947277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897145488130049149964851 1345718232195073724947277)
                  ·
                    refine ⟨504644337073152646855229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345718232195073724947277 504644337073152646855229)
                    ·
                      rfl

theorem cell22_1474187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 3].length) (baseStart_1474187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474187 prefixEnd_1474187 := by exact prefixLift 1474187
  have htrace : WordTrace (prefixWord ++ tailWord_1474187) baseStart_1474187 baseEnd_1474187 := by
    simpa [prefixWord, tailWord_1474187, baseEnd_1474187] using wordTrace_append hprefix tailTrace_1474187
  have hstable : (prefixWord ++ tailWord_1474187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474187).length < 2 ^ (prefixWord ++ tailWord_1474187).sum := by decide
  have hdescent : baseEnd_1474187 < baseStart_1474187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474200 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_1474200 : Nat := 118140960795 + 1474200 * 2 ^ 59
def prefixEnd_1474200 : Nat := 4983230072969 + 3 ^ 40 * 1474200 * 2
def baseEnd_1474200 : Nat := 168216262412941648760063

theorem tailTrace_1474200 : CollatzResearch.WordTrace tailWord_1474200 prefixEnd_1474200 168216262412941648760063 := by
  unfold tailWord_1474200
  simp only [CollatzResearch.WordTrace]
  refine ⟨26884245629616324080206027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35845660839488432106941369 26884245629616324080206027)
  ·
    refine ⟨40326368444424486120309041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26884245629616324080206027 40326368444424486120309041)
    ·
      refine ⟨30244776333318364590231781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40326368444424486120309041 30244776333318364590231781)
      ·
        refine ⟨5670895562497193360668459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30244776333318364590231781 5670895562497193360668459)
        ·
          refine ⟨8506343343745790041002689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670895562497193360668459 8506343343745790041002689)
          ·
            refine ⟨6379757507809342530752017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8506343343745790041002689 6379757507809342530752017)
            ·
              refine ⟨4784818130857006898064013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379757507809342530752017 4784818130857006898064013)
              ·
                refine ⟨1794306799071377586774005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4784818130857006898064013 1794306799071377586774005)
                ·
                  refine ⟨168216262412941648760063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1794306799071377586774005 168216262412941648760063)
                  ·
                    rfl

theorem cell22_1474200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_1474200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474200 prefixEnd_1474200 := by exact prefixLift 1474200
  have htrace : WordTrace (prefixWord ++ tailWord_1474200) baseStart_1474200 baseEnd_1474200 := by
    simpa [prefixWord, tailWord_1474200, baseEnd_1474200] using wordTrace_append hprefix tailTrace_1474200
  have hstable : (prefixWord ++ tailWord_1474200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474200).length < 2 ^ (prefixWord ++ tailWord_1474200).sum := by decide
  have hdescent : baseEnd_1474200 < baseStart_1474200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474367 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_1474367 : Nat := 118140960795 + 1474367 * 2 ^ 59
def prefixEnd_1474367 : Nat := 4983230072969 + 3 ^ 40 * 1474367 * 2
def baseEnd_1474367 : Nat := 504705954751692177354677

theorem tailTrace_1474367 : CollatzResearch.WordTrace tailWord_1474367 prefixEnd_1474367 504705954751692177354677 := by
  unfold tailWord_1474367
  simp only [CollatzResearch.WordTrace]
  refine ⟨53774582249627635681741355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35849721499751757121160903 53774582249627635681741355)
  ·
    refine ⟨80661873374441453522612033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53774582249627635681741355 80661873374441453522612033)
    ·
      refine ⟨60496405030831090141959025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80661873374441453522612033 60496405030831090141959025)
      ·
        refine ⟨45372303773123317606469269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60496405030831090141959025 45372303773123317606469269)
        ·
          refine ⟨2126826739365155512803247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45372303773123317606469269 2126826739365155512803247)
          ·
            refine ⟨3190240109047733269204871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126826739365155512803247 3190240109047733269204871)
            ·
              refine ⟨4785360163571599903807307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190240109047733269204871 4785360163571599903807307)
              ·
                refine ⟨7178040245357399855710961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785360163571599903807307 7178040245357399855710961)
                ·
                  refine ⟨5383530184018049891783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178040245357399855710961 5383530184018049891783221)
                  ·
                    refine ⟨504705954751692177354677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5383530184018049891783221 504705954751692177354677)
                    ·
                      rfl

theorem cell22_1474367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_1474367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474367 prefixEnd_1474367 := by exact prefixLift 1474367
  have htrace : WordTrace (prefixWord ++ tailWord_1474367) baseStart_1474367 baseEnd_1474367 := by
    simpa [prefixWord, tailWord_1474367, baseEnd_1474367] using wordTrace_append hprefix tailTrace_1474367
  have hstable : (prefixWord ++ tailWord_1474367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474367).length < 2 ^ (prefixWord ++ tailWord_1474367).sum := by decide
  have hdescent : baseEnd_1474367 < baseStart_1474367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474399 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 1, 4]
def baseStart_1474399 : Nat := 118140960795 + 1474399 * 2 ^ 59
def prefixEnd_1474399 : Nat := 4983230072969 + 3 ^ 40 * 1474399 * 2
def baseEnd_1474399 : Nat := 504716909005654760554579

theorem tailTrace_1474399 : CollatzResearch.WordTrace tailWord_1474399 prefixEnd_1474399 504716909005654760554579 := by
  unfold tailWord_1474399
  simp only [CollatzResearch.WordTrace]
  refine ⟨53775749385511705146906251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35850499590341136764604167 53775749385511705146906251)
  ·
    refine ⟨80663624078267557720359377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53775749385511705146906251 80663624078267557720359377)
    ·
      refine ⟨60497718058700668290269533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80663624078267557720359377 60497718058700668290269533)
      ·
        refine ⟨22686644272012750608851075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60497718058700668290269533 22686644272012750608851075)
        ·
          refine ⟨34029966408019125913276613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22686644272012750608851075 34029966408019125913276613)
          ·
            refine ⟨6380618701503586108739365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34029966408019125913276613 6380618701503586108739365)
            ·
              refine ⟨1196366006531922395388631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6380618701503586108739365 1196366006531922395388631)
              ·
                refine ⟨1794549009797883593082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196366006531922395388631 1794549009797883593082947)
                ·
                  refine ⟨2691823514696825389624421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794549009797883593082947 2691823514696825389624421)
                  ·
                    refine ⟨504716909005654760554579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691823514696825389624421 504716909005654760554579)
                    ·
                      rfl

theorem cell22_1474399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_1474399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474399 prefixEnd_1474399 := by exact prefixLift 1474399
  have htrace : WordTrace (prefixWord ++ tailWord_1474399) baseStart_1474399 baseEnd_1474399 := by
    simpa [prefixWord, tailWord_1474399, baseEnd_1474399] using wordTrace_append hprefix tailTrace_1474399
  have hstable : (prefixWord ++ tailWord_1474399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474399).length < 2 ^ (prefixWord ++ tailWord_1474399).sum := by decide
  have hdescent : baseEnd_1474399 < baseStart_1474399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474414 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1474414 : Nat := 118140960795 + 1474414 * 2 ^ 59
def prefixEnd_1474414 : Nat := 4983230072969 + 3 ^ 40 * 1474414 * 2
def baseEnd_1474414 : Nat := 168240681270733240476511

theorem tailTrace_1474414 : CollatzResearch.WordTrace tailWord_1474414 prefixEnd_1474414 168240681270733240476511 := by
  unfold tailWord_1474414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722037060057170338587787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35850864320304908472468197 6722037060057170338587787)
  ·
    refine ⟨10083055590085755507881681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6722037060057170338587787 10083055590085755507881681)
    ·
      refine ⟨7562291692564316630911261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10083055590085755507881681 7562291692564316630911261)
      ·
        refine ⟨2835859384711618736591723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7562291692564316630911261 2835859384711618736591723)
        ·
          refine ⟨4253789077067428104887585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835859384711618736591723 4253789077067428104887585)
          ·
            refine ⟨3190341807800571078665689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4253789077067428104887585 3190341807800571078665689)
            ·
              refine ⟨2392756355850428308999267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190341807800571078665689 2392756355850428308999267)
              ·
                refine ⟨3589134533775642463498901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392756355850428308999267 3589134533775642463498901)
                ·
                  refine ⟨168240681270733240476511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3589134533775642463498901 168240681270733240476511)
                  ·
                    rfl

theorem cell22_1474414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1474414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474414 prefixEnd_1474414 := by exact prefixLift 1474414
  have htrace : WordTrace (prefixWord ++ tailWord_1474414) baseStart_1474414 baseEnd_1474414 := by
    simpa [prefixWord, tailWord_1474414, baseEnd_1474414] using wordTrace_append hprefix tailTrace_1474414
  have hstable : (prefixWord ++ tailWord_1474414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474414).length < 2 ^ (prefixWord ++ tailWord_1474414).sum := by decide
  have hdescent : baseEnd_1474414 < baseStart_1474414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474425 : List Nat := [1, 2, 1, 3, 2, 2, 2, 9]
def baseStart_1474425 : Nat := 118140960795 + 1474425 * 2 ^ 59
def prefixEnd_1474425 : Nat := 4983230072969 + 3 ^ 40 * 1474425 * 2
def baseEnd_1474425 : Nat := 56080645481888817711611

theorem tailTrace_1474425 : CollatzResearch.WordTrace tailWord_1474425 prefixEnd_1474425 56080645481888817711611 := by
  unfold tailWord_1474425
  simp only [CollatzResearch.WordTrace]
  refine ⟨53776697683417511587352729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35851131788945007724901819 53776697683417511587352729)
  ·
    refine ⟨40332523262563133690514547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53776697683417511587352729 40332523262563133690514547)
    ·
      refine ⟨60498784893844700535771821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40332523262563133690514547 60498784893844700535771821)
      ·
        refine ⟨22687044335191762700914433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60498784893844700535771821 22687044335191762700914433)
        ·
          refine ⟨17015283251393822025685825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22687044335191762700914433 17015283251393822025685825)
          ·
            refine ⟨12761462438545366519264369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17015283251393822025685825 12761462438545366519264369)
            ·
              refine ⟨9571096828909024889448277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761462438545366519264369 9571096828909024889448277)
              ·
                refine ⟨56080645481888817711611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9571096828909024889448277 56080645481888817711611)
                ·
                  rfl

theorem cell22_1474425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 9].length) (baseStart_1474425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474425 prefixEnd_1474425 := by exact prefixLift 1474425
  have htrace : WordTrace (prefixWord ++ tailWord_1474425) baseStart_1474425 baseEnd_1474425 := by
    simpa [prefixWord, tailWord_1474425, baseEnd_1474425] using wordTrace_append hprefix tailTrace_1474425
  have hstable : (prefixWord ++ tailWord_1474425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474425).length < 2 ^ (prefixWord ++ tailWord_1474425).sum := by decide
  have hdescent : baseEnd_1474425 < baseStart_1474425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474457 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_1474457 : Nat := 118140960795 + 1474457 * 2 ^ 59
def prefixEnd_1474457 : Nat := 4983230072969 + 3 ^ 40 * 1474457 * 2
def baseEnd_1474457 : Nat := 504736763590961942604401

theorem tailTrace_1474457 : CollatzResearch.WordTrace tailWord_1474457 prefixEnd_1474457 504736763590961942604401 := by
  unfold tailWord_1474457
  simp only [CollatzResearch.WordTrace]
  refine ⟨53777864819301581052517625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35851909879534387368345083 53777864819301581052517625)
  ·
    refine ⟨40333398614476185789388219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53777864819301581052517625 40333398614476185789388219)
    ·
      refine ⟨60500097921714278684082329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40333398614476185789388219 60500097921714278684082329)
      ·
        refine ⟨45375073441285709013061747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60500097921714278684082329 45375073441285709013061747)
        ·
          refine ⟨68062610161928563519592621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45375073441285709013061747 68062610161928563519592621)
          ·
            refine ⟨25523478810723211319847233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68062610161928563519592621 25523478810723211319847233)
            ·
              refine ⟨19142609108042408489885425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25523478810723211319847233 19142609108042408489885425)
              ·
                refine ⟨14356956831031806367414069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19142609108042408489885425 14356956831031806367414069)
                ·
                  refine ⟨1345964702909231846945069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14356956831031806367414069 1345964702909231846945069)
                  ·
                    refine ⟨504736763590961942604401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345964702909231846945069 504736763590961942604401)
                    ·
                      rfl

theorem cell22_1474457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_1474457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474457 prefixEnd_1474457 := by exact prefixLift 1474457
  have htrace : WordTrace (prefixWord ++ tailWord_1474457) baseStart_1474457 baseEnd_1474457 := by
    simpa [prefixWord, tailWord_1474457, baseEnd_1474457] using wordTrace_append hprefix tailTrace_1474457
  have hstable : (prefixWord ++ tailWord_1474457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474457).length < 2 ^ (prefixWord ++ tailWord_1474457).sum := by decide
  have hdescent : baseEnd_1474457 < baseStart_1474457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474532 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1474532 : Nat := 118140960795 + 1474532 * 2 ^ 59
def prefixEnd_1474532 : Nat := 4983230072969 + 3 ^ 40 * 1474532 * 2
def baseEnd_1474532 : Nat := 168254145874562248993057

theorem tailTrace_1474532 : CollatzResearch.WordTrace tailWord_1474532 prefixEnd_1474532 168254145874562248993057 := by
  unfold tailWord_1474532
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890300147014934430748925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35853733529353245907665233 26890300147014934430748925)
  ·
    refine ⟨10083862555130600411530847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26890300147014934430748925 10083862555130600411530847)
    ·
      refine ⟨15125793832695900617296271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083862555130600411530847 15125793832695900617296271)
      ·
        refine ⟨22688690749043850925944407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15125793832695900617296271 22688690749043850925944407)
        ·
          refine ⟨34033036123565776388916611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22688690749043850925944407 34033036123565776388916611)
          ·
            refine ⟨51049554185348664583374917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34033036123565776388916611 51049554185348664583374917)
            ·
              refine ⟨9571791409752874609382797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51049554185348664583374917 9571791409752874609382797)
              ·
                refine ⟨3589421778657327978518549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9571791409752874609382797 3589421778657327978518549)
                ·
                  refine ⟨168254145874562248993057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3589421778657327978518549 168254145874562248993057)
                  ·
                    rfl

theorem cell22_1474532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1474532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474532 prefixEnd_1474532 := by exact prefixLift 1474532
  have htrace : WordTrace (prefixWord ++ tailWord_1474532) baseStart_1474532 baseEnd_1474532 := by
    simpa [prefixWord, tailWord_1474532, baseEnd_1474532] using wordTrace_append hprefix tailTrace_1474532
  have hstable : (prefixWord ++ tailWord_1474532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474532).length < 2 ^ (prefixWord ++ tailWord_1474532).sum := by decide
  have hdescent : baseEnd_1474532 < baseStart_1474532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474581 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_1474581 : Nat := 118140960795 + 1474581 * 2 ^ 59
def prefixEnd_1474581 : Nat := 4983230072969 + 3 ^ 40 * 1474581 * 2
def baseEnd_1474581 : Nat := 504779211325066952504021

theorem tailTrace_1474581 : CollatzResearch.WordTrace tailWord_1474581 prefixEnd_1474581 504779211325066952504021 := by
  unfold tailWord_1474581
  simp only [CollatzResearch.WordTrace]
  refine ⟨53782387470852350230031597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35854924980568233486687731 53782387470852350230031597)
  ·
    refine ⟨20168395301569631336261849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53782387470852350230031597 20168395301569631336261849)
    ·
      refine ⟨15126296476177223502196387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20168395301569631336261849 15126296476177223502196387)
      ·
        refine ⟨22689444714265835253294581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126296476177223502196387 22689444714265835253294581)
        ·
          refine ⟨2127135441962422054996367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22689444714265835253294581 2127135441962422054996367)
          ·
            refine ⟨3190703162943633082494551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127135441962422054996367 3190703162943633082494551)
            ·
              refine ⟨4786054744415449623741827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190703162943633082494551 4786054744415449623741827)
              ·
                refine ⟨7179082116623174435612741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786054744415449623741827 7179082116623174435612741)
                ·
                  refine ⟨1346077896866845206677389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7179082116623174435612741 1346077896866845206677389)
                  ·
                    refine ⟨504779211325066952504021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1346077896866845206677389 504779211325066952504021)
                    ·
                      rfl

theorem cell22_1474581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_1474581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474581 prefixEnd_1474581 := by exact prefixLift 1474581
  have htrace : WordTrace (prefixWord ++ tailWord_1474581) baseStart_1474581 baseEnd_1474581 := by
    simpa [prefixWord, tailWord_1474581, baseEnd_1474581] using wordTrace_append hprefix tailTrace_1474581
  have hstable : (prefixWord ++ tailWord_1474581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474581).length < 2 ^ (prefixWord ++ tailWord_1474581).sum := by decide
  have hdescent : baseEnd_1474581 < baseStart_1474581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474656 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_1474656 : Nat := 118140960795 + 1474656 * 2 ^ 59
def prefixEnd_1474656 : Nat := 4983230072969 + 3 ^ 40 * 1474656 * 2
def baseEnd_1474656 : Nat := 168268295119263918959597

theorem tailTrace_1474656 : CollatzResearch.WordTrace tailWord_1474656 prefixEnd_1474656 168268295119263918959597 := by
  unfold tailWord_1474656
  simp only [CollatzResearch.WordTrace]
  refine ⟨26892561472790319019505911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35856748630387092026007881 26892561472790319019505911)
  ·
    refine ⟨40338842209185478529258867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26892561472790319019505911 40338842209185478529258867)
    ·
      refine ⟨60508263313778217793888301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40338842209185478529258867 60508263313778217793888301)
      ·
        refine ⟨22690598742666831672708113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60508263313778217793888301 22690598742666831672708113)
        ·
          refine ⟨17017949057000123754531085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22690598742666831672708113 17017949057000123754531085)
          ·
            refine ⟨6381730896375046407949157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17017949057000123754531085 6381730896375046407949157)
            ·
              refine ⟨1196574543070321201490467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6381730896375046407949157 1196574543070321201490467)
              ·
                refine ⟨1794861814605481802235701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196574543070321201490467 1794861814605481802235701)
                ·
                  refine ⟨168268295119263918959597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1794861814605481802235701 168268295119263918959597)
                  ·
                    rfl

theorem cell22_1474656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_1474656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474656 prefixEnd_1474656 := by exact prefixLift 1474656
  have htrace : WordTrace (prefixWord ++ tailWord_1474656) baseStart_1474656 baseEnd_1474656 := by
    simpa [prefixWord, tailWord_1474656, baseEnd_1474656] using wordTrace_append hprefix tailTrace_1474656
  have hstable : (prefixWord ++ tailWord_1474656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474656).length < 2 ^ (prefixWord ++ tailWord_1474656).sum := by decide
  have hdescent : baseEnd_1474656 < baseStart_1474656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474716 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1474716 : Nat := 118140960795 + 1474716 * 2 ^ 59
def prefixEnd_1474716 : Nat := 4983230072969 + 3 ^ 40 * 1474716 * 2
def baseEnd_1474716 : Nat := 504825424583971600378607

theorem tailTrace_1474716 : CollatzResearch.WordTrace tailWord_1474716 prefixEnd_1474716 504825424583971600378607 := by
  unfold tailWord_1474716
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893655662681634143098001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35858207550242178857464001 26893655662681634143098001)
  ·
    refine ⟨20170241747011225607323501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26893655662681634143098001 20170241747011225607323501)
    ·
      refine ⟨7563840655129209602746313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20170241747011225607323501 7563840655129209602746313)
      ·
        refine ⟨5672880491346907202059735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7563840655129209602746313 5672880491346907202059735)
        ·
          refine ⟨8509320737020360803089603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5672880491346907202059735 8509320737020360803089603)
          ·
            refine ⟨12763981105530541204634405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509320737020360803089603 12763981105530541204634405)
            ·
              refine ⟨2393246457286976475868951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12763981105530541204634405 2393246457286976475868951)
              ·
                refine ⟨3589869685930464713803427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393246457286976475868951 3589869685930464713803427)
                ·
                  refine ⟨5384804528895697070705141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589869685930464713803427 5384804528895697070705141)
                  ·
                    refine ⟨504825424583971600378607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5384804528895697070705141 504825424583971600378607)
                    ·
                      rfl

theorem cell22_1474716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1474716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474716 prefixEnd_1474716 := by exact prefixLift 1474716
  have htrace : WordTrace (prefixWord ++ tailWord_1474716) baseStart_1474716 baseEnd_1474716 := by
    simpa [prefixWord, tailWord_1474716, baseEnd_1474716] using wordTrace_append hprefix tailTrace_1474716
  have hstable : (prefixWord ++ tailWord_1474716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474716).length < 2 ^ (prefixWord ++ tailWord_1474716).sum := by decide
  have hdescent : baseEnd_1474716 < baseStart_1474716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474718 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1474718 : Nat := 118140960795 + 1474718 * 2 ^ 59
def prefixEnd_1474718 : Nat := 4983230072969 + 3 ^ 40 * 1474718 * 2
def baseEnd_1474718 : Nat := 168275369741614753942867

theorem tailTrace_1474718 : CollatzResearch.WordTrace tailWord_1474718 prefixEnd_1474718 168275369741614753942867 := by
  unfold tailWord_1474718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723423033919502828471101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35858256180904015085179205 6723423033919502828471101)
  ·
    refine ⟨2521283637719813560676663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6723423033919502828471101 2521283637719813560676663)
    ·
      refine ⟨3781925456579720341014995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2521283637719813560676663 3781925456579720341014995)
      ·
        refine ⟨5672888184869580511522493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781925456579720341014995 5672888184869580511522493)
        ·
          refine ⟨2127333069326092691820935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5672888184869580511522493 2127333069326092691820935)
          ·
            refine ⟨3190999603989139037731403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127333069326092691820935 3190999603989139037731403)
            ·
              refine ⟨4786499405983708556597105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190999603989139037731403 4786499405983708556597105)
              ·
                refine ⟨3589874554487781417447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786499405983708556597105 3589874554487781417447829)
                ·
                  refine ⟨168275369741614753942867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3589874554487781417447829 168275369741614753942867)
                  ·
                    rfl

theorem cell22_1474718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1474718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474718 prefixEnd_1474718 := by exact prefixLift 1474718
  have htrace : WordTrace (prefixWord ++ tailWord_1474718) baseStart_1474718 baseEnd_1474718 := by
    simpa [prefixWord, tailWord_1474718, baseEnd_1474718] using wordTrace_append hprefix tailTrace_1474718
  have hstable : (prefixWord ++ tailWord_1474718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474718).length < 2 ^ (prefixWord ++ tailWord_1474718).sum := by decide
  have hdescent : baseEnd_1474718 < baseStart_1474718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474737 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_1474737 : Nat := 118140960795 + 1474737 * 2 ^ 59
def prefixEnd_1474737 : Nat := 4983230072969 + 3 ^ 40 * 1474737 * 2
def baseEnd_1474737 : Nat := 504832613313134545603543

theorem tailTrace_1474737 : CollatzResearch.WordTrace tailWord_1474737 prefixEnd_1474737 504832613313134545603543 := by
  unfold tailWord_1474737
  simp only [CollatzResearch.WordTrace]
  refine ⟨53788077258287188872710465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35858718172191459248473643 53788077258287188872710465)
  ·
    refine ⟨40341057943715391654532849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53788077258287188872710465 40341057943715391654532849)
    ·
      refine ⟨30255793457786543740899637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40341057943715391654532849 30255793457786543740899637)
      ·
        refine ⟨2836480636667488475709341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30255793457786543740899637 2836480636667488475709341)
        ·
          refine ⟨1063680238750308178391003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2836480636667488475709341 1063680238750308178391003)
          ·
            refine ⟨1595520358125462267586505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063680238750308178391003 1595520358125462267586505)
            ·
              refine ⟨1196640268594096700689879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595520358125462267586505 1196640268594096700689879)
              ·
                refine ⟨1794960402891145051034819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196640268594096700689879 1794960402891145051034819)
                ·
                  refine ⟨2692440604336717576552229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794960402891145051034819 2692440604336717576552229)
                  ·
                    refine ⟨504832613313134545603543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2692440604336717576552229 504832613313134545603543)
                    ·
                      rfl

theorem cell22_1474737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_1474737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1474737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1474737 prefixEnd_1474737 := by exact prefixLift 1474737
  have htrace : WordTrace (prefixWord ++ tailWord_1474737) baseStart_1474737 baseEnd_1474737 := by
    simpa [prefixWord, tailWord_1474737, baseEnd_1474737] using wordTrace_append hprefix tailTrace_1474737
  have hstable : (prefixWord ++ tailWord_1474737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474737).length < 2 ^ (prefixWord ++ tailWord_1474737).sum := by decide
  have hdescent : baseEnd_1474737 < baseStart_1474737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
