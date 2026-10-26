import V185TrunkScan23Chunk0450

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2667319 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_2667319 : Nat := 118140960795 + 2667319 * 2 ^ 59
def prefixEnd_2667319 : Nat := 4983230072969 + 3 ^ 40 * 2667319 * 2
def baseEnd_2667319 : Nat := 1369616705869954835845729

theorem tailTrace_2667319 : CollatzResearch.WordTrace tailWord_2667319 prefixEnd_2667319 1369616705869954835845729 := by
  unfold tailWord_2667319
  simp only [CollatzResearch.WordTrace]
  refine ⟨97285116223766279662773011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64856744149177519775182007 97285116223766279662773011)
  ·
    refine ⟨145927674335649419494159517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97285116223766279662773011 145927674335649419494159517)
    ·
      refine ⟨54722877875868532310309819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145927674335649419494159517 54722877875868532310309819)
      ·
        refine ⟨82084316813802798465464729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54722877875868532310309819 82084316813802798465464729)
        ·
          refine ⟨61563237610352098849098547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82084316813802798465464729 61563237610352098849098547)
          ·
            refine ⟨92344856415528148273647821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61563237610352098849098547 92344856415528148273647821)
            ·
              refine ⟨34629321155823055602617933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92344856415528148273647821 34629321155823055602617933)
              ·
                refine ⟨12985995433433645850981725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34629321155823055602617933 12985995433433645850981725)
                ·
                  refine ⟨4869748287537617194118147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12985995433433645850981725 4869748287537617194118147)
                  ·
                    refine ⟨7304622431306425791177221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869748287537617194118147 7304622431306425791177221)
                    ·
                      refine ⟨1369616705869954835845729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7304622431306425791177221 1369616705869954835845729)
                      ·
                        rfl

theorem cell23_2667319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_2667319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667319 prefixEnd_2667319 := by exact prefixLift 2667319
  have htrace : WordTrace (prefixWord ++ tailWord_2667319) baseStart_2667319 baseEnd_2667319 := by
    simpa [prefixWord, tailWord_2667319, baseEnd_2667319] using wordTrace_append hprefix tailTrace_2667319
  have hstable : (prefixWord ++ tailWord_2667319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667319).length < 2 ^ (prefixWord ++ tailWord_2667319).sum := by decide
  have hdescent : baseEnd_2667319 < baseStart_2667319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667336 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2667336 : Nat := 118140960795 + 2667336 * 2 ^ 59
def prefixEnd_2667336 : Nat := 4983230072969 + 3 ^ 40 * 2667336 * 2
def baseEnd_2667336 : Nat := 1369625435041081269333151

theorem tailTrace_2667336 : CollatzResearch.WordTrace tailWord_2667336 prefixEnd_2667336 1369625435041081269333151 := by
  unfold tailWord_2667336
  simp only [CollatzResearch.WordTrace]
  refine ⟨48642868132352345783070931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64857157509803127710761241 48642868132352345783070931)
  ·
    refine ⟨72964302198528518674606397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48642868132352345783070931 72964302198528518674606397)
    ·
      refine ⟨27361613324448194502977399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72964302198528518674606397 27361613324448194502977399)
      ·
        refine ⟨41042419986672291754466099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27361613324448194502977399 41042419986672291754466099)
        ·
          refine ⟨61563629980008437631699149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41042419986672291754466099 61563629980008437631699149)
          ·
            refine ⟨23086361242503164111887181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61563629980008437631699149 23086361242503164111887181)
            ·
              refine ⟨8657385465938686541957693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23086361242503164111887181 8657385465938686541957693)
              ·
                refine ⟨3246519549727007453234135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8657385465938686541957693 3246519549727007453234135)
                ·
                  refine ⟨4869779324590511179851203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246519549727007453234135 4869779324590511179851203)
                  ·
                    refine ⟨7304668986885766769776805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4869779324590511179851203 7304668986885766769776805)
                    ·
                      refine ⟨1369625435041081269333151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7304668986885766769776805 1369625435041081269333151)
                      ·
                        rfl

theorem cell23_2667336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2667336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667336 prefixEnd_2667336 := by exact prefixLift 2667336
  have htrace : WordTrace (prefixWord ++ tailWord_2667336) baseStart_2667336 baseEnd_2667336 := by
    simpa [prefixWord, tailWord_2667336, baseEnd_2667336] using wordTrace_append hprefix tailTrace_2667336
  have hstable : (prefixWord ++ tailWord_2667336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667336).length < 2 ^ (prefixWord ++ tailWord_2667336).sum := by decide
  have hdescent : baseEnd_2667336 < baseStart_2667336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667346 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2667346 : Nat := 118140960795 + 2667346 * 2 ^ 59
def prefixEnd_2667346 : Nat := 4983230072969 + 3 ^ 40 * 2667346 * 2
def baseEnd_2667346 : Nat := 456543523282542076736035

theorem tailTrace_2667346 : CollatzResearch.WordTrace tailWord_2667346 prefixEnd_2667346 456543523282542076736035 := by
  unfold tailWord_2667346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321525248667115818501473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64857400663112308849337261 24321525248667115818501473)
  ·
    refine ⟨18241143936500336863876105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321525248667115818501473 18241143936500336863876105)
    ·
      refine ⟨13680857952375252647907079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18241143936500336863876105 13680857952375252647907079)
      ·
        refine ⟨20521286928562878971860619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13680857952375252647907079 20521286928562878971860619)
        ·
          refine ⟨30781930392844318457790929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20521286928562878971860619 30781930392844318457790929)
          ·
            refine ⟨23086447794633238843343197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30781930392844318457790929 23086447794633238843343197)
            ·
              refine ⟨8657417922987464566253699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23086447794633238843343197 8657417922987464566253699)
              ·
                refine ⟨12986126884481196849380549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8657417922987464566253699 12986126884481196849380549)
                ·
                  refine ⟨2434898790840224409258853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12986126884481196849380549 2434898790840224409258853)
                  ·
                    refine ⟨456543523282542076736035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434898790840224409258853 456543523282542076736035)
                    ·
                      rfl

theorem cell23_2667346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2667346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667346 prefixEnd_2667346 := by exact prefixLift 2667346
  have htrace : WordTrace (prefixWord ++ tailWord_2667346) baseStart_2667346 baseEnd_2667346 := by
    simpa [prefixWord, tailWord_2667346, baseEnd_2667346] using wordTrace_append hprefix tailTrace_2667346
  have hstable : (prefixWord ++ tailWord_2667346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667346).length < 2 ^ (prefixWord ++ tailWord_2667346).sum := by decide
  have hdescent : baseEnd_2667346 < baseStart_2667346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667349 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2667349 : Nat := 118140960795 + 2667349 * 2 ^ 59
def prefixEnd_2667349 : Nat := 4983230072969 + 3 ^ 40 * 2667349 * 2
def baseEnd_2667349 : Nat := 1369632110289589718470591

theorem tailTrace_2667349 : CollatzResearch.WordTrace tailWord_2667349 prefixEnd_2667349 1369632110289589718470591 := by
  unfold tailWord_2667349
  simp only [CollatzResearch.WordTrace]
  refine ⟨97286210413657594786365101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64857473609105063190910067 97286210413657594786365101)
  ·
    refine ⟨36482328905121598044886913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97286210413657594786365101 36482328905121598044886913)
    ·
      refine ⟨27361746678841198533665185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36482328905121598044886913 27361746678841198533665185)
      ·
        refine ⟨20521310009130898900248889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27361746678841198533665185 20521310009130898900248889)
        ·
          refine ⟨15390982506848174175186667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20521310009130898900248889 15390982506848174175186667)
          ·
            refine ⟨23086473760272261262780001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15390982506848174175186667 23086473760272261262780001)
            ·
              refine ⟨17314855320204195947085001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23086473760272261262780001 17314855320204195947085001)
              ·
                refine ⟨12986141490153146960313751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17314855320204195947085001 12986141490153146960313751)
                ·
                  refine ⟨19479212235229720440470627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12986141490153146960313751 19479212235229720440470627)
                  ·
                    refine ⟨29218818352844580660705941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19479212235229720440470627 29218818352844580660705941)
                    ·
                      refine ⟨1369632110289589718470591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29218818352844580660705941 1369632110289589718470591)
                      ·
                        rfl

theorem cell23_2667349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2667349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667349 prefixEnd_2667349 := by exact prefixLift 2667349
  have htrace : WordTrace (prefixWord ++ tailWord_2667349) baseStart_2667349 baseEnd_2667349 := by
    simpa [prefixWord, tailWord_2667349, baseEnd_2667349] using wordTrace_append hprefix tailTrace_2667349
  have hstable : (prefixWord ++ tailWord_2667349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667349).length < 2 ^ (prefixWord ++ tailWord_2667349).sum := by decide
  have hdescent : baseEnd_2667349 < baseStart_2667349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667353 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 3, 2, 2]
def baseStart_2667353 : Nat := 118140960795 + 2667353 * 2 ^ 59
def prefixEnd_2667353 : Nat := 4983230072969 + 3 ^ 40 * 2667353 * 2
def baseEnd_2667353 : Nat := 1369634164212207702820573

theorem tailTrace_2667353 : CollatzResearch.WordTrace tailWord_2667353 prefixEnd_2667353 1369634164212207702820573 := by
  unfold tailWord_2667353
  simp only [CollatzResearch.WordTrace]
  refine ⟨97286356305643103469510713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64857570870428735646340475 97286356305643103469510713)
  ·
    refine ⟨72964767229232327602133035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97286356305643103469510713 72964767229232327602133035)
    ·
      refine ⟨109447150843848491403199553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72964767229232327602133035 109447150843848491403199553)
      ·
        refine ⟨82085363132886368552399665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109447150843848491403199553 82085363132886368552399665)
        ·
          refine ⟨61564022349664776414299749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82085363132886368552399665 61564022349664776414299749)
          ·
            refine ⟨11543254190562145577681203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61564022349664776414299749 11543254190562145577681203)
            ·
              refine ⟨17314881285843218366521805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543254190562145577681203 17314881285843218366521805)
              ·
                refine ⟨6493080482191206887445677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17314881285843218366521805 6493080482191206887445677)
                ·
                  refine ⟨2434905180821702582792129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6493080482191206887445677 2434905180821702582792129)
                  ·
                    refine ⟨1826178885616276937094097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434905180821702582792129 1826178885616276937094097)
                    ·
                      refine ⟨1369634164212207702820573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826178885616276937094097 1369634164212207702820573)
                      ·
                        rfl

theorem cell23_2667353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_2667353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667353 prefixEnd_2667353 := by exact prefixLift 2667353
  have htrace : WordTrace (prefixWord ++ tailWord_2667353) baseStart_2667353 baseEnd_2667353 := by
    simpa [prefixWord, tailWord_2667353, baseEnd_2667353] using wordTrace_append hprefix tailTrace_2667353
  have hstable : (prefixWord ++ tailWord_2667353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667353).length < 2 ^ (prefixWord ++ tailWord_2667353).sum := by decide
  have hdescent : baseEnd_2667353 < baseStart_2667353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667356 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2667356 : Nat := 118140960795 + 2667356 * 2 ^ 59
def prefixEnd_2667356 : Nat := 4983230072969 + 3 ^ 40 * 2667356 * 2
def baseEnd_2667356 : Nat := 1369635704654171191083059

theorem tailTrace_2667356 : CollatzResearch.WordTrace tailWord_2667356 prefixEnd_2667356 1369635704654171191083059 := by
  unfold tailWord_2667356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48643232862316117490934961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64857643816421489987913281 48643232862316117490934961)
  ·
    refine ⟨36482424646737088118201221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48643232862316117490934961 36482424646737088118201221)
    ·
      refine ⟨6840454621263204022162729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36482424646737088118201221 6840454621263204022162729)
      ·
        refine ⟨5130340965947403016622047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6840454621263204022162729 5130340965947403016622047)
        ·
          refine ⟨7695511448921104524933071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130340965947403016622047 7695511448921104524933071)
          ·
            refine ⟨11543267173381656787399607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695511448921104524933071 11543267173381656787399607)
            ·
              refine ⟨17314900760072485181099411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543267173381656787399607 17314900760072485181099411)
              ·
                refine ⟨25972351140108727771649117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17314900760072485181099411 25972351140108727771649117)
                ·
                  refine ⟨9739631677540772914368419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25972351140108727771649117 9739631677540772914368419)
                  ·
                    refine ⟨14609447516311159371552629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9739631677540772914368419 14609447516311159371552629)
                    ·
                      refine ⟨1369635704654171191083059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14609447516311159371552629 1369635704654171191083059)
                      ·
                        rfl

theorem cell23_2667356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2667356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667356 prefixEnd_2667356 := by exact prefixLift 2667356
  have htrace : WordTrace (prefixWord ++ tailWord_2667356) baseStart_2667356 baseEnd_2667356 := by
    simpa [prefixWord, tailWord_2667356, baseEnd_2667356] using wordTrace_append hprefix tailTrace_2667356
  have hstable : (prefixWord ++ tailWord_2667356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667356).length < 2 ^ (prefixWord ++ tailWord_2667356).sum := by decide
  have hdescent : baseEnd_2667356 < baseStart_2667356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667390 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2667390 : Nat := 118140960795 + 2667390 * 2 ^ 59
def prefixEnd_2667390 : Nat := 4983230072969 + 3 ^ 40 * 2667390 * 2
def baseEnd_2667390 : Nat := 1369653162996424058057903

theorem tailTrace_2667390 : CollatzResearch.WordTrace tailWord_2667390 prefixEnd_2667390 1369653162996424058057903 := by
  unfold tailWord_2667390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160963225813632348575953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64858470537672705859071749 12160963225813632348575953)
  ·
    refine ⟨9120722419360224261431965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12160963225813632348575953 9120722419360224261431965)
    ·
      refine ⟨3420270907260084098036987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9120722419360224261431965 3420270907260084098036987)
      ·
        refine ⟨5130406360890126147055481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420270907260084098036987 5130406360890126147055481)
        ·
          refine ⟨3847804770667594610291611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5130406360890126147055481 3847804770667594610291611)
          ·
            refine ⟨5771707156001391915437417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847804770667594610291611 5771707156001391915437417)
            ·
              refine ⟨4328780367001043936578063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5771707156001391915437417 4328780367001043936578063)
              ·
                refine ⟨6493170550501565904867095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328780367001043936578063 6493170550501565904867095)
                ·
                  refine ⟨9739755825752348857300643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493170550501565904867095 9739755825752348857300643)
                  ·
                    refine ⟨14609633738628523285950965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9739755825752348857300643 14609633738628523285950965)
                    ·
                      refine ⟨1369653162996424058057903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14609633738628523285950965 1369653162996424058057903)
                      ·
                        rfl

theorem cell23_2667390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2667390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667390 prefixEnd_2667390 := by exact prefixLift 2667390
  have htrace : WordTrace (prefixWord ++ tailWord_2667390) baseStart_2667390 baseEnd_2667390 := by
    simpa [prefixWord, tailWord_2667390, baseEnd_2667390] using wordTrace_append hprefix tailTrace_2667390
  have hstable : (prefixWord ++ tailWord_2667390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667390).length < 2 ^ (prefixWord ++ tailWord_2667390).sum := by decide
  have hdescent : baseEnd_2667390 < baseStart_2667390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667409 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2667409 : Nat := 118140960795 + 2667409 * 2 ^ 59
def prefixEnd_2667409 : Nat := 4983230072969 + 3 ^ 40 * 2667409 * 2
def baseEnd_2667409 : Nat := 1369662919128859483720315

theorem tailTrace_2667409 : CollatzResearch.WordTrace tailWord_2667409 prefixEnd_2667409 1369662919128859483720315 := by
  unfold tailWord_2667409
  simp only [CollatzResearch.WordTrace]
  refine ⟨97288398793440225033549281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64858932528960150022366187 97288398793440225033549281)
  ·
    refine ⟨72966299095080168775161961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97288398793440225033549281 72966299095080168775161961)
    ·
      refine ⟨54724724321310126581371471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72966299095080168775161961 54724724321310126581371471)
      ·
        refine ⟨82087086481965189872057207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54724724321310126581371471 82087086481965189872057207)
        ·
          refine ⟨123130629722947784808085811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82087086481965189872057207 123130629722947784808085811)
          ·
            refine ⟨184695944584421677212128717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123130629722947784808085811 184695944584421677212128717)
            ·
              refine ⟨69260979219158128954548269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184695944584421677212128717 69260979219158128954548269)
              ·
                refine ⟨25972867207184298357955601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69260979219158128954548269 25972867207184298357955601)
                ·
                  refine ⟨19479650405388223768466701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25972867207184298357955601 19479650405388223768466701)
                  ·
                    refine ⟨7304868902020583913175013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19479650405388223768466701 7304868902020583913175013)
                    ·
                      refine ⟨1369662919128859483720315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7304868902020583913175013 1369662919128859483720315)
                      ·
                        rfl

theorem cell23_2667409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2667409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667409 prefixEnd_2667409 := by exact prefixLift 2667409
  have htrace : WordTrace (prefixWord ++ tailWord_2667409) baseStart_2667409 baseEnd_2667409 := by
    simpa [prefixWord, tailWord_2667409, baseEnd_2667409] using wordTrace_append hprefix tailTrace_2667409
  have hstable : (prefixWord ++ tailWord_2667409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667409).length < 2 ^ (prefixWord ++ tailWord_2667409).sum := by decide
  have hdescent : baseEnd_2667409 < baseStart_2667409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667414 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2667414 : Nat := 118140960795 + 2667414 * 2 ^ 59
def prefixEnd_2667414 : Nat := 4983230072969 + 3 ^ 40 * 2667414 * 2
def baseEnd_2667414 : Nat := 456555162177377321385931

theorem tailTrace_2667414 : CollatzResearch.WordTrace tailWord_2667414 prefixEnd_2667414 456555162177377321385931 := by
  unfold tailWord_2667414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080536322401381930467581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64859054105614740591654197 6080536322401381930467581)
  ·
    refine ⟨2280201120900518223925343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6080536322401381930467581 2280201120900518223925343)
    ·
      refine ⟨3420301681350777335888015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280201120900518223925343 3420301681350777335888015)
      ·
        refine ⟨5130452522026166003832023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420301681350777335888015 5130452522026166003832023)
        ·
          refine ⟨7695678783039249005748035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130452522026166003832023 7695678783039249005748035)
          ·
            refine ⟨11543518174558873508622053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695678783039249005748035 11543518174558873508622053)
            ·
              refine ⟨2164409657729788782866635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11543518174558873508622053 2164409657729788782866635)
              ·
                refine ⟨3246614486594683174299953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164409657729788782866635 3246614486594683174299953)
                ·
                  refine ⟨2434960864946012380724965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246614486594683174299953 2434960864946012380724965)
                  ·
                    refine ⟨456555162177377321385931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2434960864946012380724965 456555162177377321385931)
                    ·
                      rfl

theorem cell23_2667414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2667414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667414 prefixEnd_2667414 := by exact prefixLift 2667414
  have htrace : WordTrace (prefixWord ++ tailWord_2667414) baseStart_2667414 baseEnd_2667414 := by
    simpa [prefixWord, tailWord_2667414, baseEnd_2667414] using wordTrace_append hprefix tailTrace_2667414
  have hstable : (prefixWord ++ tailWord_2667414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667414).length < 2 ^ (prefixWord ++ tailWord_2667414).sum := by decide
  have hdescent : baseEnd_2667414 < baseStart_2667414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667439 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_2667439 : Nat := 118140960795 + 2667439 * 2 ^ 59
def prefixEnd_2667439 : Nat := 4983230072969 + 3 ^ 40 * 2667439 * 2
def baseEnd_2667439 : Nat := 1369678323548494366345177

theorem tailTrace_2667439 : CollatzResearch.WordTrace tailWord_2667439 prefixEnd_2667439 1369678323548494366345177 := by
  unfold tailWord_2667439
  simp only [CollatzResearch.WordTrace]
  refine ⟨97289492983331540157141371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64859661988887693438094247 97289492983331540157141371)
  ·
    refine ⟨145934239474997310235712057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97289492983331540157141371 145934239474997310235712057)
    ·
      refine ⟨109450679606247982676784043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145934239474997310235712057 109450679606247982676784043)
      ·
        refine ⟨164176019409371974015176065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109450679606247982676784043 164176019409371974015176065)
        ·
          refine ⟨123132014557028980511382049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164176019409371974015176065 123132014557028980511382049)
          ·
            refine ⟨92349010917771735383536537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123132014557028980511382049 92349010917771735383536537)
            ·
              refine ⟨69261758188328801537652403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92349010917771735383536537 69261758188328801537652403)
              ·
                refine ⟨103892637282493202306478605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69261758188328801537652403 103892637282493202306478605)
                ·
                  refine ⟨38959738980934950864929477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103892637282493202306478605 38959738980934950864929477)
                  ·
                    refine ⟨7304951058925303287174277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38959738980934950864929477 7304951058925303287174277)
                    ·
                      refine ⟨1369678323548494366345177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7304951058925303287174277 1369678323548494366345177)
                      ·
                        rfl

theorem cell23_2667439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_2667439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667439 prefixEnd_2667439 := by exact prefixLift 2667439
  have htrace : WordTrace (prefixWord ++ tailWord_2667439) baseStart_2667439 baseEnd_2667439 := by
    simpa [prefixWord, tailWord_2667439, baseEnd_2667439] using wordTrace_append hprefix tailTrace_2667439
  have hstable : (prefixWord ++ tailWord_2667439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667439).length < 2 ^ (prefixWord ++ tailWord_2667439).sum := by decide
  have hdescent : baseEnd_2667439 < baseStart_2667439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667443 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 4, 2, 2]
def baseStart_2667443 : Nat := 118140960795 + 2667443 * 2 ^ 59
def prefixEnd_2667443 : Nat := 4983230072969 + 3 ^ 40 * 2667443 * 2
def baseEnd_2667443 : Nat := 1369680377471112350695159

theorem tailTrace_2667443 : CollatzResearch.WordTrace tailWord_2667443 prefixEnd_2667443 1369680377471112350695159 := by
  unfold tailWord_2667443
  simp only [CollatzResearch.WordTrace]
  refine ⟨97289638875317048840286983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64859759250211365893524655 97289638875317048840286983)
  ·
    refine ⟨145934458312975573260430475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97289638875317048840286983 145934458312975573260430475)
    ·
      refine ⟨218901687469463359890645713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145934458312975573260430475 218901687469463359890645713)
      ·
        refine ⟨164176265602097519917984285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218901687469463359890645713 164176265602097519917984285)
        ·
          refine ⟨61566099600786569969244107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164176265602097519917984285 61566099600786569969244107)
          ·
            refine ⟨92349149401179854953866161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61566099600786569969244107 92349149401179854953866161)
            ·
              refine ⟨69261862050884891215399621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92349149401179854953866161 69261862050884891215399621)
              ·
                refine ⟨12986599134540917102887429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69261862050884891215399621 12986599134540917102887429)
                ·
                  refine ⟨2434987337726421956791393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12986599134540917102887429 2434987337726421956791393)
                  ·
                    refine ⟨1826240503294816467593545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2434987337726421956791393 1826240503294816467593545)
                    ·
                      refine ⟨1369680377471112350695159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826240503294816467593545 1369680377471112350695159)
                      ·
                        rfl

theorem cell23_2667443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 2, 2].length) (baseStart_2667443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667443 prefixEnd_2667443 := by exact prefixLift 2667443
  have htrace : WordTrace (prefixWord ++ tailWord_2667443) baseStart_2667443 baseEnd_2667443 := by
    simpa [prefixWord, tailWord_2667443, baseEnd_2667443] using wordTrace_append hprefix tailTrace_2667443
  have hstable : (prefixWord ++ tailWord_2667443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667443).length < 2 ^ (prefixWord ++ tailWord_2667443).sum := by decide
  have hdescent : baseEnd_2667443 < baseStart_2667443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667546 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2667546 : Nat := 118140960795 + 2667546 * 2 ^ 59
def prefixEnd_2667546 : Nat := 4983230072969 + 3 ^ 40 * 2667546 * 2
def baseEnd_2667546 : Nat := 1369733265978525447707185

theorem tailTrace_2667546 : CollatzResearch.WordTrace tailWord_2667546 prefixEnd_2667546 1369733265978525447707185 := by
  unfold tailWord_2667546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323348898485974357821623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64862263729295931620857661 24323348898485974357821623)
  ·
    refine ⟨36485023347728961536732435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24323348898485974357821623 36485023347728961536732435)
    ·
      refine ⟨54727535021593442305098653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36485023347728961536732435 54727535021593442305098653)
      ·
        refine ⟨20522825633097540864411995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54727535021593442305098653 20522825633097540864411995)
        ·
          refine ⟨30784238449646311296617993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20522825633097540864411995 30784238449646311296617993)
          ·
            refine ⟨23088178837234733472463495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30784238449646311296617993 23088178837234733472463495)
            ·
              refine ⟨34632268255852100208695243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23088178837234733472463495 34632268255852100208695243)
              ·
                refine ⟨51948402383778150313042865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34632268255852100208695243 51948402383778150313042865)
                ·
                  refine ⟨38961301787833612734782149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51948402383778150313042865 38961301787833612734782149)
                  ·
                    refine ⟨7305244085218802387771653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38961301787833612734782149 7305244085218802387771653)
                    ·
                      refine ⟨1369733265978525447707185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7305244085218802387771653 1369733265978525447707185)
                      ·
                        rfl

theorem cell23_2667546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2667546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667546 prefixEnd_2667546 := by exact prefixLift 2667546
  have htrace : WordTrace (prefixWord ++ tailWord_2667546) baseStart_2667546 baseEnd_2667546 := by
    simpa [prefixWord, tailWord_2667546, baseEnd_2667546] using wordTrace_append hprefix tailTrace_2667546
  have hstable : (prefixWord ++ tailWord_2667546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667546).length < 2 ^ (prefixWord ++ tailWord_2667546).sum := by decide
  have hdescent : baseEnd_2667546 < baseStart_2667546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667553 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2667553 : Nat := 118140960795 + 2667553 * 2 ^ 59
def prefixEnd_2667553 : Nat := 4983230072969 + 3 ^ 40 * 2667553 * 2
def baseEnd_2667553 : Nat := 1369736860343106920319653

theorem tailTrace_2667553 : CollatzResearch.WordTrace tailWord_2667553 prefixEnd_2667553 1369736860343106920319653 := by
  unfold tailWord_2667553
  simp only [CollatzResearch.WordTrace]
  refine ⟨97293650904918537626791313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64862433936612358417860875 97293650904918537626791313)
  ·
    refine ⟨72970238178688903220093485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97293650904918537626791313 72970238178688903220093485)
    ·
      refine ⟨27363839317008338707535057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72970238178688903220093485 27363839317008338707535057)
      ·
        refine ⟨20522879487756254030651293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27363839317008338707535057 20522879487756254030651293)
        ·
          refine ⟨7696079807908595261494235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20522879487756254030651293 7696079807908595261494235)
          ·
            refine ⟨11544119711862892892241353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7696079807908595261494235 11544119711862892892241353)
            ·
              refine ⟨8658089783897169669181015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11544119711862892892241353 8658089783897169669181015)
              ·
                refine ⟨12987134675845754503771523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8658089783897169669181015 12987134675845754503771523)
                ·
                  refine ⟨19480702013768631755657285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12987134675845754503771523 19480702013768631755657285)
                  ·
                    refine ⟨3652631627581618454185741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19480702013768631755657285 3652631627581618454185741)
                    ·
                      refine ⟨1369736860343106920319653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3652631627581618454185741 1369736860343106920319653)
                      ·
                        rfl

theorem cell23_2667553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2667553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667553 prefixEnd_2667553 := by exact prefixLift 2667553
  have htrace : WordTrace (prefixWord ++ tailWord_2667553) baseStart_2667553 baseEnd_2667553 := by
    simpa [prefixWord, tailWord_2667553, baseEnd_2667553] using wordTrace_append hprefix tailTrace_2667553
  have hstable : (prefixWord ++ tailWord_2667553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667553).length < 2 ^ (prefixWord ++ tailWord_2667553).sum := by decide
  have hdescent : baseEnd_2667553 < baseStart_2667553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667593 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 5, 2]
def baseStart_2667593 : Nat := 118140960795 + 2667593 * 2 ^ 59
def prefixEnd_2667593 : Nat := 4983230072969 + 3 ^ 40 * 2667593 * 2
def baseEnd_2667593 : Nat := 1369757399569286763819469

theorem tailTrace_2667593 : CollatzResearch.WordTrace tailWord_2667593 prefixEnd_2667593 1369757399569286763819469 := by
  unfold tailWord_2667593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97295109824773624458247433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64863406549849082972164955 97295109824773624458247433)
  ·
    refine ⟨72971332368580218343685575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97295109824773624458247433 72971332368580218343685575)
    ·
      refine ⟨109456998552870327515528363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72971332368580218343685575 109456998552870327515528363)
      ·
        refine ⟨164185497829305491273292545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109456998552870327515528363 164185497829305491273292545)
        ·
          refine ⟨123139123371979118454969409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164185497829305491273292545 123139123371979118454969409)
          ·
            refine ⟨92354342528984338841227057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123139123371979118454969409 92354342528984338841227057)
            ·
              refine ⟨69265756896738254130920293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92354342528984338841227057 69265756896738254130920293)
              ·
                refine ⟨12987329418138422649547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69265756896738254130920293 12987329418138422649547555)
                ·
                  refine ⟨19480994127207633974321333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12987329418138422649547555 19480994127207633974321333)
                  ·
                    refine ⟨1826343199425715685092625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19480994127207633974321333 1826343199425715685092625)
                    ·
                      refine ⟨1369757399569286763819469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826343199425715685092625 1369757399569286763819469)
                      ·
                        rfl

theorem cell23_2667593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 5, 2].length) (baseStart_2667593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667593 prefixEnd_2667593 := by exact prefixLift 2667593
  have htrace : WordTrace (prefixWord ++ tailWord_2667593) baseStart_2667593 baseEnd_2667593 := by
    simpa [prefixWord, tailWord_2667593, baseEnd_2667593] using wordTrace_append hprefix tailTrace_2667593
  have hstable : (prefixWord ++ tailWord_2667593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667593).length < 2 ^ (prefixWord ++ tailWord_2667593).sum := by decide
  have hdescent : baseEnd_2667593 < baseStart_2667593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667657 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 3, 2, 2]
def baseStart_2667657 : Nat := 118140960795 + 2667657 * 2 ^ 59
def prefixEnd_2667657 : Nat := 4983230072969 + 3 ^ 40 * 2667657 * 2
def baseEnd_2667657 : Nat := 1369790262331174513419175

theorem tailTrace_2667657 : CollatzResearch.WordTrace tailWord_2667657 prefixEnd_2667657 1369790262331174513419175 := by
  unfold tailWord_2667657
  simp only [CollatzResearch.WordTrace]
  refine ⟨97297444096541763388577225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64864962731027842259051483 97297444096541763388577225)
  ·
    refine ⟨72973083072406322541432919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97297444096541763388577225 72973083072406322541432919)
    ·
      refine ⟨109459624608609483812149379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72973083072406322541432919 109459624608609483812149379)
      ·
        refine ⟨164189436912914225718224069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109459624608609483812149379 164189436912914225718224069)
        ·
          refine ⟨30785519421171417322167013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164189436912914225718224069 30785519421171417322167013)
          ·
            refine ⟨5772284891469640747906315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30785519421171417322167013 5772284891469640747906315)
            ·
              refine ⟨8658427337204461121859473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772284891469640747906315 8658427337204461121859473)
              ·
                refine ⟨6493820502903345841394605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8658427337204461121859473 6493820502903345841394605)
                ·
                  refine ⟨2435182688588754690522977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6493820502903345841394605 2435182688588754690522977)
                  ·
                    refine ⟨1826387016441566017892233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435182688588754690522977 1826387016441566017892233)
                    ·
                      refine ⟨1369790262331174513419175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826387016441566017892233 1369790262331174513419175)
                      ·
                        rfl

theorem cell23_2667657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 2, 2].length) (baseStart_2667657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667657 prefixEnd_2667657 := by exact prefixLift 2667657
  have htrace : WordTrace (prefixWord ++ tailWord_2667657) baseStart_2667657 baseEnd_2667657 := by
    simpa [prefixWord, tailWord_2667657, baseEnd_2667657] using wordTrace_append hprefix tailTrace_2667657
  have hstable : (prefixWord ++ tailWord_2667657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667657).length < 2 ^ (prefixWord ++ tailWord_2667657).sum := by decide
  have hdescent : baseEnd_2667657 < baseStart_2667657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667674 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2667674 : Nat := 118140960795 + 2667674 * 2 ^ 59
def prefixEnd_2667674 : Nat := 4983230072969 + 3 ^ 40 * 2667674 * 2
def baseEnd_2667674 : Nat := 1369798991502300946906597

theorem tailTrace_2667674 : CollatzResearch.WordTrace tailWord_2667674 prefixEnd_2667674 1369798991502300946906597 := by
  unfold tailWord_2667674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24324516034370043822986519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64865376091653450194630717 24324516034370043822986519)
  ·
    refine ⟨36486774051555065734479779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24324516034370043822986519 36486774051555065734479779)
    ·
      refine ⟨54730161077332598601719669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36486774051555065734479779 54730161077332598601719669)
      ·
        refine ⟨5130952600999931118911219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54730161077332598601719669 5130952600999931118911219)
        ·
          refine ⟨7696428901499896678366829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130952600999931118911219 7696428901499896678366829)
          ·
            refine ⟨2886160838062461254387561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7696428901499896678366829 2886160838062461254387561)
            ·
              refine ⟨2164620628546845940790671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886160838062461254387561 2164620628546845940790671)
              ·
                refine ⟨3246930942820268911186007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164620628546845940790671 3246930942820268911186007)
                ·
                  refine ⟨4870396414230403366779011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3246930942820268911186007 4870396414230403366779011)
                  ·
                    refine ⟨7305594621345605050168517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870396414230403366779011 7305594621345605050168517)
                    ·
                      refine ⟨1369798991502300946906597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7305594621345605050168517 1369798991502300946906597)
                      ·
                        rfl

theorem cell23_2667674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2667674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667674 prefixEnd_2667674 := by exact prefixLift 2667674
  have htrace : WordTrace (prefixWord ++ tailWord_2667674) baseStart_2667674 baseEnd_2667674 := by
    simpa [prefixWord, tailWord_2667674, baseEnd_2667674] using wordTrace_append hprefix tailTrace_2667674
  have hstable : (prefixWord ++ tailWord_2667674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667674).length < 2 ^ (prefixWord ++ tailWord_2667674).sum := by decide
  have hdescent : baseEnd_2667674 < baseStart_2667674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667743 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2667743 : Nat := 118140960795 + 2667743 * 2 ^ 59
def prefixEnd_2667743 : Nat := 4983230072969 + 3 ^ 40 * 2667743 * 2
def baseEnd_2667743 : Nat := 1369834421667461176943779

theorem tailTrace_2667743 : CollatzResearch.WordTrace tailWord_2667743 prefixEnd_2667743 1369834421667461176943779 := by
  unfold tailWord_2667743
  simp only [CollatzResearch.WordTrace]
  refine ⟨97300580774230200076207883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64867053849486800050805255 97300580774230200076207883)
  ·
    refine ⟨145950871161345300114311825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97300580774230200076207883 145950871161345300114311825)
    ·
      refine ⟨109463153371008975085733869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145950871161345300114311825 109463153371008975085733869)
      ·
        refine ⟨41048682514128365657150201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109463153371008975085733869 41048682514128365657150201)
        ·
          refine ⟨30786511885596274242862651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41048682514128365657150201 30786511885596274242862651)
          ·
            refine ⟨46179767828394411364293977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30786511885596274242862651 46179767828394411364293977)
            ·
              refine ⟨34634825871295808523220483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46179767828394411364293977 34634825871295808523220483)
              ·
                refine ⟨51952238806943712784830725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34634825871295808523220483 51952238806943712784830725)
                ·
                  refine ⟨9741044776301946147155761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51952238806943712784830725 9741044776301946147155761)
                  ·
                    refine ⟨7305783582226459610366821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9741044776301946147155761 7305783582226459610366821)
                    ·
                      refine ⟨1369834421667461176943779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7305783582226459610366821 1369834421667461176943779)
                      ·
                        rfl

theorem cell23_2667743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2667743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667743 prefixEnd_2667743 := by exact prefixLift 2667743
  have htrace : WordTrace (prefixWord ++ tailWord_2667743) baseStart_2667743 baseEnd_2667743 := by
    simpa [prefixWord, tailWord_2667743, baseEnd_2667743] using wordTrace_append hprefix tailTrace_2667743
  have hstable : (prefixWord ++ tailWord_2667743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667743).length < 2 ^ (prefixWord ++ tailWord_2667743).sum := by decide
  have hdescent : baseEnd_2667743 < baseStart_2667743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667793 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2667793 : Nat := 118140960795 + 2667793 * 2 ^ 59
def prefixEnd_2667793 : Nat := 4983230072969 + 3 ^ 40 * 2667793 * 2
def baseEnd_2667793 : Nat := 1369860095700185981318549

theorem tailTrace_2667793 : CollatzResearch.WordTrace tailWord_2667793 prefixEnd_2667793 1369860095700185981318549 := by
  unfold tailWord_2667793
  simp only [CollatzResearch.WordTrace]
  refine ⟨97302404424049058615528033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64868269616032705743685355 97302404424049058615528033)
  ·
    refine ⟨72976803318036793961646025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97302404424049058615528033 72976803318036793961646025)
    ·
      refine ⟨54732602488527595471234519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72976803318036793961646025 54732602488527595471234519)
      ·
        refine ⟨82098903732791393206851779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54732602488527595471234519 82098903732791393206851779)
        ·
          refine ⟨123148355599187089810277669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82098903732791393206851779 123148355599187089810277669)
          ·
            refine ⟨23090316674847579339427063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123148355599187089810277669 23090316674847579339427063)
            ·
              refine ⟨34635475012271369009140595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23090316674847579339427063 34635475012271369009140595)
              ·
                refine ⟨51953212518407053513710893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34635475012271369009140595 51953212518407053513710893)
                ·
                  refine ⟨19482454694402645067641585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51953212518407053513710893 19482454694402645067641585)
                  ·
                    refine ⟨14611841020801983800731189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19482454694402645067641585 14611841020801983800731189)
                    ·
                      refine ⟨1369860095700185981318549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14611841020801983800731189 1369860095700185981318549)
                      ·
                        rfl

theorem cell23_2667793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2667793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667793 prefixEnd_2667793 := by exact prefixLift 2667793
  have htrace : WordTrace (prefixWord ++ tailWord_2667793) baseStart_2667793 baseEnd_2667793 := by
    simpa [prefixWord, tailWord_2667793, baseEnd_2667793] using wordTrace_append hprefix tailTrace_2667793
  have hstable : (prefixWord ++ tailWord_2667793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667793).length < 2 ^ (prefixWord ++ tailWord_2667793).sum := by decide
  have hdescent : baseEnd_2667793 < baseStart_2667793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667800 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_2667800 : Nat := 118140960795 + 2667800 * 2 ^ 59
def prefixEnd_2667800 : Nat := 4983230072969 + 3 ^ 40 * 2667800 * 2
def baseEnd_2667800 : Nat := 456621230021589151310339

theorem tailTrace_2667800 : CollatzResearch.WordTrace tailWord_2667800 prefixEnd_2667800 456621230021589151310339 := by
  unfold tailWord_2667800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48651329867511849405516427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64868439823349132540688569 48651329867511849405516427)
  ·
    refine ⟨72976994801267774108274641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48651329867511849405516427 72976994801267774108274641)
    ·
      refine ⟨54732746100950830581205981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72976994801267774108274641 54732746100950830581205981)
      ·
        refine ⟨20524779787856561467952243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54732746100950830581205981 20524779787856561467952243)
        ·
          refine ⟨30787169681784842201928365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20524779787856561467952243 30787169681784842201928365)
          ·
            refine ⟨11545188630669315825723137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30787169681784842201928365 11545188630669315825723137)
            ·
              refine ⟨8658891473001986869292353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11545188630669315825723137 8658891473001986869292353)
              ·
                refine ⟨6494168604751490151969265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8658891473001986869292353 6494168604751490151969265)
                ·
                  refine ⟨4870626453563617613976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6494168604751490151969265 4870626453563617613976949)
                  ·
                    refine ⟨456621230021589151310339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4870626453563617613976949 456621230021589151310339)
                    ·
                      rfl

theorem cell23_2667800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_2667800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667800 prefixEnd_2667800 := by exact prefixLift 2667800
  have htrace : WordTrace (prefixWord ++ tailWord_2667800) baseStart_2667800 baseEnd_2667800 := by
    simpa [prefixWord, tailWord_2667800, baseEnd_2667800] using wordTrace_append hprefix tailTrace_2667800
  have hstable : (prefixWord ++ tailWord_2667800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667800).length < 2 ^ (prefixWord ++ tailWord_2667800).sum := by decide
  have hdescent : baseEnd_2667800 < baseStart_2667800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667803 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_2667803 : Nat := 118140960795 + 2667803 * 2 ^ 59
def prefixEnd_2667803 : Nat := 4983230072969 + 3 ^ 40 * 2667803 * 2
def baseEnd_2667803 : Nat := 1369865230506730942193503

theorem tailTrace_2667803 : CollatzResearch.WordTrace tailWord_2667803 prefixEnd_2667803 1369865230506730942193503 := by
  unfold tailWord_2667803
  simp only [CollatzResearch.WordTrace]
  refine ⟨97302769154012830323392063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64868512769341886882261375 97302769154012830323392063)
  ·
    refine ⟨145954153731019245485088095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97302769154012830323392063 145954153731019245485088095)
    ·
      refine ⟨218931230596528868227632143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145954153731019245485088095 218931230596528868227632143)
      ·
        refine ⟨328396845894793302341448215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218931230596528868227632143 328396845894793302341448215)
        ·
          refine ⟨492595268842189953512172323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328396845894793302341448215 492595268842189953512172323)
          ·
            refine ⟨738892903263284930268258485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492595268842189953512172323 738892903263284930268258485)
            ·
              refine ⟨69271209680932962212649233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 738892903263284930268258485 69271209680932962212649233)
              ·
                refine ⟨51953407260699721659486925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69271209680932962212649233 51953407260699721659486925)
                ·
                  refine ⟨19482527722762395622307597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51953407260699721659486925 19482527722762395622307597)
                  ·
                    refine ⟨7305947896035898358365349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19482527722762395622307597 7305947896035898358365349)
                    ·
                      refine ⟨1369865230506730942193503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7305947896035898358365349 1369865230506730942193503)
                      ·
                        rfl

theorem cell23_2667803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_2667803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667803 prefixEnd_2667803 := by exact prefixLift 2667803
  have htrace : WordTrace (prefixWord ++ tailWord_2667803) baseStart_2667803 baseEnd_2667803 := by
    simpa [prefixWord, tailWord_2667803, baseEnd_2667803] using wordTrace_append hprefix tailTrace_2667803
  have hstable : (prefixWord ++ tailWord_2667803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667803).length < 2 ^ (prefixWord ++ tailWord_2667803).sum := by decide
  have hdescent : baseEnd_2667803 < baseStart_2667803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667840 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_2667840 : Nat := 118140960795 + 2667840 * 2 ^ 59
def prefixEnd_2667840 : Nat := 4983230072969 + 3 ^ 40 * 2667840 * 2
def baseEnd_2667840 : Nat := 1369884229290947297430833

theorem tailTrace_2667840 : CollatzResearch.WordTrace tailWord_2667840 prefixEnd_2667840 1369884229290947297430833 := by
  unfold tailWord_2667840
  simp only [CollatzResearch.WordTrace]
  refine ⟨48652059327439392821244487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64869412436585857094992649 48652059327439392821244487)
  ·
    refine ⟨72978088991159089231866731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48652059327439392821244487 72978088991159089231866731)
    ·
      refine ⟨109467133486738633847800097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72978088991159089231866731 109467133486738633847800097)
      ·
        refine ⟨82100350115053975385850073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109467133486738633847800097 82100350115053975385850073)
        ·
          refine ⟨61575262586290481539387555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82100350115053975385850073 61575262586290481539387555)
          ·
            refine ⟨92362893879435722309081333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61575262586290481539387555 92362893879435722309081333)
            ·
              refine ⟨8659021301197098966476375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92362893879435722309081333 8659021301197098966476375)
              ·
                refine ⟨12988531951795648449714563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659021301197098966476375 12988531951795648449714563)
                ·
                  refine ⟨19482797927693472674571845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12988531951795648449714563 19482797927693472674571845)
                  ·
                    refine ⟨3653024611442526126482221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19482797927693472674571845 3653024611442526126482221)
                    ·
                      refine ⟨1369884229290947297430833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653024611442526126482221 1369884229290947297430833)
                      ·
                        rfl

theorem cell23_2667840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_2667840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667840 prefixEnd_2667840 := by exact prefixLift 2667840
  have htrace : WordTrace (prefixWord ++ tailWord_2667840) baseStart_2667840 baseEnd_2667840 := by
    simpa [prefixWord, tailWord_2667840, baseEnd_2667840] using wordTrace_append hprefix tailTrace_2667840
  have hstable : (prefixWord ++ tailWord_2667840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667840).length < 2 ^ (prefixWord ++ tailWord_2667840).sum := by decide
  have hdescent : baseEnd_2667840 < baseStart_2667840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667843 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 8]
def baseStart_2667843 : Nat := 118140960795 + 2667843 * 2 ^ 59
def prefixEnd_2667843 : Nat := 4983230072969 + 3 ^ 40 * 2667843 * 2
def baseEnd_2667843 : Nat := 152209529970323420632591

theorem tailTrace_2667843 : CollatzResearch.WordTrace tailWord_2667843 prefixEnd_2667843 152209529970323420632591 := by
  unfold tailWord_2667843
  simp only [CollatzResearch.WordTrace]
  refine ⟨97304228073867917154848183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64869485382578611436565455 97304228073867917154848183)
  ·
    refine ⟨145956342110801875732272275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97304228073867917154848183 145956342110801875732272275)
    ·
      refine ⟨218934513166202813598408413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145956342110801875732272275 218934513166202813598408413)
      ·
        refine ⟨82100442437326055099403155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218934513166202813598408413 82100442437326055099403155)
        ·
          refine ⟨123150663655989082649104733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82100442437326055099403155 123150663655989082649104733)
          ·
            refine ⟨46181498870995905993414275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123150663655989082649104733 46181498870995905993414275)
            ·
              refine ⟨69272248306493858990121413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46181498870995905993414275 69272248306493858990121413)
              ·
                refine ⟨12988546557467598560647765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69272248306493858990121413 12988546557467598560647765)
                ·
                  refine ⟨152209529970323420632591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12988546557467598560647765 152209529970323420632591)
                  ·
                    rfl

theorem cell23_2667843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 8].length) (baseStart_2667843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667843 prefixEnd_2667843 := by exact prefixLift 2667843
  have htrace : WordTrace (prefixWord ++ tailWord_2667843) baseStart_2667843 baseEnd_2667843 := by
    simpa [prefixWord, tailWord_2667843, baseEnd_2667843] using wordTrace_append hprefix tailTrace_2667843
  have hstable : (prefixWord ++ tailWord_2667843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667843).length < 2 ^ (prefixWord ++ tailWord_2667843).sum := by decide
  have hdescent : baseEnd_2667843 < baseStart_2667843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667860 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2667860 : Nat := 118140960795 + 2667860 * 2 ^ 59
def prefixEnd_2667860 : Nat := 4983230072969 + 3 ^ 40 * 2667860 * 2
def baseEnd_2667860 : Nat := 152210499878226357686749

theorem tailTrace_2667860 : CollatzResearch.WordTrace tailWord_2667860 prefixEnd_2667860 152210499878226357686749 := by
  unfold tailWord_2667860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48652424057403164529108517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64869898743204219372144689 48652424057403164529108517)
  ·
    refine ⟨9122329510763093349207847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48652424057403164529108517 9122329510763093349207847)
    ·
      refine ⟨13683494266144640023811771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9122329510763093349207847 13683494266144640023811771)
      ·
        refine ⟨20525241399216960035717657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13683494266144640023811771 20525241399216960035717657)
        ·
          refine ⟨15393931049412720026788243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20525241399216960035717657 15393931049412720026788243)
          ·
            refine ⟨23090896574119080040182365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15393931049412720026788243 23090896574119080040182365)
            ·
              refine ⟨8659086215294655015068387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23090896574119080040182365 8659086215294655015068387)
              ·
                refine ⟨12988629322941982522602581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659086215294655015068387 12988629322941982522602581)
                ·
                  refine ⟨152210499878226357686749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12988629322941982522602581 152210499878226357686749)
                  ·
                    rfl

theorem cell23_2667860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2667860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667860 prefixEnd_2667860 := by exact prefixLift 2667860
  have htrace : WordTrace (prefixWord ++ tailWord_2667860) baseStart_2667860 baseEnd_2667860 := by
    simpa [prefixWord, tailWord_2667860, baseEnd_2667860] using wordTrace_append hprefix tailTrace_2667860
  have hstable : (prefixWord ++ tailWord_2667860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667860).length < 2 ^ (prefixWord ++ tailWord_2667860).sum := by decide
  have hdescent : baseEnd_2667860 < baseStart_2667860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667877 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 6]
def baseStart_2667877 : Nat := 118140960795 + 2667877 * 2 ^ 59
def prefixEnd_2667877 : Nat := 4983230072969 + 3 ^ 40 * 2667877 * 2
def baseEnd_2667877 : Nat := 152211469786129294740907

theorem tailTrace_2667877 : CollatzResearch.WordTrace tailWord_2667877 prefixEnd_2667877 152211469786129294740907 := by
  unfold tailWord_2667877
  simp only [CollatzResearch.WordTrace]
  refine ⟨97305468155744740961585885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64870312103829827307723923 97305468155744740961585885)
  ·
    refine ⟨36489550558404277860594707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97305468155744740961585885 36489550558404277860594707)
    ·
      refine ⟨54734325837606416790892061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36489550558404277860594707 54734325837606416790892061)
      ·
        refine ⟨20525372189102406296584523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54734325837606416790892061 20525372189102406296584523)
        ·
          refine ⟨30788058283653609444876785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20525372189102406296584523 30788058283653609444876785)
          ·
            refine ⟨23091043712740207083657589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30788058283653609444876785 23091043712740207083657589)
            ·
              refine ⟨2164785348069394414092899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23091043712740207083657589 2164785348069394414092899)
              ·
                refine ⟨3247178022104091621139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164785348069394414092899 3247178022104091621139349)
                ·
                  refine ⟨152211469786129294740907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3247178022104091621139349 152211469786129294740907)
                  ·
                    rfl

theorem cell23_2667877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_2667877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667877 prefixEnd_2667877 := by exact prefixLift 2667877
  have htrace : WordTrace (prefixWord ++ tailWord_2667877) baseStart_2667877 baseEnd_2667877 := by
    simpa [prefixWord, tailWord_2667877, baseEnd_2667877] using wordTrace_append hprefix tailTrace_2667877
  have hstable : (prefixWord ++ tailWord_2667877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667877).length < 2 ^ (prefixWord ++ tailWord_2667877).sum := by decide
  have hdescent : baseEnd_2667877 < baseStart_2667877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667887 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_2667887 : Nat := 118140960795 + 2667887 * 2 ^ 59
def prefixEnd_2667887 : Nat := 4983230072969 + 3 ^ 40 * 2667887 * 2
def baseEnd_2667887 : Nat := 1369908362881708613543117

theorem tailTrace_2667887 : CollatzResearch.WordTrace tailWord_2667887 prefixEnd_2667887 1369908362881708613543117 := by
  unfold tailWord_2667887
  simp only [CollatzResearch.WordTrace]
  refine ⟨97305832885708512669449915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64870555257139008446299943 97305832885708512669449915)
  ·
    refine ⟨145958749328562769004174873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97305832885708512669449915 145958749328562769004174873)
    ·
      refine ⟨109469061996422076753131155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145958749328562769004174873 109469061996422076753131155)
      ·
        refine ⟨164203592994633115129696733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109469061996422076753131155 164203592994633115129696733)
        ·
          refine ⟨61576347372987418173636275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164203592994633115129696733 61576347372987418173636275)
          ·
            refine ⟨92364521059481127260454413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61576347372987418173636275 92364521059481127260454413)
            ·
              refine ⟨34636695397305422722670405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92364521059481127260454413 34636695397305422722670405)
              ·
                refine ⟨6494380386994766760500701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34636695397305422722670405 6494380386994766760500701)
                ·
                  refine ⟨2435392645123037535187763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6494380386994766760500701 2435392645123037535187763)
                  ·
                    refine ⟨3653088967684556302781645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435392645123037535187763 3653088967684556302781645)
                    ·
                      refine ⟨1369908362881708613543117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653088967684556302781645 1369908362881708613543117)
                      ·
                        rfl

theorem cell23_2667887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_2667887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667887 prefixEnd_2667887 := by exact prefixLift 2667887
  have htrace : WordTrace (prefixWord ++ tailWord_2667887) baseStart_2667887 baseEnd_2667887 := by
    simpa [prefixWord, tailWord_2667887, baseEnd_2667887] using wordTrace_append hprefix tailTrace_2667887
  have hstable : (prefixWord ++ tailWord_2667887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667887).length < 2 ^ (prefixWord ++ tailWord_2667887).sum := by decide
  have hdescent : baseEnd_2667887 < baseStart_2667887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667897 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 5, 2]
def baseStart_2667897 : Nat := 118140960795 + 2667897 * 2 ^ 59
def prefixEnd_2667897 : Nat := 4983230072969 + 3 ^ 40 * 2667897 * 2
def baseEnd_2667897 : Nat := 1369913497688253574418071

theorem tailTrace_2667897 : CollatzResearch.WordTrace tailWord_2667897 prefixEnd_2667897 1369913497688253574418071 := by
  unfold tailWord_2667897
  simp only [CollatzResearch.WordTrace]
  refine ⟨97306197615672284377313945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64870798410448189584875963 97306197615672284377313945)
  ·
    refine ⟨72979648211754213282985459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97306197615672284377313945 72979648211754213282985459)
    ·
      refine ⟨109469472317631319924478189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72979648211754213282985459 109469472317631319924478189)
      ·
        refine ⟨41051052119111744971679321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109469472317631319924478189 41051052119111744971679321)
        ·
          refine ⟨30788289089333808728759491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41051052119111744971679321 30788289089333808728759491)
          ·
            refine ⟨46182433634000713093139237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30788289089333808728759491 46182433634000713093139237)
            ·
              refine ⟨8659206306375133704963607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46182433634000713093139237 8659206306375133704963607)
              ·
                refine ⟨12988809459562700557445411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8659206306375133704963607 12988809459562700557445411)
                ·
                  refine ⟨19483214189344050836168117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12988809459562700557445411 19483214189344050836168117)
                  ·
                    refine ⟨1826551330251004765890761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19483214189344050836168117 1826551330251004765890761)
                    ·
                      refine ⟨1369913497688253574418071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826551330251004765890761 1369913497688253574418071)
                      ·
                        rfl

theorem cell23_2667897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_2667897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667897 prefixEnd_2667897 := by exact prefixLift 2667897
  have htrace : WordTrace (prefixWord ++ tailWord_2667897) baseStart_2667897 baseEnd_2667897 := by
    simpa [prefixWord, tailWord_2667897, baseEnd_2667897] using wordTrace_append hprefix tailTrace_2667897
  have hstable : (prefixWord ++ tailWord_2667897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667897).length < 2 ^ (prefixWord ++ tailWord_2667897).sum := by decide
  have hdescent : baseEnd_2667897 < baseStart_2667897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667907 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 1, 5]
def baseStart_2667907 : Nat := 118140960795 + 2667907 * 2 ^ 59
def prefixEnd_2667907 : Nat := 4983230072969 + 3 ^ 40 * 2667907 * 2
def baseEnd_2667907 : Nat := 456639544164932845097675

theorem tailTrace_2667907 : CollatzResearch.WordTrace tailWord_2667907 prefixEnd_2667907 456639544164932845097675 := by
  unfold tailWord_2667907
  simp only [CollatzResearch.WordTrace]
  refine ⟨97306562345636056085177975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64871041563757370723451983 97306562345636056085177975)
  ·
    refine ⟨145959843518454084127766963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97306562345636056085177975 145959843518454084127766963)
    ·
      refine ⟨218939765277681126191650445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145959843518454084127766963 218939765277681126191650445)
      ·
        refine ⟨82102411979130422321868917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218939765277681126191650445 82102411979130422321868917)
        ·
          refine ⟨7697101123043477092675211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82102411979130422321868917 7697101123043477092675211)
          ·
            refine ⟨11545651684565215639012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697101123043477092675211 11545651684565215639012817)
            ·
              refine ⟨8659238763423911729259613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11545651684565215639012817 8659238763423911729259613)
              ·
                refine ⟨3247214536283966898472355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8659238763423911729259613 3247214536283966898472355)
                ·
                  refine ⟨4870821804425950347708533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247214536283966898472355 4870821804425950347708533)
                  ·
                    refine ⟨456639544164932845097675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4870821804425950347708533 456639544164932845097675)
                    ·
                      rfl

theorem cell23_2667907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 5].length) (baseStart_2667907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667907 prefixEnd_2667907 := by exact prefixLift 2667907
  have htrace : WordTrace (prefixWord ++ tailWord_2667907) baseStart_2667907 baseEnd_2667907 := by
    simpa [prefixWord, tailWord_2667907, baseEnd_2667907] using wordTrace_append hprefix tailTrace_2667907
  have hstable : (prefixWord ++ tailWord_2667907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667907).length < 2 ^ (prefixWord ++ tailWord_2667907).sum := by decide
  have hdescent : baseEnd_2667907 < baseStart_2667907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667957 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2667957 : Nat := 118140960795 + 2667957 * 2 ^ 59
def prefixEnd_2667957 : Nat := 4983230072969 + 3 ^ 40 * 2667957 * 2
def baseEnd_2667957 : Nat := 1369944306527523339667795

theorem tailTrace_2667957 : CollatzResearch.WordTrace tailWord_2667957 prefixEnd_2667957 1369944306527523339667795 := by
  unfold tailWord_2667957
  simp only [CollatzResearch.WordTrace]
  refine ⟨97308385995454914624498125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64872257330303276416332083 97308385995454914624498125)
  ·
    refine ⟨36490644748295592984186797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97308385995454914624498125 36490644748295592984186797)
    ·
      refine ⟨13683991780610847369070049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36490644748295592984186797 13683991780610847369070049)
      ·
        refine ⟨10262993835458135526802537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13683991780610847369070049 10262993835458135526802537)
        ·
          refine ⟨7697245376593601645101903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10262993835458135526802537 7697245376593601645101903)
          ·
            refine ⟨11545868064890402467652855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7697245376593601645101903 11545868064890402467652855)
            ·
              refine ⟨17318802097335603701479283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11545868064890402467652855 17318802097335603701479283)
              ·
                refine ⟨25978203146003405552218925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17318802097335603701479283 25978203146003405552218925)
                ·
                  refine ⟨9741826179751277082082097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25978203146003405552218925 9741826179751277082082097)
                  ·
                    refine ⟨7306369634813457811561573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9741826179751277082082097 7306369634813457811561573)
                    ·
                      refine ⟨1369944306527523339667795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7306369634813457811561573 1369944306527523339667795)
                      ·
                        rfl

theorem cell23_2667957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2667957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667957 prefixEnd_2667957 := by exact prefixLift 2667957
  have htrace : WordTrace (prefixWord ++ tailWord_2667957) baseStart_2667957 baseEnd_2667957 := by
    simpa [prefixWord, tailWord_2667957, baseEnd_2667957] using wordTrace_append hprefix tailTrace_2667957
  have hstable : (prefixWord ++ tailWord_2667957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667957).length < 2 ^ (prefixWord ++ tailWord_2667957).sum := by decide
  have hdescent : baseEnd_2667957 < baseStart_2667957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667961 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2667961 : Nat := 118140960795 + 2667961 * 2 ^ 59
def prefixEnd_2667961 : Nat := 4983230072969 + 3 ^ 40 * 2667961 * 2
def baseEnd_2667961 : Nat := 1369946360450141324017777

theorem tailTrace_2667961 : CollatzResearch.WordTrace tailWord_2667961 prefixEnd_2667961 1369946360450141324017777 := by
  unfold tailWord_2667961
  simp only [CollatzResearch.WordTrace]
  refine ⟨97308531887440423307643737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64872354591626948871762491 97308531887440423307643737)
  ·
    refine ⟨72981398915580317480732803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97308531887440423307643737 72981398915580317480732803)
    ·
      refine ⟨109472098373370476221099205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72981398915580317480732803 109472098373370476221099205)
      ·
        refine ⟨20526018445006964291456101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109472098373370476221099205 20526018445006964291456101)
        ·
          refine ⟨3848628458438805804648019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20526018445006964291456101 3848628458438805804648019)
          ·
            refine ⟨5772942687658208706972029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848628458438805804648019 5772942687658208706972029)
            ·
              refine ⟨2164853507871828265114511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5772942687658208706972029 2164853507871828265114511)
              ·
                refine ⟨3247280261807742397671767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164853507871828265114511 3247280261807742397671767)
                ·
                  refine ⟨4870920392711613596507651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247280261807742397671767 4870920392711613596507651)
                  ·
                    refine ⟨7306380589067420394761477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4870920392711613596507651 7306380589067420394761477)
                    ·
                      refine ⟨1369946360450141324017777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7306380589067420394761477 1369946360450141324017777)
                      ·
                        rfl

theorem cell23_2667961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2667961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667961 prefixEnd_2667961 := by exact prefixLift 2667961
  have htrace : WordTrace (prefixWord ++ tailWord_2667961) baseStart_2667961 baseEnd_2667961 := by
    simpa [prefixWord, tailWord_2667961, baseEnd_2667961] using wordTrace_append hprefix tailTrace_2667961
  have hstable : (prefixWord ++ tailWord_2667961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667961).length < 2 ^ (prefixWord ++ tailWord_2667961).sum := by decide
  have hdescent : baseEnd_2667961 < baseStart_2667961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667978 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_2667978 : Nat := 118140960795 + 2667978 * 2 ^ 59
def prefixEnd_2667978 : Nat := 4983230072969 + 3 ^ 40 * 2667978 * 2
def baseEnd_2667978 : Nat := 1369955089621267757505199

theorem tailTrace_2667978 : CollatzResearch.WordTrace tailWord_2667978 prefixEnd_2667978 1369955089621267757505199 := by
  unfold tailWord_2667978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24327287982094708802753147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64872767952252556807341725 24327287982094708802753147)
  ·
    refine ⟨36490931973142063204129721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24327287982094708802753147 36490931973142063204129721)
    ·
      refine ⟨27368198979856547403097291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36490931973142063204129721 27368198979856547403097291)
      ·
        refine ⟨41052298469784821104645937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27368198979856547403097291 41052298469784821104645937)
        ·
          refine ⟨30789223852338615828484453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41052298469784821104645937 30789223852338615828484453)
          ·
            refine ⟨5772979472313490467840835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30789223852338615828484453 5772979472313490467840835)
            ·
              refine ⟨8659469208470235701761253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772979472313490467840835 8659469208470235701761253)
              ·
                refine ⟨1623650476588169194080235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8659469208470235701761253 1623650476588169194080235)
                ·
                  refine ⟨2435475714882253791120353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623650476588169194080235 2435475714882253791120353)
                  ·
                    refine ⟨1826606786161690343340265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435475714882253791120353 1826606786161690343340265)
                    ·
                      refine ⟨1369955089621267757505199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826606786161690343340265 1369955089621267757505199)
                      ·
                        rfl

theorem cell23_2667978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_2667978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667978 prefixEnd_2667978 := by exact prefixLift 2667978
  have htrace : WordTrace (prefixWord ++ tailWord_2667978) baseStart_2667978 baseEnd_2667978 := by
    simpa [prefixWord, tailWord_2667978, baseEnd_2667978] using wordTrace_append hprefix tailTrace_2667978
  have hstable : (prefixWord ++ tailWord_2667978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667978).length < 2 ^ (prefixWord ++ tailWord_2667978).sum := by decide
  have hdescent : baseEnd_2667978 < baseStart_2667978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2667994 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2667994 : Nat := 118140960795 + 2667994 * 2 ^ 59
def prefixEnd_2667994 : Nat := 4983230072969 + 3 ^ 40 * 2667994 * 2
def baseEnd_2667994 : Nat := 1369963305311739694905125

theorem tailTrace_2667994 : CollatzResearch.WordTrace tailWord_2667994 prefixEnd_2667994 1369963305311739694905125 := by
  unfold tailWord_2667994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24327433874080217485898759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64873156997547246629063357 24327433874080217485898759)
  ·
    refine ⟨36491150811120326228848139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24327433874080217485898759 36491150811120326228848139)
    ·
      refine ⟨54736726216680489343272209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36491150811120326228848139 54736726216680489343272209)
      ·
        refine ⟨41052544662510367007454157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54736726216680489343272209 41052544662510367007454157)
        ·
          refine ⟨15394704248441387627795309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41052544662510367007454157 15394704248441387627795309)
          ·
            refine ⟨5773014093165520360423241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15394704248441387627795309 5773014093165520360423241)
            ·
              refine ⟨4329760569874140270317431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773014093165520360423241 4329760569874140270317431)
              ·
                refine ⟨6494640854811210405476147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329760569874140270317431 6494640854811210405476147)
                ·
                  refine ⟨9741961282216815608214221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494640854811210405476147 9741961282216815608214221)
                  ·
                    refine ⟨3653235480831305853080333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9741961282216815608214221 3653235480831305853080333)
                    ·
                      refine ⟨1369963305311739694905125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653235480831305853080333 1369963305311739694905125)
                      ·
                        rfl

theorem cell23_2667994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2667994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2667994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2667994 prefixEnd_2667994 := by exact prefixLift 2667994
  have htrace : WordTrace (prefixWord ++ tailWord_2667994) baseStart_2667994 baseEnd_2667994 := by
    simpa [prefixWord, tailWord_2667994, baseEnd_2667994] using wordTrace_append hprefix tailTrace_2667994
  have hstable : (prefixWord ++ tailWord_2667994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2667994).length < 2 ^ (prefixWord ++ tailWord_2667994).sum := by decide
  have hdescent : baseEnd_2667994 < baseStart_2667994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2667994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668045 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2668045 : Nat := 118140960795 + 2668045 * 2 ^ 59
def prefixEnd_2668045 : Nat := 4983230072969 + 3 ^ 40 * 2668045 * 2
def baseEnd_2668045 : Nat := 1369989492825118995367391

theorem tailTrace_2668045 : CollatzResearch.WordTrace tailWord_2668045 prefixEnd_2668045 1369989492825118995367391 := by
  unfold tailWord_2668045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97311595619136105653701589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64874397079424070435801059 97311595619136105653701589)
  ·
    refine ⟨2280740522323502476258631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97311595619136105653701589 2280740522323502476258631)
    ·
      refine ⟨3421110783485253714387947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280740522323502476258631 3421110783485253714387947)
      ·
        refine ⟨5131666175227880571581921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421110783485253714387947 5131666175227880571581921)
        ·
          refine ⟨3848749631420910428686441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5131666175227880571581921 3848749631420910428686441)
          ·
            refine ⟨2886562223565682821514831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848749631420910428686441 2886562223565682821514831)
            ·
              refine ⟨4329843335348524232272247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886562223565682821514831 4329843335348524232272247)
              ·
                refine ⟨6494765003022786348408371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329843335348524232272247 6494765003022786348408371)
                ·
                  refine ⟨9742147504534179522612557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494765003022786348408371 9742147504534179522612557)
                  ·
                    refine ⟨3653305314200317320979709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9742147504534179522612557 3653305314200317320979709)
                    ·
                      refine ⟨1369989492825118995367391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653305314200317320979709 1369989492825118995367391)
                      ·
                        rfl

theorem cell23_2668045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2668045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668045 prefixEnd_2668045 := by exact prefixLift 2668045
  have htrace : WordTrace (prefixWord ++ tailWord_2668045) baseStart_2668045 baseEnd_2668045 := by
    simpa [prefixWord, tailWord_2668045, baseEnd_2668045] using wordTrace_append hprefix tailTrace_2668045
  have hstable : (prefixWord ++ tailWord_2668045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668045).length < 2 ^ (prefixWord ++ tailWord_2668045).sum := by decide
  have hdescent : baseEnd_2668045 < baseStart_2668045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668051 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 4, 2]
def baseStart_2668051 : Nat := 118140960795 + 2668051 * 2 ^ 59
def prefixEnd_2668051 : Nat := 4983230072969 + 3 ^ 40 * 2668051 * 2
def baseEnd_2668051 : Nat := 1369992573709045971892363

theorem tailTrace_2668051 : CollatzResearch.WordTrace tailWord_2668051 prefixEnd_2668051 1369992573709045971892363 := by
  unfold tailWord_2668051
  simp only [CollatzResearch.WordTrace]
  refine ⟨97311814457114368678420007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64874542971409579118946671 97311814457114368678420007)
  ·
    refine ⟨145967721685671553017630011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97311814457114368678420007 145967721685671553017630011)
    ·
      refine ⟨218951582528507329526445017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145967721685671553017630011 218951582528507329526445017)
      ·
        refine ⟨164213686896380497144833763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218951582528507329526445017 164213686896380497144833763)
        ·
          refine ⟨246320530344570745717250645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164213686896380497144833763 246320530344570745717250645)
          ·
            refine ⟨2886568714975438426374031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 246320530344570745717250645 2886568714975438426374031)
            ·
              refine ⟨4329853072463157639561047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886568714975438426374031 4329853072463157639561047)
              ·
                refine ⟨6494779608694736459341571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4329853072463157639561047 6494779608694736459341571)
                ·
                  refine ⟨9742169413042104689012357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6494779608694736459341571 9742169413042104689012357)
                  ·
                    refine ⟨1826656764945394629189817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9742169413042104689012357 1826656764945394629189817)
                    ·
                      refine ⟨1369992573709045971892363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826656764945394629189817 1369992573709045971892363)
                      ·
                        rfl

theorem cell23_2668051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4, 2].length) (baseStart_2668051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668051 prefixEnd_2668051 := by exact prefixLift 2668051
  have htrace : WordTrace (prefixWord ++ tailWord_2668051) baseStart_2668051 baseEnd_2668051 := by
    simpa [prefixWord, tailWord_2668051, baseEnd_2668051] using wordTrace_append hprefix tailTrace_2668051
  have hstable : (prefixWord ++ tailWord_2668051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668051).length < 2 ^ (prefixWord ++ tailWord_2668051).sum := by decide
  have hdescent : baseEnd_2668051 < baseStart_2668051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668087 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 4, 5]
def baseStart_2668087 : Nat := 118140960795 + 2668087 * 2 ^ 59
def prefixEnd_2668087 : Nat := 4983230072969 + 3 ^ 40 * 2668087 * 2
def baseEnd_2668087 : Nat := 456670353004202610347399

theorem tailTrace_2668087 : CollatzResearch.WordTrace tailWord_2668087 prefixEnd_2668087 456670353004202610347399 := by
  unfold tailWord_2668087
  simp only [CollatzResearch.WordTrace]
  refine ⟨97313127484983946826730515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64875418323322631217820343 97313127484983946826730515)
  ·
    refine ⟨145969691227475920240095773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97313127484983946826730515 145969691227475920240095773)
    ·
      refine ⟨54738634210303470090035915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145969691227475920240095773 54738634210303470090035915)
      ·
        refine ⟨82107951315455205135053873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54738634210303470090035915 82107951315455205135053873)
        ·
          refine ⟨61580963486591403851290405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82107951315455205135053873 61580963486591403851290405)
          ·
            refine ⟨11546430653735888222116951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61580963486591403851290405 11546430653735888222116951)
            ·
              refine ⟨17319645980603832333175427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11546430653735888222116951 17319645980603832333175427)
              ·
                refine ⟨25979468970905748499763141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17319645980603832333175427 25979468970905748499763141)
                ·
                  refine ⟨4871150432044827843705589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25979468970905748499763141 4871150432044827843705589)
                  ·
                    refine ⟨456670353004202610347399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4871150432044827843705589 456670353004202610347399)
                    ·
                      rfl

theorem cell23_2668087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_2668087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668087 prefixEnd_2668087 := by exact prefixLift 2668087
  have htrace : WordTrace (prefixWord ++ tailWord_2668087) baseStart_2668087 baseEnd_2668087 := by
    simpa [prefixWord, tailWord_2668087, baseEnd_2668087] using wordTrace_append hprefix tailTrace_2668087
  have hstable : (prefixWord ++ tailWord_2668087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668087).length < 2 ^ (prefixWord ++ tailWord_2668087).sum := by decide
  have hdescent : baseEnd_2668087 < baseStart_2668087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668102 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2668102 : Nat := 118140960795 + 2668102 * 2 ^ 59
def prefixEnd_2668102 : Nat := 4983230072969 + 3 ^ 40 * 2668102 * 2
def baseEnd_2668102 : Nat := 1370018761222425272354629

theorem tailTrace_2668102 : CollatzResearch.WordTrace tailWord_2668102 prefixEnd_2668102 1370018761222425272354629 := by
  unfold tailWord_2668102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3041052330622800137141455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64875783053286402925684373 3041052330622800137141455)
  ·
    refine ⟨4561578495934200205712183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3041052330622800137141455 4561578495934200205712183)
    ·
      refine ⟨6842367743901300308568275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561578495934200205712183 6842367743901300308568275)
      ·
        refine ⟨10263551615851950462852413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842367743901300308568275 10263551615851950462852413)
        ·
          refine ⟨3848831855944481423569655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10263551615851950462852413 3848831855944481423569655)
          ·
            refine ⟨5773247783916722135354483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848831855944481423569655 5773247783916722135354483)
            ·
              refine ⟨8659871675875083203031725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5773247783916722135354483 8659871675875083203031725)
              ·
                refine ⟨3247451878453156201136897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8659871675875083203031725 3247451878453156201136897)
                ·
                  refine ⟨2435588908839867150852673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247451878453156201136897 2435588908839867150852673)
                  ·
                    refine ⟨1826691681629900363139505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435588908839867150852673 1826691681629900363139505)
                    ·
                      refine ⟨1370018761222425272354629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826691681629900363139505 1370018761222425272354629)
                      ·
                        rfl

theorem cell23_2668102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2668102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668102 prefixEnd_2668102 := by exact prefixLift 2668102
  have htrace : WordTrace (prefixWord ++ tailWord_2668102) baseStart_2668102 baseEnd_2668102 := by
    simpa [prefixWord, tailWord_2668102, baseEnd_2668102] using wordTrace_append hprefix tailTrace_2668102
  have hstable : (prefixWord ++ tailWord_2668102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668102).length < 2 ^ (prefixWord ++ tailWord_2668102).sum := by decide
  have hdescent : baseEnd_2668102 < baseStart_2668102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668107 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4]
def baseStart_2668107 : Nat := 118140960795 + 2668107 * 2 ^ 59
def prefixEnd_2668107 : Nat := 4983230072969 + 3 ^ 40 * 2668107 * 2
def baseEnd_2668107 : Nat := 1370021328625697752792105

theorem tailTrace_2668107 : CollatzResearch.WordTrace tailWord_2668107 prefixEnd_2668107 1370021328625697752792105 := by
  unfold tailWord_2668107
  simp only [CollatzResearch.WordTrace]
  refine ⟨97313856944911490242458575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64875904629940993494972383 97313856944911490242458575)
  ·
    refine ⟨145970785417367235363687863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97313856944911490242458575 145970785417367235363687863)
    ·
      refine ⟨218956178126050853045531795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145970785417367235363687863 218956178126050853045531795)
      ·
        refine ⟨328434267189076279568297693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218956178126050853045531795 328434267189076279568297693)
        ·
          refine ⟨123162850195903604838111635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328434267189076279568297693 123162850195903604838111635)
          ·
            refine ⟨184744275293855407257167453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123162850195903604838111635 184744275293855407257167453)
            ·
              refine ⟨69279103235195777721437795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184744275293855407257167453 69279103235195777721437795)
              ·
                refine ⟨103918654852793666582156693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69279103235195777721437795 103918654852793666582156693)
                ·
                  refine ⟨4871186946224703121038595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103918654852793666582156693 4871186946224703121038595)
                  ·
                    refine ⟨7306780419337054681557893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871186946224703121038595 7306780419337054681557893)
                    ·
                      refine ⟨1370021328625697752792105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7306780419337054681557893 1370021328625697752792105)
                      ·
                        rfl

theorem cell23_2668107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_2668107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668107 prefixEnd_2668107 := by exact prefixLift 2668107
  have htrace : WordTrace (prefixWord ++ tailWord_2668107) baseStart_2668107 baseEnd_2668107 := by
    simpa [prefixWord, tailWord_2668107, baseEnd_2668107] using wordTrace_append hprefix tailTrace_2668107
  have hstable : (prefixWord ++ tailWord_2668107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668107).length < 2 ^ (prefixWord ++ tailWord_2668107).sum := by decide
  have hdescent : baseEnd_2668107 < baseStart_2668107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668168 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_2668168 : Nat := 118140960795 + 2668168 * 2 ^ 59
def prefixEnd_2668168 : Nat := 4983230072969 + 3 ^ 40 * 2668168 * 2
def baseEnd_2668168 : Nat := 456684216981874004709775

theorem tailTrace_2668168 : CollatzResearch.WordTrace tailWord_2668168 prefixEnd_2668168 456684216981874004709775 := by
  unfold tailWord_2668168
  simp only [CollatzResearch.WordTrace]
  refine ⟨48658040898845248830214579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64877387865126998440286105 48658040898845248830214579)
  ·
    refine ⟨72987061348267873245321869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48658040898845248830214579 72987061348267873245321869)
    ·
      refine ⟨27370148005600452466995701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72987061348267873245321869 27370148005600452466995701)
      ·
        refine ⟨2565951375525042418780847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27370148005600452466995701 2565951375525042418780847)
        ·
          refine ⟨3848927063287563628171271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565951375525042418780847 3848927063287563628171271)
          ·
            refine ⟨5773390594931345442256907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848927063287563628171271 5773390594931345442256907)
            ·
              refine ⟨8660085892397018163385361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5773390594931345442256907 8660085892397018163385361)
              ·
                refine ⟨6495064419297763622539021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8660085892397018163385361 6495064419297763622539021)
                ·
                  refine ⟨2435649157236661358452133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6495064419297763622539021 2435649157236661358452133)
                  ·
                    refine ⟨456684216981874004709775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2435649157236661358452133 456684216981874004709775)
                    ·
                      rfl

theorem cell23_2668168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_2668168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668168 prefixEnd_2668168 := by exact prefixLift 2668168
  have htrace : WordTrace (prefixWord ++ tailWord_2668168) baseStart_2668168 baseEnd_2668168 := by
    simpa [prefixWord, tailWord_2668168, baseEnd_2668168] using wordTrace_append hprefix tailTrace_2668168
  have hstable : (prefixWord ++ tailWord_2668168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668168).length < 2 ^ (prefixWord ++ tailWord_2668168).sum := by decide
  have hdescent : baseEnd_2668168 < baseStart_2668168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668208 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 1, 1, 3]
def baseStart_2668208 : Nat := 118140960795 + 2668208 * 2 ^ 59
def prefixEnd_2668208 : Nat := 4983230072969 + 3 ^ 40 * 2668208 * 2
def baseEnd_2668208 : Nat := 1370073190171801857629141

theorem tailTrace_2668208 : CollatzResearch.WordTrace tailWord_2668208 prefixEnd_2668208 1370073190171801857629141 := by
  unfold tailWord_2668208
  simp only [CollatzResearch.WordTrace]
  refine ⟨48658770358772792245942639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64878360478363722994590185 48658770358772792245942639)
  ·
    refine ⟨72988155538159188368913959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48658770358772792245942639 72988155538159188368913959)
    ·
      refine ⟨109482233307238782553370939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72988155538159188368913959 109482233307238782553370939)
      ·
        refine ⟨164223349960858173830056409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109482233307238782553370939 164223349960858173830056409)
        ·
          refine ⟨123167512470643630372542307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164223349960858173830056409 123167512470643630372542307)
          ·
            refine ⟨184751268705965445558813461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123167512470643630372542307 184751268705965445558813461)
            ·
              refine ⟨8660215720592130260569381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184751268705965445558813461 8660215720592130260569381)
              ·
                refine ⟨1623790447611024423856759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8660215720592130260569381 1623790447611024423856759)
                ·
                  refine ⟨2435685671416536635785139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623790447611024423856759 2435685671416536635785139)
                  ·
                    refine ⟨3653528507124804953677709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435685671416536635785139 3653528507124804953677709)
                    ·
                      refine ⟨1370073190171801857629141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653528507124804953677709 1370073190171801857629141)
                      ·
                        rfl

theorem cell23_2668208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 1, 3].length) (baseStart_2668208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668208 prefixEnd_2668208 := by exact prefixLift 2668208
  have htrace : WordTrace (prefixWord ++ tailWord_2668208) baseStart_2668208 baseEnd_2668208 := by
    simpa [prefixWord, tailWord_2668208, baseEnd_2668208] using wordTrace_append hprefix tailTrace_2668208
  have hstable : (prefixWord ++ tailWord_2668208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668208).length < 2 ^ (prefixWord ++ tailWord_2668208).sum := by decide
  have hdescent : baseEnd_2668208 < baseStart_2668208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668231 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2668231 : Nat := 118140960795 + 2668231 * 2 ^ 59
def prefixEnd_2668231 : Nat := 4983230072969 + 3 ^ 40 * 2668231 * 2
def baseEnd_2668231 : Nat := 1370085000226855267641535

theorem tailTrace_2668231 : CollatzResearch.WordTrace tailWord_2668231 prefixEnd_2668231 1370085000226855267641535 := by
  unfold tailWord_2668231
  simp only [CollatzResearch.WordTrace]
  refine ⟨97318379596462259419972547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64878919730974839613315031 97318379596462259419972547)
  ·
    refine ⟨145977569394693389129958821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97318379596462259419972547 145977569394693389129958821)
    ·
      refine ⟨27370794261505010461867279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145977569394693389129958821 27370794261505010461867279)
      ·
        refine ⟨41056191392257515692800919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27370794261505010461867279 41056191392257515692800919)
        ·
          refine ⟨61584287088386273539201379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41056191392257515692800919 61584287088386273539201379)
          ·
            refine ⟨92376430632579410308802069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61584287088386273539201379 92376430632579410308802069)
            ·
              refine ⟨4330145185902159858225097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92376430632579410308802069 4330145185902159858225097)
              ·
                refine ⟨3247608889426619893668823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330145185902159858225097 3247608889426619893668823)
                ·
                  refine ⟨4871413334139929840503235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3247608889426619893668823 4871413334139929840503235)
                  ·
                    refine ⟨7307120001209894760754853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871413334139929840503235 7307120001209894760754853)
                    ·
                      refine ⟨1370085000226855267641535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7307120001209894760754853 1370085000226855267641535)
                      ·
                        rfl

theorem cell23_2668231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2668231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668231 prefixEnd_2668231 := by exact prefixLift 2668231
  have htrace : WordTrace (prefixWord ++ tailWord_2668231) baseStart_2668231 baseEnd_2668231 := by
    simpa [prefixWord, tailWord_2668231, baseEnd_2668231] using wordTrace_append hprefix tailTrace_2668231
  have hstable : (prefixWord ++ tailWord_2668231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668231).length < 2 ^ (prefixWord ++ tailWord_2668231).sum := by decide
  have hdescent : baseEnd_2668231 < baseStart_2668231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668242 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2668242 : Nat := 118140960795 + 2668242 * 2 ^ 59
def prefixEnd_2668242 : Nat := 4983230072969 + 3 ^ 40 * 2668242 * 2
def baseEnd_2668242 : Nat := 1370090648514054724603985

theorem tailTrace_2668242 : CollatzResearch.WordTrace tailWord_2668242 prefixEnd_2668242 1370090648514054724603985 := by
  unfold tailWord_2668242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329695199855602074655745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64879187199614938865748653 24329695199855602074655745)
  ·
    refine ⟨18247271399891701555991809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24329695199855602074655745 18247271399891701555991809)
    ·
      refine ⟨13685453549918776166993857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18247271399891701555991809 13685453549918776166993857)
      ·
        refine ⟨10264090162439082125245393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13685453549918776166993857 10264090162439082125245393)
        ·
          refine ⟨7698067621829311593934045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10264090162439082125245393 7698067621829311593934045)
          ·
            refine ⟨2886775358185991847725267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7698067621829311593934045 2886775358185991847725267)
            ·
              refine ⟨4330163037278987771587901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886775358185991847725267 4330163037278987771587901)
              ·
                refine ⟨1623811138979620414345463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4330163037278987771587901 1623811138979620414345463)
                ·
                  refine ⟨2435716708469430621518195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623811138979620414345463 2435716708469430621518195)
                  ·
                    refine ⟨3653575062704145932277293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435716708469430621518195 3653575062704145932277293)
                    ·
                      refine ⟨1370090648514054724603985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653575062704145932277293 1370090648514054724603985)
                      ·
                        rfl

theorem cell23_2668242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2668242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668242 prefixEnd_2668242 := by exact prefixLift 2668242
  have htrace : WordTrace (prefixWord ++ tailWord_2668242) baseStart_2668242 baseEnd_2668242 := by
    simpa [prefixWord, tailWord_2668242, baseEnd_2668242] using wordTrace_append hprefix tailTrace_2668242
  have hstable : (prefixWord ++ tailWord_2668242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668242).length < 2 ^ (prefixWord ++ tailWord_2668242).sum := by decide
  have hdescent : baseEnd_2668242 < baseStart_2668242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668274 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2668274 : Nat := 118140960795 + 2668274 * 2 ^ 59
def prefixEnd_2668274 : Nat := 4983230072969 + 3 ^ 40 * 2668274 * 2
def baseEnd_2668274 : Nat := 1370107079894998599403837

theorem tailTrace_2668274 : CollatzResearch.WordTrace tailWord_2668274 prefixEnd_2668274 1370107079894998599403837 := by
  unfold tailWord_2668274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329986983826619440946969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64879965290204318509191917 24329986983826619440946969)
  ·
    refine ⟨18247490237869964580710227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24329986983826619440946969 18247490237869964580710227)
    ·
      refine ⟨27371235356804946871065341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18247490237869964580710227 27371235356804946871065341)
      ·
        refine ⟨10264213258801855076649503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27371235356804946871065341 10264213258801855076649503)
        ·
          refine ⟨15396319888202782614974255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10264213258801855076649503 15396319888202782614974255)
          ·
            refine ⟨23094479832304173922461383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15396319888202782614974255 23094479832304173922461383)
            ·
              refine ⟨34641719748456260883692075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23094479832304173922461383 34641719748456260883692075)
              ·
                refine ⟨51962579622684391325538113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34641719748456260883692075 51962579622684391325538113)
                ·
                  refine ⟨38971934717013293494153585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51962579622684391325538113 38971934717013293494153585)
                  ·
                    refine ⟨29228951037759970120615189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38971934717013293494153585 29228951037759970120615189)
                    ·
                      refine ⟨1370107079894998599403837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29228951037759970120615189 1370107079894998599403837)
                      ·
                        rfl

theorem cell23_2668274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2668274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668274 prefixEnd_2668274 := by exact prefixLift 2668274
  have htrace : WordTrace (prefixWord ++ tailWord_2668274) baseStart_2668274 baseEnd_2668274 := by
    simpa [prefixWord, tailWord_2668274, baseEnd_2668274] using wordTrace_append hprefix tailTrace_2668274
  have hstable : (prefixWord ++ tailWord_2668274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668274).length < 2 ^ (prefixWord ++ tailWord_2668274).sum := by decide
  have hdescent : baseEnd_2668274 < baseStart_2668274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668338 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_2668338 : Nat := 118140960795 + 2668338 * 2 ^ 59
def prefixEnd_2668338 : Nat := 4983230072969 + 3 ^ 40 * 2668338 * 2
def baseEnd_2668338 : Nat := 1370139942656886349003543

theorem tailTrace_2668338 : CollatzResearch.WordTrace tailWord_2668338 prefixEnd_2668338 1370139942656886349003543 := by
  unfold tailWord_2668338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24330570551768654173529417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64881521471383077796078445 24330570551768654173529417)
  ·
    refine ⟨18247927913826490630147063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24330570551768654173529417 18247927913826490630147063)
    ·
      refine ⟨27371891870739735945220595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18247927913826490630147063 27371891870739735945220595)
      ·
        refine ⟨41057837806109603917830893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27371891870739735945220595 41057837806109603917830893)
        ·
          refine ⟨15396689177291101469186585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41057837806109603917830893 15396689177291101469186585)
          ·
            refine ⟨11547516882968326101889939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15396689177291101469186585 11547516882968326101889939)
            ·
              refine ⟨17321275324452489152834909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11547516882968326101889939 17321275324452489152834909)
              ·
                refine ⟨6495478246669683432313091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17321275324452489152834909 6495478246669683432313091)
                ·
                  refine ⟨9743217370004525148469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6495478246669683432313091 9743217370004525148469637)
                  ·
                    refine ⟨1826853256875848465338057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9743217370004525148469637 1826853256875848465338057)
                    ·
                      refine ⟨1370139942656886349003543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826853256875848465338057 1370139942656886349003543)
                      ·
                        rfl

theorem cell23_2668338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_2668338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668338 prefixEnd_2668338 := by exact prefixLift 2668338
  have htrace : WordTrace (prefixWord ++ tailWord_2668338) baseStart_2668338 baseEnd_2668338 := by
    simpa [prefixWord, tailWord_2668338, baseEnd_2668338] using wordTrace_append hprefix tailTrace_2668338
  have hstable : (prefixWord ++ tailWord_2668338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668338).length < 2 ^ (prefixWord ++ tailWord_2668338).sum := by decide
  have hdescent : baseEnd_2668338 < baseStart_2668338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668344 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 9]
def baseStart_2668344 : Nat := 118140960795 + 2668344 * 2 ^ 59
def prefixEnd_2668344 : Nat := 4983230072969 + 3 ^ 40 * 2668344 * 2
def baseEnd_2668344 : Nat := 152238113726757036169835

theorem tailTrace_2668344 : CollatzResearch.WordTrace tailWord_2668344 prefixEnd_2668344 152238113726757036169835 := by
  unfold tailWord_2668344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48661250522526439859418043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64881667363368586479224057 48661250522526439859418043)
  ·
    refine ⟨72991875783789659789127065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48661250522526439859418043 72991875783789659789127065)
    ·
      refine ⟨54743906837842244841845299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72991875783789659789127065 54743906837842244841845299)
      ·
        refine ⟨82115860256763367262767949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54743906837842244841845299 82115860256763367262767949)
        ·
          refine ⟨30793447596286262723537981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82115860256763367262767949 30793447596286262723537981)
          ·
            refine ⟨11547542848607348521326743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30793447596286262723537981 11547542848607348521326743)
            ·
              refine ⟨17321314272911022781990115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11547542848607348521326743 17321314272911022781990115)
              ·
                refine ⟨25981971409366534172985173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17321314272911022781990115 25981971409366534172985173)
                ·
                  refine ⟨152238113726757036169835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25981971409366534172985173 152238113726757036169835)
                  ·
                    rfl

theorem cell23_2668344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_2668344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668344 prefixEnd_2668344 := by exact prefixLift 2668344
  have htrace : WordTrace (prefixWord ++ tailWord_2668344) baseStart_2668344 baseEnd_2668344 := by
    simpa [prefixWord, tailWord_2668344, baseEnd_2668344] using wordTrace_append hprefix tailTrace_2668344
  have hstable : (prefixWord ++ tailWord_2668344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668344).length < 2 ^ (prefixWord ++ tailWord_2668344).sum := by decide
  have hdescent : baseEnd_2668344 < baseStart_2668344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668372 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_2668372 : Nat := 118140960795 + 2668372 * 2 ^ 59
def prefixEnd_2668372 : Nat := 4983230072969 + 3 ^ 40 * 2668372 * 2
def baseEnd_2668372 : Nat := 1370157400999139215978387

theorem tailTrace_2668372 : CollatzResearch.WordTrace tailWord_2668372 prefixEnd_2668372 1370157400999139215978387 := by
  unfold tailWord_2668372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48661761144475720250427685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64882348192634293667236913 48661761144475720250427685)
  ·
    refine ⟨9124080214589197546955191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48661761144475720250427685 9124080214589197546955191)
    ·
      refine ⟨13686120321883796320432787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9124080214589197546955191 13686120321883796320432787)
      ·
        refine ⟨20529180482825694480649181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13686120321883796320432787 20529180482825694480649181)
        ·
          refine ⟨7698442681059635430243443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20529180482825694480649181 7698442681059635430243443)
          ·
            refine ⟨11547664021589453145365165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7698442681059635430243443 11547664021589453145365165)
            ·
              refine ⟨4330374008096044929511937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11547664021589453145365165 4330374008096044929511937)
              ·
                refine ⟨3247780506072033697133953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330374008096044929511937 3247780506072033697133953)
                ·
                  refine ⟨2435835379554025272850465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247780506072033697133953 2435835379554025272850465)
                  ·
                    refine ⟨1826876534665518954637849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435835379554025272850465 1826876534665518954637849)
                    ·
                      refine ⟨1370157400999139215978387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826876534665518954637849 1370157400999139215978387)
                      ·
                        rfl

theorem cell23_2668372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_2668372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668372 prefixEnd_2668372 := by exact prefixLift 2668372
  have htrace : WordTrace (prefixWord ++ tailWord_2668372) baseStart_2668372 baseEnd_2668372 := by
    simpa [prefixWord, tailWord_2668372, baseEnd_2668372] using wordTrace_append hprefix tailTrace_2668372
  have hstable : (prefixWord ++ tailWord_2668372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668372).length < 2 ^ (prefixWord ++ tailWord_2668372).sum := by decide
  have hdescent : baseEnd_2668372 < baseStart_2668372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668411 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4]
def baseStart_2668411 : Nat := 118140960795 + 2668411 * 2 ^ 59
def prefixEnd_2668411 : Nat := 4983230072969 + 3 ^ 40 * 2668411 * 2
def baseEnd_2668411 : Nat := 1370177426744664563390707

theorem tailTrace_2668411 : CollatzResearch.WordTrace tailWord_2668411 prefixEnd_2668411 1370177426744664563390707 := by
  unfold tailWord_2668411
  simp only [CollatzResearch.WordTrace]
  refine ⟨97324944735810150161525087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64883296490540100107683391 97324944735810150161525087)
  ·
    refine ⟨145987417103715225242287631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97324944735810150161525087 145987417103715225242287631)
    ·
      refine ⟨218981125655572837863431447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145987417103715225242287631 218981125655572837863431447)
      ·
        refine ⟨328471688483359256795147171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218981125655572837863431447 328471688483359256795147171)
        ·
          refine ⟨492707532725038885192720757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328471688483359256795147171 492707532725038885192720757)
          ·
            refine ⟨46191331192972395486817571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 492707532725038885192720757 46191331192972395486817571)
            ·
              refine ⟨69286996789458593230226357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46191331192972395486817571 69286996789458593230226357)
              ·
                refine ⟨6495655949011743115333721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69286996789458593230226357 6495655949011743115333721)
                ·
                  refine ⟨4871741961758807336500291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495655949011743115333721 4871741961758807336500291)
                  ·
                    refine ⟨7307612942638211004750437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4871741961758807336500291 7307612942638211004750437)
                    ·
                      refine ⟨1370177426744664563390707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7307612942638211004750437 1370177426744664563390707)
                      ·
                        rfl

theorem cell23_2668411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_2668411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668411 prefixEnd_2668411 := by exact prefixLift 2668411
  have htrace : WordTrace (prefixWord ++ tailWord_2668411) baseStart_2668411 baseEnd_2668411 := by
    simpa [prefixWord, tailWord_2668411, baseEnd_2668411] using wordTrace_append hprefix tailTrace_2668411
  have hstable : (prefixWord ++ tailWord_2668411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668411).length < 2 ^ (prefixWord ++ tailWord_2668411).sum := by decide
  have hdescent : baseEnd_2668411 < baseStart_2668411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668465 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2668465 : Nat := 118140960795 + 2668465 * 2 ^ 59
def prefixEnd_2668465 : Nat := 4983230072969 + 3 ^ 40 * 2668465 * 2
def baseEnd_2668465 : Nat := 1370205154700007352115459

theorem tailTrace_2668465 : CollatzResearch.WordTrace tailWord_2668465 prefixEnd_2668465 1370205154700007352115459 := by
  unfold tailWord_2668465
  simp only [CollatzResearch.WordTrace]
  refine ⟨97326914277614517383990849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64884609518409678255993899 97326914277614517383990849)
  ·
    refine ⟨72995185708210888037993137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97326914277614517383990849 72995185708210888037993137)
    ·
      refine ⟨54746389281158166028494853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72995185708210888037993137 54746389281158166028494853)
      ·
        refine ⟨10264947990217156130342785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54746389281158166028494853 10264947990217156130342785)
        ·
          refine ⟨7698710992662867097757089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10264947990217156130342785 7698710992662867097757089)
          ·
            refine ⟨5774033244497150323317817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7698710992662867097757089 5774033244497150323317817)
            ·
              refine ⟨4330524933372862742488363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774033244497150323317817 4330524933372862742488363)
              ·
                refine ⟨6495787400059294113732545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330524933372862742488363 6495787400059294113732545)
                ·
                  refine ⟨4871840550044470585299409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6495787400059294113732545 4871840550044470585299409)
                  ·
                    refine ⟨3653880412533352938974557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4871840550044470585299409 3653880412533352938974557)
                    ·
                      refine ⟨1370205154700007352115459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653880412533352938974557 1370205154700007352115459)
                      ·
                        rfl

theorem cell23_2668465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2668465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668465 prefixEnd_2668465 := by exact prefixLift 2668465
  have htrace : WordTrace (prefixWord ++ tailWord_2668465) baseStart_2668465 baseEnd_2668465 := by
    simpa [prefixWord, tailWord_2668465, baseEnd_2668465] using wordTrace_append hprefix tailTrace_2668465
  have hstable : (prefixWord ++ tailWord_2668465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668465).length < 2 ^ (prefixWord ++ tailWord_2668465).sum := by decide
  have hdescent : baseEnd_2668465 < baseStart_2668465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668529 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_2668529 : Nat := 118140960795 + 2668529 * 2 ^ 59
def prefixEnd_2668529 : Nat := 4983230072969 + 3 ^ 40 * 2668529 * 2
def baseEnd_2668529 : Nat := 1370238017461895101715165

theorem tailTrace_2668529 : CollatzResearch.WordTrace tailWord_2668529 prefixEnd_2668529 1370238017461895101715165 := by
  unfold tailWord_2668529
  simp only [CollatzResearch.WordTrace]
  refine ⟨97329248549382656314320641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64886165699588437542880427 97329248549382656314320641)
  ·
    refine ⟨72996936412036992235740481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97329248549382656314320641 72996936412036992235740481)
    ·
      refine ⟨54747702309027744176805361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72996936412036992235740481 54747702309027744176805361)
      ·
        refine ⟨41060776731770808132604021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54747702309027744176805361 41060776731770808132604021)
        ·
          refine ⟨3849447818603513262431627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41060776731770808132604021 3849447818603513262431627)
          ·
            refine ⟨5774171727905269893647441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849447818603513262431627 5774171727905269893647441)
            ·
              refine ⟨4330628795928952420235581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774171727905269893647441 4330628795928952420235581)
              ·
                refine ⟨1623985798473357157588343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4330628795928952420235581 1623985798473357157588343)
                ·
                  refine ⟨2435978697710035736382515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623985798473357157588343 2435978697710035736382515)
                  ·
                    refine ⟨3653968046565053604573773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2435978697710035736382515 3653968046565053604573773)
                    ·
                      refine ⟨1370238017461895101715165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3653968046565053604573773 1370238017461895101715165)
                      ·
                        rfl

theorem cell23_2668529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_2668529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668529 prefixEnd_2668529 := by exact prefixLift 2668529
  have htrace : WordTrace (prefixWord ++ tailWord_2668529) baseStart_2668529 baseEnd_2668529 := by
    simpa [prefixWord, tailWord_2668529, baseEnd_2668529] using wordTrace_append hprefix tailTrace_2668529
  have hstable : (prefixWord ++ tailWord_2668529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668529).length < 2 ^ (prefixWord ++ tailWord_2668529).sum := by decide
  have hdescent : baseEnd_2668529 < baseStart_2668529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668552 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_2668552 : Nat := 118140960795 + 2668552 * 2 ^ 59
def prefixEnd_2668552 : Nat := 4983230072969 + 3 ^ 40 * 2668552 * 2
def baseEnd_2668552 : Nat := 1370249827516948511727559

theorem tailTrace_2668552 : CollatzResearch.WordTrace tailWord_2668552 prefixEnd_2668552 1370249827516948511727559 := by
  unfold tailWord_2668552
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665043714149665621203955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64886724952199554161605273 48665043714149665621203955)
  ·
    refine ⟨72997565571224498431805933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48665043714149665621203955 72997565571224498431805933)
    ·
      refine ⟨27374087089209186911927225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72997565571224498431805933 27374087089209186911927225)
      ·
        refine ⟨20530565316906890183945419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27374087089209186911927225 20530565316906890183945419)
        ·
          refine ⟨30795847975360335275918129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20530565316906890183945419 30795847975360335275918129)
          ·
            refine ⟨23096885981520251456938597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30795847975360335275918129 23096885981520251456938597)
            ·
              refine ⟨4330666121535047148175987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23096885981520251456938597 4330666121535047148175987)
              ·
                refine ⟨6495999182302570722263981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330666121535047148175987 6495999182302570722263981)
                ·
                  refine ⟨2435999693363464020848993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6495999182302570722263981 2435999693363464020848993)
                  ·
                    refine ⟨1826999770022598015636745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435999693363464020848993 1826999770022598015636745)
                    ·
                      refine ⟨1370249827516948511727559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1826999770022598015636745 1370249827516948511727559)
                      ·
                        rfl

theorem cell23_2668552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_2668552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668552 prefixEnd_2668552 := by exact prefixLift 2668552
  have htrace : WordTrace (prefixWord ++ tailWord_2668552) baseStart_2668552 baseEnd_2668552 := by
    simpa [prefixWord, tailWord_2668552, baseEnd_2668552] using wordTrace_append hprefix tailTrace_2668552
  have hstable : (prefixWord ++ tailWord_2668552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668552).length < 2 ^ (prefixWord ++ tailWord_2668552).sum := by decide
  have hdescent : baseEnd_2668552 < baseStart_2668552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668572 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2668572 : Nat := 118140960795 + 2668572 * 2 ^ 59
def prefixEnd_2668572 : Nat := 4983230072969 + 3 ^ 40 * 2668572 * 2
def baseEnd_2668572 : Nat := 1370260097130038433477467

theorem tailTrace_2668572 : CollatzResearch.WordTrace tailWord_2668572 prefixEnd_2668572 1370260097130038433477467 := by
  unfold tailWord_2668572
  simp only [CollatzResearch.WordTrace]
  refine ⟨48665408444113437329067985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64887211258817916438757313 48665408444113437329067985)
  ·
    refine ⟨36499056333085077996800989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48665408444113437329067985 36499056333085077996800989)
    ·
      refine ⟨13687146124906904248800371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36499056333085077996800989 13687146124906904248800371)
      ·
        refine ⟨20530719187360356373200557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13687146124906904248800371 20530719187360356373200557)
        ·
          refine ⟨7699019695260133639950209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20530719187360356373200557 7699019695260133639950209)
          ·
            refine ⟨5774264771445100229962657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7699019695260133639950209 5774264771445100229962657)
            ·
              refine ⟨4330698578583825172471993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774264771445100229962657 4330698578583825172471993)
              ·
                refine ⟨3248023933937868879353995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330698578583825172471993 3248023933937868879353995)
                ·
                  refine ⟨4872035900906803319030993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248023933937868879353995 4872035900906803319030993)
                  ·
                    refine ⟨3654026925680102489273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4872035900906803319030993 3654026925680102489273245)
                    ·
                      refine ⟨1370260097130038433477467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3654026925680102489273245 1370260097130038433477467)
                      ·
                        rfl

theorem cell23_2668572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2668572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668572 prefixEnd_2668572 := by exact prefixLift 2668572
  have htrace : WordTrace (prefixWord ++ tailWord_2668572) baseStart_2668572 baseEnd_2668572 := by
    simpa [prefixWord, tailWord_2668572, baseEnd_2668572] using wordTrace_append hprefix tailTrace_2668572
  have hstable : (prefixWord ++ tailWord_2668572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668572).length < 2 ^ (prefixWord ++ tailWord_2668572).sum := by decide
  have hdescent : baseEnd_2668572 < baseStart_2668572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668586 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2668586 : Nat := 118140960795 + 2668586 * 2 ^ 59
def prefixEnd_2668586 : Nat := 4983230072969 + 3 ^ 40 * 2668586 * 2
def baseEnd_2668586 : Nat := 1370267285859201378702403

theorem tailTrace_2668586 : CollatzResearch.WordTrace tailWord_2668586 prefixEnd_2668586 1370267285859201378702403 := by
  unfold tailWord_2668586
  simp only [CollatzResearch.WordTrace]
  refine ⟨24332831877544038762286403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64887551673450770032763741 24332831877544038762286403)
  ·
    refine ⟨36499247816316058143429605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24332831877544038762286403 36499247816316058143429605)
    ·
      refine ⟨6843608965559260901893051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36499247816316058143429605 6843608965559260901893051)
      ·
        refine ⟨10265413448338891352839577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843608965559260901893051 10265413448338891352839577)
        ·
          refine ⟨7699060086254168514629683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10265413448338891352839577 7699060086254168514629683)
          ·
            refine ⟨11548590129381252771944525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699060086254168514629683 11548590129381252771944525)
            ·
              refine ⟨4330721298517969789479197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11548590129381252771944525 4330721298517969789479197)
              ·
                refine ⟨1624020486944238671054699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4330721298517969789479197 1624020486944238671054699)
                ·
                  refine ⟨2436030730416358006582049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624020486944238671054699 2436030730416358006582049)
                  ·
                    refine ⟨1827023047812268504936537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436030730416358006582049 1827023047812268504936537)
                    ·
                      refine ⟨1370267285859201378702403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827023047812268504936537 1370267285859201378702403)
                      ·
                        rfl

theorem cell23_2668586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2668586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668586 prefixEnd_2668586 := by exact prefixLift 2668586
  have htrace : WordTrace (prefixWord ++ tailWord_2668586) baseStart_2668586 baseEnd_2668586 := by
    simpa [prefixWord, tailWord_2668586, baseEnd_2668586] using wordTrace_append hprefix tailTrace_2668586
  have hstable : (prefixWord ++ tailWord_2668586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668586).length < 2 ^ (prefixWord ++ tailWord_2668586).sum := by decide
  have hdescent : baseEnd_2668586 < baseStart_2668586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668625 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_2668625 : Nat := 118140960795 + 2668625 * 2 ^ 59
def prefixEnd_2668625 : Nat := 4983230072969 + 3 ^ 40 * 2668625 * 2
def baseEnd_2668625 : Nat := 1370287311604726726114723

theorem tailTrace_2668625 : CollatzResearch.WordTrace tailWord_2668625 prefixEnd_2668625 1370287311604726726114723 := by
  unfold tailWord_2668625
  simp only [CollatzResearch.WordTrace]
  refine ⟨97332749957034864709815329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64888499971356576473210219 97332749957034864709815329)
  ·
    refine ⟨72999562467776148532361497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97332749957034864709815329 72999562467776148532361497)
    ·
      refine ⟨54749671850832111399271123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72999562467776148532361497 54749671850832111399271123)
      ·
        refine ⟨82124507776248167098906685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54749671850832111399271123 82124507776248167098906685)
        ·
          refine ⟨30796690416093062662090007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82124507776248167098906685 30796690416093062662090007)
          ·
            refine ⟨46195035624139593993135011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30796690416093062662090007 46195035624139593993135011)
            ·
              refine ⟨69292553436209390989702517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46195035624139593993135011 69292553436209390989702517)
              ·
                refine ⟨6496176884644630405284611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69292553436209390989702517 6496176884644630405284611)
                ·
                  refine ⟨9744265326966945607926917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496176884644630405284611 9744265326966945607926917)
                  ·
                    refine ⟨1827049748806302301486297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9744265326966945607926917 1827049748806302301486297)
                    ·
                      refine ⟨1370287311604726726114723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827049748806302301486297 1370287311604726726114723)
                      ·
                        rfl

theorem cell23_2668625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_2668625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668625 prefixEnd_2668625 := by exact prefixLift 2668625
  have htrace : WordTrace (prefixWord ++ tailWord_2668625) baseStart_2668625 baseEnd_2668625 := by
    simpa [prefixWord, tailWord_2668625, baseEnd_2668625] using wordTrace_append hprefix tailTrace_2668625
  have hstable : (prefixWord ++ tailWord_2668625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668625).length < 2 ^ (prefixWord ++ tailWord_2668625).sum := by decide
  have hdescent : baseEnd_2668625 < baseStart_2668625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668629 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2668629 : Nat := 118140960795 + 2668629 * 2 ^ 59
def prefixEnd_2668629 : Nat := 4983230072969 + 3 ^ 40 * 2668629 * 2
def baseEnd_2668629 : Nat := 1370289365527344710464705

theorem tailTrace_2668629 : CollatzResearch.WordTrace tailWord_2668629 prefixEnd_2668629 1370289365527344710464705 := by
  unfold tailWord_2668629
  simp only [CollatzResearch.WordTrace]
  refine ⟨97332895849020373392960941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64888597232680248928640627 97332895849020373392960941)
  ·
    refine ⟨36499835943382640022360353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97332895849020373392960941 36499835943382640022360353)
    ·
      refine ⟨27374876957536980016770265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36499835943382640022360353 27374876957536980016770265)
      ·
        refine ⟨20531157718152735012577699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27374876957536980016770265 20531157718152735012577699)
        ·
          refine ⟨30796736577229102518866549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20531157718152735012577699 30796736577229102518866549)
          ·
            refine ⟨2887194054115228361143739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30796736577229102518866549 2887194054115228361143739)
            ·
              refine ⟨4330791081172842541715609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887194054115228361143739 4330791081172842541715609)
              ·
                refine ⟨3248093310879631906286707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330791081172842541715609 3248093310879631906286707)
                ·
                  refine ⟨4872139966319447859430061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248093310879631906286707 4872139966319447859430061)
                  ·
                    refine ⟨1827052487369792947286273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4872139966319447859430061 1827052487369792947286273)
                    ·
                      refine ⟨1370289365527344710464705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827052487369792947286273 1370289365527344710464705)
                      ·
                        rfl

theorem cell23_2668629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2668629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668629 prefixEnd_2668629 := by exact prefixLift 2668629
  have htrace : WordTrace (prefixWord ++ tailWord_2668629) baseStart_2668629 baseEnd_2668629 := by
    simpa [prefixWord, tailWord_2668629, baseEnd_2668629] using wordTrace_append hprefix tailTrace_2668629
  have hstable : (prefixWord ++ tailWord_2668629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668629).length < 2 ^ (prefixWord ++ tailWord_2668629).sum := by decide
  have hdescent : baseEnd_2668629 < baseStart_2668629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668675 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3]
def baseStart_2668675 : Nat := 118140960795 + 2668675 * 2 ^ 59
def prefixEnd_2668675 : Nat := 4983230072969 + 3 ^ 40 * 2668675 * 2
def baseEnd_2668675 : Nat := 1370312985637451530489493

theorem tailTrace_2668675 : CollatzResearch.WordTrace tailWord_2668675 prefixEnd_2668675 1370312985637451530489493 := by
  unfold tailWord_2668675
  simp only [CollatzResearch.WordTrace]
  refine ⟨97334573606853723249135479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64889715737902482166090319 97334573606853723249135479)
  ·
    refine ⟨146001860410280584873703219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97334573606853723249135479 146001860410280584873703219)
    ·
      refine ⟨219002790615420877310554829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146001860410280584873703219 219002790615420877310554829)
      ·
        refine ⟨82126046480782828991458061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219002790615420877310554829 82126046480782828991458061)
        ·
          refine ⟨30797267430293560871796773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82126046480782828991458061 30797267430293560871796773)
          ·
            refine ⟨5774487643180042663461895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30797267430293560871796773 5774487643180042663461895)
            ·
              refine ⟨8661731464770063995192843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774487643180042663461895 8661731464770063995192843)
              ·
                refine ⟨12992597197155095992789265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661731464770063995192843 12992597197155095992789265)
                ·
                  refine ⟨9744447897866321994591949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12992597197155095992789265 9744447897866321994591949)
                  ·
                    refine ⟨3654167961699870747971981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9744447897866321994591949 3654167961699870747971981)
                    ·
                      refine ⟨1370312985637451530489493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3654167961699870747971981 1370312985637451530489493)
                      ·
                        rfl

theorem cell23_2668675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_2668675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668675 prefixEnd_2668675 := by exact prefixLift 2668675
  have htrace : WordTrace (prefixWord ++ tailWord_2668675) baseStart_2668675 baseEnd_2668675 := by
    simpa [prefixWord, tailWord_2668675, baseEnd_2668675] using wordTrace_append hprefix tailTrace_2668675
  have hstable : (prefixWord ++ tailWord_2668675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668675).length < 2 ^ (prefixWord ++ tailWord_2668675).sum := by decide
  have hdescent : baseEnd_2668675 < baseStart_2668675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668695 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 7]
def baseStart_2668695 : Nat := 118140960795 + 2668695 * 2 ^ 59
def prefixEnd_2668695 : Nat := 4983230072969 + 3 ^ 40 * 2668695 * 2
def baseEnd_2668695 : Nat := 456774418416847150746467

theorem tailTrace_2668695 : CollatzResearch.WordTrace tailWord_2668695 prefixEnd_2668695 456774418416847150746467 := by
  unfold tailWord_2668695
  simp only [CollatzResearch.WordTrace]
  refine ⟨97335303066781266664863539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64890202044520844443242359 97335303066781266664863539)
  ·
    refine ⟨146002954600171899997295309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97335303066781266664863539 146002954600171899997295309)
    ·
      refine ⟨54751107975064462498985741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146002954600171899997295309 54751107975064462498985741)
      ·
        refine ⟨20531665490649173437119653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54751107975064462498985741 20531665490649173437119653)
        ·
          refine ⟨3849687279496720019459935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20531665490649173437119653 3849687279496720019459935)
          ·
            refine ⟨5774530919245080029189903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849687279496720019459935 5774530919245080029189903)
            ·
              refine ⟨8661796378867620043784855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774530919245080029189903 8661796378867620043784855)
              ·
                refine ⟨12992694568301430065677283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661796378867620043784855 12992694568301430065677283)
                ·
                  refine ⟨19489041852452145098515925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12992694568301430065677283 19489041852452145098515925)
                  ·
                    refine ⟨456774418416847150746467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19489041852452145098515925 456774418416847150746467)
                    ·
                      rfl

theorem cell23_2668695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_2668695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668695 prefixEnd_2668695 := by exact prefixLift 2668695
  have htrace : WordTrace (prefixWord ++ tailWord_2668695) baseStart_2668695 baseEnd_2668695 := by
    simpa [prefixWord, tailWord_2668695, baseEnd_2668695] using wordTrace_append hprefix tailTrace_2668695
  have hstable : (prefixWord ++ tailWord_2668695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668695).length < 2 ^ (prefixWord ++ tailWord_2668695).sum := by decide
  have hdescent : baseEnd_2668695 < baseStart_2668695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668728 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2668728 : Nat := 118140960795 + 2668728 * 2 ^ 59
def prefixEnd_2668728 : Nat := 4983230072969 + 3 ^ 40 * 2668728 * 2
def baseEnd_2668728 : Nat := 1370340200112139823126749

theorem tailTrace_2668728 : CollatzResearch.WordTrace tailWord_2668728 prefixEnd_2668728 1370340200112139823126749 := by
  unfold tailWord_2668728
  simp only [CollatzResearch.WordTrace]
  refine ⟨48668253337830856650407419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64891004450441142200543225 48668253337830856650407419)
  ·
    refine ⟨73002380006746284975611129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48668253337830856650407419 73002380006746284975611129)
    ·
      refine ⟨54751785005059713731708347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73002380006746284975611129 54751785005059713731708347)
      ·
        refine ⟨82127677507589570597562521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54751785005059713731708347 82127677507589570597562521)
        ·
          refine ⟨61595758130692177948171891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82127677507589570597562521 61595758130692177948171891)
          ·
            refine ⟨92393637196038266922257837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61595758130692177948171891 92393637196038266922257837)
            ·
              refine ⟨34647613948514350095846689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92393637196038266922257837 34647613948514350095846689)
              ·
                refine ⟨25985710461385762571885017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34647613948514350095846689 25985710461385762571885017)
                ·
                  refine ⟨19489282846039321928913763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25985710461385762571885017 19489282846039321928913763)
                  ·
                    refine ⟨29233924269058982893370645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19489282846039321928913763 29233924269058982893370645)
                    ·
                      refine ⟨1370340200112139823126749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29233924269058982893370645 1370340200112139823126749)
                      ·
                        rfl

theorem cell23_2668728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2668728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668728 prefixEnd_2668728 := by exact prefixLift 2668728
  have htrace : WordTrace (prefixWord ++ tailWord_2668728) baseStart_2668728 baseEnd_2668728 := by
    simpa [prefixWord, tailWord_2668728, baseEnd_2668728] using wordTrace_append hprefix tailTrace_2668728
  have hstable : (prefixWord ++ tailWord_2668728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668728).length < 2 ^ (prefixWord ++ tailWord_2668728).sum := by decide
  have hdescent : baseEnd_2668728 < baseStart_2668728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668776 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2668776 : Nat := 118140960795 + 2668776 * 2 ^ 59
def prefixEnd_2668776 : Nat := 4983230072969 + 3 ^ 40 * 2668776 * 2
def baseEnd_2668776 : Nat := 456788282394518545108843

theorem tailTrace_2668776 : CollatzResearch.WordTrace tailWord_2668776 prefixEnd_2668776 456788282394518545108843 := by
  unfold tailWord_2668776
  simp only [CollatzResearch.WordTrace]
  refine ⟨48669128689743908749281091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64892171586325211665708121 48669128689743908749281091)
  ·
    refine ⟨73003693034615863123921637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48669128689743908749281091 73003693034615863123921637)
    ·
      refine ⟨13688192443990474335735307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73003693034615863123921637 13688192443990474335735307)
      ·
        refine ⟨20532288665985711503602961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13688192443990474335735307 20532288665985711503602961)
        ·
          refine ⟨15399216499489283627702221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20532288665985711503602961 15399216499489283627702221)
          ·
            refine ⟨5774706187308481360388333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15399216499489283627702221 5774706187308481360388333)
            ·
              refine ⟨2165514820240680510145625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5774706187308481360388333 2165514820240680510145625)
              ·
                refine ⟨1624136115180510382609219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165514820240680510145625 1624136115180510382609219)
                ·
                  refine ⟨2436204172770765573913829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624136115180510382609219 2436204172770765573913829)
                  ·
                    refine ⟨456788282394518545108843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436204172770765573913829 456788282394518545108843)
                    ·
                      rfl

theorem cell23_2668776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2668776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668776 prefixEnd_2668776 := by exact prefixLift 2668776
  have htrace : WordTrace (prefixWord ++ tailWord_2668776) baseStart_2668776 baseEnd_2668776 := by
    simpa [prefixWord, tailWord_2668776, baseEnd_2668776] using wordTrace_append hprefix tailTrace_2668776
  have hstable : (prefixWord ++ tailWord_2668776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668776).length < 2 ^ (prefixWord ++ tailWord_2668776).sum := by decide
  have hdescent : baseEnd_2668776 < baseStart_2668776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668809 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 2, 3, 2]
def baseStart_2668809 : Nat := 118140960795 + 2668809 * 2 ^ 59
def prefixEnd_2668809 : Nat := 4983230072969 + 3 ^ 40 * 2668809 * 2
def baseEnd_2668809 : Nat := 1370381792045154006213877

theorem tailTrace_2668809 : CollatzResearch.WordTrace tailWord_2668809 prefixEnd_2668809 1370381792045154006213877 := by
  unfold tailWord_2668809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97339460988368264134513481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64892973992245509423008987 97339460988368264134513481)
  ·
    refine ⟨73004595741276198100885111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97339460988368264134513481 73004595741276198100885111)
    ·
      refine ⟨109506893611914297151327667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73004595741276198100885111 109506893611914297151327667)
      ·
        refine ⟨164260340417871445726991501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109506893611914297151327667 164260340417871445726991501)
        ·
          refine ⟨61597627656701792147621813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164260340417871445726991501 61597627656701792147621813)
          ·
            refine ⟨5774777592815793013839545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61597627656701792147621813 5774777592815793013839545)
            ·
              refine ⟨4331083194611844760379659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5774777592815793013839545 4331083194611844760379659)
              ·
                refine ⟨6496624791917767140569489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331083194611844760379659 6496624791917767140569489)
                ·
                  refine ⟨4872468593938325355427117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6496624791917767140569489 4872468593938325355427117)
                  ·
                    refine ⟨1827175722726872008285169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4872468593938325355427117 1827175722726872008285169)
                    ·
                      refine ⟨1370381792045154006213877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827175722726872008285169 1370381792045154006213877)
                      ·
                        rfl

theorem cell23_2668809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 3, 2].length) (baseStart_2668809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668809 prefixEnd_2668809 := by exact prefixLift 2668809
  have htrace : WordTrace (prefixWord ++ tailWord_2668809) baseStart_2668809 baseEnd_2668809 := by
    simpa [prefixWord, tailWord_2668809, baseEnd_2668809] using wordTrace_append hprefix tailTrace_2668809
  have hstable : (prefixWord ++ tailWord_2668809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668809).length < 2 ^ (prefixWord ++ tailWord_2668809).sum := by decide
  have hdescent : baseEnd_2668809 < baseStart_2668809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668815 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 6, 4]
def baseStart_2668815 : Nat := 118140960795 + 2668815 * 2 ^ 59
def prefixEnd_2668815 : Nat := 4983230072969 + 3 ^ 40 * 2668815 * 2
def baseEnd_2668815 : Nat := 456794957643026994246283

theorem tailTrace_2668815 : CollatzResearch.WordTrace tailWord_2668815 prefixEnd_2668815 456794957643026994246283 := by
  unfold tailWord_2668815
  simp only [CollatzResearch.WordTrace]
  refine ⟨97339679826346527159231899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64893119884231018106154599 97339679826346527159231899)
  ·
    refine ⟨146009519739519790738847849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97339679826346527159231899 146009519739519790738847849)
    ·
      refine ⟨109507139804639843054135887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146009519739519790738847849 109507139804639843054135887)
      ·
        refine ⟨164260709706959764581203831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109507139804639843054135887 164260709706959764581203831)
        ·
          refine ⟨246391064560439646871805747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164260709706959764581203831 246391064560439646871805747)
          ·
            refine ⟨369586596840659470307708621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246391064560439646871805747 369586596840659470307708621)
            ·
              refine ⟨138594973815247301365390733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369586596840659470307708621 138594973815247301365390733)
              ·
                refine ⟨51973115180717738012021525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138594973815247301365390733 51973115180717738012021525)
                ·
                  refine ⟨2436239774096143969313509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51973115180717738012021525 2436239774096143969313509)
                  ·
                    refine ⟨456794957643026994246283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436239774096143969313509 456794957643026994246283)
                    ·
                      rfl

theorem cell23_2668815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_2668815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668815 prefixEnd_2668815 := by exact prefixLift 2668815
  have htrace : WordTrace (prefixWord ++ tailWord_2668815) baseStart_2668815 baseEnd_2668815 := by
    simpa [prefixWord, tailWord_2668815, baseEnd_2668815] using wordTrace_append hprefix tailTrace_2668815
  have hstable : (prefixWord ++ tailWord_2668815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668815).length < 2 ^ (prefixWord ++ tailWord_2668815).sum := by decide
  have hdescent : baseEnd_2668815 < baseStart_2668815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668835 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2668835 : Nat := 118140960795 + 2668835 * 2 ^ 59
def prefixEnd_2668835 : Nat := 4983230072969 + 3 ^ 40 * 2668835 * 2
def baseEnd_2668835 : Nat := 1370395142542170904488757

theorem tailTrace_2668835 : CollatzResearch.WordTrace tailWord_2668835 prefixEnd_2668835 1370395142542170904488757 := by
  unfold tailWord_2668835
  simp only [CollatzResearch.WordTrace]
  refine ⟨97340409286274070574959959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64893606190849380383306639 97340409286274070574959959)
  ·
    refine ⟨146010613929411105862439939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97340409286274070574959959 146010613929411105862439939)
    ·
      refine ⟨219015920894116658793659909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146010613929411105862439939 219015920894116658793659909)
      ·
        refine ⟨41065485167646873523811233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219015920894116658793659909 41065485167646873523811233)
        ·
          refine ⟨30799113875735155142858425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41065485167646873523811233 30799113875735155142858425)
          ·
            refine ⟨23099335406801366357143819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30799113875735155142858425 23099335406801366357143819)
            ·
              refine ⟨34649003110202049535715729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23099335406801366357143819 34649003110202049535715729)
              ·
                refine ⟨25986752332651537151786797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34649003110202049535715729 25986752332651537151786797)
                ·
                  refine ⟨9745032124744326431920049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25986752332651537151786797 9745032124744326431920049)
                  ·
                    refine ⟨7308774093558244823940037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9745032124744326431920049 7308774093558244823940037)
                    ·
                      refine ⟨1370395142542170904488757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7308774093558244823940037 1370395142542170904488757)
                      ·
                        rfl

theorem cell23_2668835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2668835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668835 prefixEnd_2668835 := by exact prefixLift 2668835
  have htrace : WordTrace (prefixWord ++ tailWord_2668835) baseStart_2668835 baseEnd_2668835 := by
    simpa [prefixWord, tailWord_2668835, baseEnd_2668835] using wordTrace_append hprefix tailTrace_2668835
  have hstable : (prefixWord ++ tailWord_2668835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668835).length < 2 ^ (prefixWord ++ tailWord_2668835).sum := by decide
  have hdescent : baseEnd_2668835 < baseStart_2668835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668872 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2668872 : Nat := 118140960795 + 2668872 * 2 ^ 59
def prefixEnd_2668872 : Nat := 4983230072969 + 3 ^ 40 * 2668872 * 2
def baseEnd_2668872 : Nat := 1370414141326387259726087

theorem tailTrace_2668872 : CollatzResearch.WordTrace tailWord_2668872 prefixEnd_2668872 1370414141326387259726087 := by
  unfold tailWord_2668872
  simp only [CollatzResearch.WordTrace]
  refine ⟨48670879393570012947028435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64894505858093350596037913 48670879393570012947028435)
  ·
    refine ⟨73006319090355019420542653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48670879393570012947028435 73006319090355019420542653)
    ·
      refine ⟨27377369658883132282703495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73006319090355019420542653 27377369658883132282703495)
      ·
        refine ⟨41066054488324698424055243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27377369658883132282703495 41066054488324698424055243)
        ·
          refine ⟨61599081732487047636082865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41066054488324698424055243 61599081732487047636082865)
          ·
            refine ⟨46199311299365285727062149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61599081732487047636082865 46199311299365285727062149)
            ·
              refine ⟨8662370868630991073824153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46199311299365285727062149 8662370868630991073824153)
              ·
                refine ⟨6496778151473243305368115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8662370868630991073824153 6496778151473243305368115)
                ·
                  refine ⟨9745167227209864958052173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496778151473243305368115 9745167227209864958052173)
                  ·
                    refine ⟨3654437710203699359269565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9745167227209864958052173 3654437710203699359269565)
                    ·
                      refine ⟨1370414141326387259726087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3654437710203699359269565 1370414141326387259726087)
                      ·
                        rfl

theorem cell23_2668872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2668872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668872 prefixEnd_2668872 := by exact prefixLift 2668872
  have htrace : WordTrace (prefixWord ++ tailWord_2668872) baseStart_2668872 baseEnd_2668872 := by
    simpa [prefixWord, tailWord_2668872, baseEnd_2668872] using wordTrace_append hprefix tailTrace_2668872
  have hstable : (prefixWord ++ tailWord_2668872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668872).length < 2 ^ (prefixWord ++ tailWord_2668872).sum := by decide
  have hdescent : baseEnd_2668872 < baseStart_2668872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668895 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2668895 : Nat := 118140960795 + 2668895 * 2 ^ 59
def prefixEnd_2668895 : Nat := 4983230072969 + 3 ^ 40 * 2668895 * 2
def baseEnd_2668895 : Nat := 1370425951381440669738481

theorem tailTrace_2668895 : CollatzResearch.WordTrace tailWord_2668895 prefixEnd_2668895 1370425951381440669738481 := by
  unfold tailWord_2668895
  simp only [CollatzResearch.WordTrace]
  refine ⟨97342597666056700822144139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64895065110704467214762759 97342597666056700822144139)
  ·
    refine ⟨146013896499085051233216209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97342597666056700822144139 146013896499085051233216209)
    ·
      refine ⟨109510422374313788424912157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146013896499085051233216209 109510422374313788424912157)
      ·
        refine ⟨41066408390367670659342059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109510422374313788424912157 41066408390367670659342059)
        ·
          refine ⟨61599612585551505989013089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41066408390367670659342059 61599612585551505989013089)
          ·
            refine ⟨46199709439163629491759817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61599612585551505989013089 46199709439163629491759817)
            ·
              refine ⟨34649782079372722118819863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46199709439163629491759817 34649782079372722118819863)
              ·
                refine ⟨51974673119059083178229795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34649782079372722118819863 51974673119059083178229795)
                ·
                  refine ⟨77962009678588624767344693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51974673119059083178229795 77962009678588624767344693)
                  ·
                    refine ⟨7308938407367683571938565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77962009678588624767344693 7308938407367683571938565)
                    ·
                      refine ⟨1370425951381440669738481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7308938407367683571938565 1370425951381440669738481)
                      ·
                        rfl

theorem cell23_2668895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2668895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668895 prefixEnd_2668895 := by exact prefixLift 2668895
  have htrace : WordTrace (prefixWord ++ tailWord_2668895) baseStart_2668895 baseEnd_2668895 := by
    simpa [prefixWord, tailWord_2668895, baseEnd_2668895] using wordTrace_append hprefix tailTrace_2668895
  have hstable : (prefixWord ++ tailWord_2668895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668895).length < 2 ^ (prefixWord ++ tailWord_2668895).sum := by decide
  have hdescent : baseEnd_2668895 < baseStart_2668895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668905 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_2668905 : Nat := 118140960795 + 2668905 * 2 ^ 59
def prefixEnd_2668905 : Nat := 4983230072969 + 3 ^ 40 * 2668905 * 2
def baseEnd_2668905 : Nat := 456810362062661876871145

theorem tailTrace_2668905 : CollatzResearch.WordTrace tailWord_2668905 prefixEnd_2668905 456810362062661876871145 := by
  unfold tailWord_2668905
  simp only [CollatzResearch.WordTrace]
  refine ⟨97342962396020472530008169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64895308264013648353338779 97342962396020472530008169)
  ·
    refine ⟨73007221797015354397506127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97342962396020472530008169 73007221797015354397506127)
    ·
      refine ⟨109510832695523031596259191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73007221797015354397506127 109510832695523031596259191)
      ·
        refine ⟨164266249043284547394388787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109510832695523031596259191 164266249043284547394388787)
        ·
          refine ⟨246399373564926821091583181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164266249043284547394388787 246399373564926821091583181)
          ·
            refine ⟨92399765086847557909343693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246399373564926821091583181 92399765086847557909343693)
            ·
              refine ⟨34649911907567834216003885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92399765086847557909343693 34649911907567834216003885)
              ·
                refine ⟨12993716965337937831001457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34649911907567834216003885 12993716965337937831001457)
                ·
                  refine ⟨9745287724003453373251093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12993716965337937831001457 9745287724003453373251093)
                  ·
                    refine ⟨456810362062661876871145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9745287724003453373251093 456810362062661876871145)
                    ·
                      rfl

theorem cell23_2668905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_2668905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668905 prefixEnd_2668905 := by exact prefixLift 2668905
  have htrace : WordTrace (prefixWord ++ tailWord_2668905) baseStart_2668905 baseEnd_2668905 := by
    simpa [prefixWord, tailWord_2668905, baseEnd_2668905] using wordTrace_append hprefix tailTrace_2668905
  have hstable : (prefixWord ++ tailWord_2668905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668905).length < 2 ^ (prefixWord ++ tailWord_2668905).sum := by decide
  have hdescent : baseEnd_2668905 < baseStart_2668905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668906 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2668906 : Nat := 118140960795 + 2668906 * 2 ^ 59
def prefixEnd_2668906 : Nat := 4983230072969 + 3 ^ 40 * 2668906 * 2
def baseEnd_2668906 : Nat := 1370431599668640126700931

theorem tailTrace_2668906 : CollatzResearch.WordTrace tailWord_2668906 prefixEnd_2668906 1370431599668640126700931 := by
  unfold tailWord_2668906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24335749717254212425198643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64895332579344566467196381 24335749717254212425198643)
  ·
    refine ⟨36503624575881318637797965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24335749717254212425198643 36503624575881318637797965)
    ·
      refine ⟨13688859215955494489174237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36503624575881318637797965 13688859215955494489174237)
      ·
        refine ⟨5133322205983310433440339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13688859215955494489174237 5133322205983310433440339)
        ·
          refine ⟨7699983308974965650160509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5133322205983310433440339 7699983308974965650160509)
          ·
            refine ⟨2887493740865612118810191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7699983308974965650160509 2887493740865612118810191)
            ·
              refine ⟨4331240611298418178215287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887493740865612118810191 4331240611298418178215287)
              ·
                refine ⟨6496860916947627267322931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4331240611298418178215287 6496860916947627267322931)
                ·
                  refine ⟨9745291375421440900984397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6496860916947627267322931 9745291375421440900984397)
                  ·
                    refine ⟨3654484265783040337869149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9745291375421440900984397 3654484265783040337869149)
                    ·
                      refine ⟨1370431599668640126700931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3654484265783040337869149 1370431599668640126700931)
                      ·
                        rfl

theorem cell23_2668906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2668906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668906 prefixEnd_2668906 := by exact prefixLift 2668906
  have htrace : WordTrace (prefixWord ++ tailWord_2668906) baseStart_2668906 baseEnd_2668906 := by
    simpa [prefixWord, tailWord_2668906, baseEnd_2668906] using wordTrace_append hprefix tailTrace_2668906
  have hstable : (prefixWord ++ tailWord_2668906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668906).length < 2 ^ (prefixWord ++ tailWord_2668906).sum := by decide
  have hdescent : baseEnd_2668906 < baseStart_2668906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_2668915 : Nat := 118140960795 + 2668915 * 2 ^ 59
def prefixEnd_2668915 : Nat := 4983230072969 + 3 ^ 40 * 2668915 * 2
def baseEnd_2668915 : Nat := 1370436220994530591488389

theorem tailTrace_2668915 : CollatzResearch.WordTrace tailWord_2668915 prefixEnd_2668915 1370436220994530591488389 := by
  unfold tailWord_2668915
  simp only [CollatzResearch.WordTrace]
  refine ⟨97343327125984244237872199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64895551417322829491914799 97343327125984244237872199)
  ·
    refine ⟨146014990688976366356808299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97343327125984244237872199 146014990688976366356808299)
    ·
      refine ⟨219022486033464549535212449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146014990688976366356808299 219022486033464549535212449)
      ·
        refine ⟨164266864525098412151409337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219022486033464549535212449 164266864525098412151409337)
        ·
          refine ⟨123200148393823809113557003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164266864525098412151409337 123200148393823809113557003)
          ·
            refine ⟨184800222590735713670335505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123200148393823809113557003 184800222590735713670335505)
            ·
              refine ⟨138600166943051785252751629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184800222590735713670335505 138600166943051785252751629)
              ·
                refine ⟨51975062603644419469781861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138600166943051785252751629 51975062603644419469781861)
                ·
                  refine ⟨9745324238183328650584099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51975062603644419469781861 9745324238183328650584099)
                  ·
                    refine ⟨14617986357274992975876149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9745324238183328650584099 14617986357274992975876149)
                    ·
                      refine ⟨1370436220994530591488389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14617986357274992975876149 1370436220994530591488389)
                      ·
                        rfl

theorem cell23_2668915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_2668915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668915 prefixEnd_2668915 := by exact prefixLift 2668915
  have htrace : WordTrace (prefixWord ++ tailWord_2668915) baseStart_2668915 baseEnd_2668915 := by
    simpa [prefixWord, tailWord_2668915, baseEnd_2668915] using wordTrace_append hprefix tailTrace_2668915
  have hstable : (prefixWord ++ tailWord_2668915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668915).length < 2 ^ (prefixWord ++ tailWord_2668915).sum := by decide
  have hdescent : baseEnd_2668915 < baseStart_2668915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668932 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2668932 : Nat := 118140960795 + 2668932 * 2 ^ 59
def prefixEnd_2668932 : Nat := 4983230072969 + 3 ^ 40 * 2668932 * 2
def baseEnd_2668932 : Nat := 1370444950165657024975811

theorem tailTrace_2668932 : CollatzResearch.WordTrace tailWord_2668932 prefixEnd_2668932 1370444950165657024975811 := by
  unfold tailWord_2668932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48671973583461328070620525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64895964777948437427494033 48671973583461328070620525)
  ·
    refine ⟨18251990093797998026482697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48671973583461328070620525 18251990093797998026482697)
    ·
      refine ⟨13688992570348498519862023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18251990093797998026482697 13688992570348498519862023)
      ·
        refine ⟨20533488855522747779793035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13688992570348498519862023 20533488855522747779793035)
        ·
          refine ⟨30800233283284121669689553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20533488855522747779793035 30800233283284121669689553)
          ·
            refine ⟨23100174962463091252267165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30800233283284121669689553 23100174962463091252267165)
            ·
              refine ⟨8662565610923659219600187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23100174962463091252267165 8662565610923659219600187)
              ·
                refine ⟨12993848416385488829400281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8662565610923659219600187 12993848416385488829400281)
                ·
                  refine ⟨9745386312289116622050211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12993848416385488829400281 9745386312289116622050211)
                  ·
                    refine ⟨14618079468433674933075317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9745386312289116622050211 14618079468433674933075317)
                    ·
                      refine ⟨1370444950165657024975811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14618079468433674933075317 1370444950165657024975811)
                      ·
                        rfl

theorem cell23_2668932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2668932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668932 prefixEnd_2668932 := by exact prefixLift 2668932
  have htrace : WordTrace (prefixWord ++ tailWord_2668932) baseStart_2668932 baseEnd_2668932 := by
    simpa [prefixWord, tailWord_2668932, baseEnd_2668932] using wordTrace_append hprefix tailTrace_2668932
  have hstable : (prefixWord ++ tailWord_2668932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668932).length < 2 ^ (prefixWord ++ tailWord_2668932).sum := by decide
  have hdescent : baseEnd_2668932 < baseStart_2668932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668963 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 2, 2, 2]
def baseStart_2668963 : Nat := 118140960795 + 2668963 * 2 ^ 59
def prefixEnd_2668963 : Nat := 4983230072969 + 3 ^ 40 * 2668963 * 2
def baseEnd_2668963 : Nat := 1370460868065946403688169

theorem tailTrace_2668963 : CollatzResearch.WordTrace tailWord_2668963 prefixEnd_2668963 1370460868065946403688169 := by
  unfold tailWord_2668963
  simp only [CollatzResearch.WordTrace]
  refine ⟨97345077829810348435619543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64896718553206898957079695 97345077829810348435619543)
  ·
    refine ⟨146017616744715522653429315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97345077829810348435619543 146017616744715522653429315)
    ·
      refine ⟨219026425117073283980143973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146017616744715522653429315 219026425117073283980143973)
      ·
        refine ⟨41067454709451240746276995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219026425117073283980143973 41067454709451240746276995)
        ·
          refine ⟨61601182064176861119415493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41067454709451240746276995 61601182064176861119415493)
          ·
            refine ⟨11550221637033161459890405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61601182064176861119415493 11550221637033161459890405)
            ·
              refine ⟨2165666556943717773729451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11550221637033161459890405 2165666556943717773729451)
              ·
                refine ⟨3248499835415576660594177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165666556943717773729451 3248499835415576660594177)
                ·
                  refine ⟨2436374876561682495445633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248499835415576660594177 2436374876561682495445633)
                  ·
                    refine ⟨1827281157421261871584225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436374876561682495445633 1827281157421261871584225)
                    ·
                      refine ⟨1370460868065946403688169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827281157421261871584225 1370460868065946403688169)
                      ·
                        rfl

theorem cell23_2668963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_2668963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668963 prefixEnd_2668963 := by exact prefixLift 2668963
  have htrace : WordTrace (prefixWord ++ tailWord_2668963) baseStart_2668963 baseEnd_2668963 := by
    simpa [prefixWord, tailWord_2668963, baseEnd_2668963] using wordTrace_append hprefix tailTrace_2668963
  have hstable : (prefixWord ++ tailWord_2668963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668963).length < 2 ^ (prefixWord ++ tailWord_2668963).sum := by decide
  have hdescent : baseEnd_2668963 < baseStart_2668963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2668980 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2668980 : Nat := 118140960795 + 2668980 * 2 ^ 59
def prefixEnd_2668980 : Nat := 4983230072969 + 3 ^ 40 * 2668980 * 2
def baseEnd_2668980 : Nat := 1370469597237072837175591

theorem tailTrace_2668980 : CollatzResearch.WordTrace tailWord_2668980 prefixEnd_2668980 1370469597237072837175591 := by
  unfold tailWord_2668980
  simp only [CollatzResearch.WordTrace]
  refine ⟨48672848935374380169494197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64897131913832506892658929 48672848935374380169494197)
  ·
    refine ⟨4563079587691348140890081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48672848935374380169494197 4563079587691348140890081)
    ·
      refine ⟨3422309690768511105667561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4563079587691348140890081 3422309690768511105667561)
      ·
        refine ⟨2566732268076383329250671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3422309690768511105667561 2566732268076383329250671)
        ·
          refine ⟨3850098402114574993876007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566732268076383329250671 3850098402114574993876007)
          ·
            refine ⟨5775147603171862490814011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850098402114574993876007 5775147603171862490814011)
            ·
              refine ⟨8662721404757793736221017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5775147603171862490814011 8662721404757793736221017)
              ·
                refine ⟨6497041053568345302165763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8662721404757793736221017 6497041053568345302165763)
                ·
                  refine ⟨9745561580352517953248645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6497041053568345302165763 9745561580352517953248645)
                  ·
                    refine ⟨1827292796316097116234121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9745561580352517953248645 1827292796316097116234121)
                    ·
                      refine ⟨1370469597237072837175591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827292796316097116234121 1370469597237072837175591)
                      ·
                        rfl

theorem cell23_2668980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2668980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2668980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2668980 prefixEnd_2668980 := by exact prefixLift 2668980
  have htrace : WordTrace (prefixWord ++ tailWord_2668980) baseStart_2668980 baseEnd_2668980 := by
    simpa [prefixWord, tailWord_2668980, baseEnd_2668980] using wordTrace_append hprefix tailTrace_2668980
  have hstable : (prefixWord ++ tailWord_2668980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2668980).length < 2 ^ (prefixWord ++ tailWord_2668980).sum := by decide
  have hdescent : baseEnd_2668980 < baseStart_2668980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2668980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669082 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2669082 : Nat := 118140960795 + 2669082 * 2 ^ 59
def prefixEnd_2669082 : Nat := 4983230072969 + 3 ^ 40 * 2669082 * 2
def baseEnd_2669082 : Nat := 1370521972263831438100121

theorem tailTrace_2669082 : CollatzResearch.WordTrace tailWord_2669082 prefixEnd_2669082 1370521972263831438100121 := by
  unfold tailWord_2669082
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337354529094807939800375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64899612077586154506134333 24337354529094807939800375)
  ·
    refine ⟨36506031793642211909700563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24337354529094807939800375 36506031793642211909700563)
    ·
      refine ⟨54759047690463317864550845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36506031793642211909700563 54759047690463317864550845)
      ·
        refine ⟨20534642883923744199206567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54759047690463317864550845 20534642883923744199206567)
        ·
          refine ⟨30801964325885616298809851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20534642883923744199206567 30801964325885616298809851)
          ·
            refine ⟨46202946488828424448214777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30801964325885616298809851 46202946488828424448214777)
            ·
              refine ⟨34652209866621318336161083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46202946488828424448214777 34652209866621318336161083)
              ·
                refine ⟨51978314799931977504241625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34652209866621318336161083 51978314799931977504241625)
                ·
                  refine ⟨38983736099948983128181219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51978314799931977504241625 38983736099948983128181219)
                  ·
                    refine ⟨58475604149923474692271829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38983736099948983128181219 58475604149923474692271829)
                    ·
                      refine ⟨1370521972263831438100121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58475604149923474692271829 1370521972263831438100121)
                      ·
                        rfl

theorem cell23_2669082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2669082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669082 prefixEnd_2669082 := by exact prefixLift 2669082
  have htrace : WordTrace (prefixWord ++ tailWord_2669082) baseStart_2669082 baseEnd_2669082 := by
    simpa [prefixWord, tailWord_2669082, baseEnd_2669082] using wordTrace_append hprefix tailTrace_2669082
  have hstable : (prefixWord ++ tailWord_2669082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669082).length < 2 ^ (prefixWord ++ tailWord_2669082).sum := by decide
  have hdescent : baseEnd_2669082 < baseStart_2669082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669119 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 4, 4]
def baseStart_2669119 : Nat := 118140960795 + 2669119 * 2 ^ 59
def prefixEnd_2669119 : Nat := 4983230072969 + 3 ^ 40 * 2669119 * 2
def baseEnd_2669119 : Nat := 456846990349349264445817

theorem tailTrace_2669119 : CollatzResearch.WordTrace tailWord_2669119 prefixEnd_2669119 456846990349349264445817 := by
  unfold tailWord_2669119
  simp only [CollatzResearch.WordTrace]
  refine ⟨97350767617245187078298411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64900511744830124718865607 97350767617245187078298411)
  ·
    refine ⟨146026151425867780617447617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97350767617245187078298411 146026151425867780617447617)
    ·
      refine ⟨109519613569400835463085713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146026151425867780617447617 109519613569400835463085713)
      ·
        refine ⟨82139710177050626597314285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109519613569400835463085713 82139710177050626597314285)
        ·
          refine ⟨30802391316393984973992857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82139710177050626597314285 30802391316393984973992857)
          ·
            refine ⟨23101793487295488730494643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30802391316393984973992857 23101793487295488730494643)
            ·
              refine ⟨34652690230943233095741965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23101793487295488730494643 34652690230943233095741965)
              ·
                refine ⟨12994758836603712410903237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34652690230943233095741965 12994758836603712410903237)
                ·
                  refine ⟨2436517281863196077044357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12994758836603712410903237 2436517281863196077044357)
                  ·
                    refine ⟨456846990349349264445817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436517281863196077044357 456846990349349264445817)
                    ·
                      rfl

theorem cell23_2669119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_2669119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669119 prefixEnd_2669119 := by exact prefixLift 2669119
  have htrace : WordTrace (prefixWord ++ tailWord_2669119) baseStart_2669119 baseEnd_2669119 := by
    simpa [prefixWord, tailWord_2669119, baseEnd_2669119] using wordTrace_append hprefix tailTrace_2669119
  have hstable : (prefixWord ++ tailWord_2669119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669119).length < 2 ^ (prefixWord ++ tailWord_2669119).sum := by decide
  have hdescent : baseEnd_2669119 < baseStart_2669119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669160 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2669160 : Nat := 118140960795 + 2669160 * 2 ^ 59
def prefixEnd_2669160 : Nat := 4983230072969 + 3 ^ 40 * 2669160 * 2
def baseEnd_2669160 : Nat := 1370562023754882132924763

theorem tailTrace_2669160 : CollatzResearch.WordTrace tailWord_2669160 prefixEnd_2669160 1370562023754882132924763 := by
  unfold tailWord_2669160
  simp only [CollatzResearch.WordTrace]
  refine ⟨48676131505048325540270467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64901508673397767387027289 48676131505048325540270467)
  ·
    refine ⟨73014197257572488310405701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48676131505048325540270467 73014197257572488310405701)
    ·
      refine ⟨13690161985794841558201069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73014197257572488310405701 13690161985794841558201069)
      ·
        refine ⟨5133810744673065584325401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13690161985794841558201069 5133810744673065584325401)
        ·
          refine ⟨3850358058504799188244051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5133810744673065584325401 3850358058504799188244051)
          ·
            refine ⟨5775537087757198782366077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850358058504799188244051 5775537087757198782366077)
            ·
              refine ⟨2165826407908949543387279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5775537087757198782366077 2165826407908949543387279)
              ·
                refine ⟨3248739611863424315080919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165826407908949543387279 3248739611863424315080919)
                ·
                  refine ⟨4873109417795136472621379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248739611863424315080919 4873109417795136472621379)
                  ·
                    refine ⟨7309664126692704708932069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4873109417795136472621379 7309664126692704708932069)
                    ·
                      refine ⟨1370562023754882132924763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7309664126692704708932069 1370562023754882132924763)
                      ·
                        rfl

theorem cell23_2669160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2669160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669160 prefixEnd_2669160 := by exact prefixLift 2669160
  have htrace : WordTrace (prefixWord ++ tailWord_2669160) baseStart_2669160 baseEnd_2669160 := by
    simpa [prefixWord, tailWord_2669160, baseEnd_2669160] using wordTrace_append hprefix tailTrace_2669160
  have hstable : (prefixWord ++ tailWord_2669160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669160).length < 2 ^ (prefixWord ++ tailWord_2669160).sum := by decide
  have hdescent : baseEnd_2669160 < baseStart_2669160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669177 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 1, 2, 2]
def baseStart_2669177 : Nat := 118140960795 + 2669177 * 2 ^ 59
def prefixEnd_2669177 : Nat := 4983230072969 + 3 ^ 40 * 2669177 * 2
def baseEnd_2669177 : Nat := 1370570752926008566412185

theorem tailTrace_2669177 : CollatzResearch.WordTrace tailWord_2669177 prefixEnd_2669177 1370570752926008566412185 := by
  unfold tailWord_2669177
  simp only [CollatzResearch.WordTrace]
  refine ⟨97352883051035062983909785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64901922034023375322606523 97352883051035062983909785)
  ·
    refine ⟨73014662288276297237932339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97352883051035062983909785 73014662288276297237932339)
    ·
      refine ⟨109521993432414445856898509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73014662288276297237932339 109521993432414445856898509)
      ·
        refine ⟨41070747537155417196336941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109521993432414445856898509 41070747537155417196336941)
        ·
          refine ⟨15401530326433281448626353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41070747537155417196336941 15401530326433281448626353)
          ·
            refine ⟨11551147744824961086469765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15401530326433281448626353 11551147744824961086469765)
            ·
              refine ⟨2165840202154680203713081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11551147744824961086469765 2165840202154680203713081)
              ·
                refine ⟨1624380151616010152784811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165840202154680203713081 1624380151616010152784811)
                ·
                  refine ⟨2436570227424015229177217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624380151616010152784811 2436570227424015229177217)
                  ·
                    refine ⟨1827427670568011421882913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436570227424015229177217 1827427670568011421882913)
                    ·
                      refine ⟨1370570752926008566412185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827427670568011421882913 1370570752926008566412185)
                      ·
                        rfl

theorem cell23_2669177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_2669177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669177 prefixEnd_2669177 := by exact prefixLift 2669177
  have htrace : WordTrace (prefixWord ++ tailWord_2669177) baseStart_2669177 baseEnd_2669177 := by
    simpa [prefixWord, tailWord_2669177, baseEnd_2669177] using wordTrace_append hprefix tailTrace_2669177
  have hstable : (prefixWord ++ tailWord_2669177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669177).length < 2 ^ (prefixWord ++ tailWord_2669177).sum := by decide
  have hdescent : baseEnd_2669177 < baseStart_2669177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669219 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3]
def baseStart_2669219 : Nat := 118140960795 + 2669219 * 2 ^ 59
def prefixEnd_2669219 : Nat := 4983230072969 + 3 ^ 40 * 2669219 * 2
def baseEnd_2669219 : Nat := 1370592319113497402086991

theorem tailTrace_2669219 : CollatzResearch.WordTrace tailWord_2669219 prefixEnd_2669219 1370592319113497402086991 := by
  unfold tailWord_2669219
  simp only [CollatzResearch.WordTrace]
  refine ⟨97354414916882904156938711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64902943277921936104625807 97354414916882904156938711)
  ·
    refine ⟨146031622375324356235408067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97354414916882904156938711 146031622375324356235408067)
    ·
      refine ⟨219047433562986534353112101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146031622375324356235408067 219047433562986534353112101)
      ·
        refine ⟨41071393793059975191208519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219047433562986534353112101 41071393793059975191208519)
        ·
          refine ⟨61607090689589962786812779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41071393793059975191208519 61607090689589962786812779)
          ·
            refine ⟨92410636034384944180219169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61607090689589962786812779 92410636034384944180219169)
            ·
              refine ⟨69307977025788708135164377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92410636034384944180219169 69307977025788708135164377)
              ·
                refine ⟨51980982769341531101373283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69307977025788708135164377 51980982769341531101373283)
                ·
                  refine ⟨77971474154012296652059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51980982769341531101373283 77971474154012296652059925)
                  ·
                    refine ⟨3654912850969326405565309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77971474154012296652059925 3654912850969326405565309)
                    ·
                      refine ⟨1370592319113497402086991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3654912850969326405565309 1370592319113497402086991)
                      ·
                        rfl

theorem cell23_2669219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_2669219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669219 prefixEnd_2669219 := by exact prefixLift 2669219
  have htrace : WordTrace (prefixWord ++ tailWord_2669219) baseStart_2669219 baseEnd_2669219 := by
    simpa [prefixWord, tailWord_2669219, baseEnd_2669219] using wordTrace_append hprefix tailTrace_2669219
  have hstable : (prefixWord ++ tailWord_2669219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669219).length < 2 ^ (prefixWord ++ tailWord_2669219).sum := by decide
  have hdescent : baseEnd_2669219 < baseStart_2669219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669246 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2669246 : Nat := 118140960795 + 2669246 * 2 ^ 59
def prefixEnd_2669246 : Nat := 4983230072969 + 3 ^ 40 * 2669246 * 2
def baseEnd_2669246 : Nat := 1370606183091168796449367

theorem tailTrace_2669246 : CollatzResearch.WordTrace tailWord_2669246 prefixEnd_2669246 1370606183091168796449367 := by
  unfold tailWord_2669246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169424960973135971021449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64903599791856725178781061 12169424960973135971021449)
  ·
    refine ⟨9127068720729851978266087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12169424960973135971021449 9127068720729851978266087)
    ·
      refine ⟨13690603081094777967399131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127068720729851978266087 13690603081094777967399131)
      ·
        refine ⟨20535904621642166951098697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13690603081094777967399131 20535904621642166951098697)
        ·
          refine ⟨15401928466231625213324023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20535904621642166951098697 15401928466231625213324023)
          ·
            refine ⟨23102892699347437819986035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15401928466231625213324023 23102892699347437819986035)
            ·
              refine ⟨34654339049021156729979053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23102892699347437819986035 34654339049021156729979053)
              ·
                refine ⟨12995377143382933773742145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34654339049021156729979053 12995377143382933773742145)
                ·
                  refine ⟨9746532857537200330306609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12995377143382933773742145 9746532857537200330306609)
                  ·
                    refine ⟨7309899643152900247729957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9746532857537200330306609 7309899643152900247729957)
                    ·
                      refine ⟨1370606183091168796449367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7309899643152900247729957 1370606183091168796449367)
                      ·
                        rfl

theorem cell23_2669246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2669246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669246 prefixEnd_2669246 := by exact prefixLift 2669246
  have htrace : WordTrace (prefixWord ++ tailWord_2669246) baseStart_2669246 baseEnd_2669246 := by
    simpa [prefixWord, tailWord_2669246, baseEnd_2669246] using wordTrace_append hprefix tailTrace_2669246
  have hstable : (prefixWord ++ tailWord_2669246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669246).length < 2 ^ (prefixWord ++ tailWord_2669246).sum := by decide
  have hdescent : baseEnd_2669246 < baseStart_2669246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669293 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2669293 : Nat := 118140960795 + 2669293 * 2 ^ 59
def prefixEnd_2669293 : Nat := 4983230072969 + 3 ^ 40 * 2669293 * 2
def baseEnd_2669293 : Nat := 1370630316681930112561651

theorem tailTrace_2669293 : CollatzResearch.WordTrace tailWord_2669293 prefixEnd_2669293 1370630316681930112561651 := by
  unfold tailWord_2669293
  simp only [CollatzResearch.WordTrace]
  refine ⟨97357113918614814795132533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64904742612409876530088355 97357113918614814795132533)
  ·
    refine ⟨9127229429870138887043675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97357113918614814795132533 9127229429870138887043675)
    ·
      refine ⟨13690844144805208330565513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127229429870138887043675 13690844144805208330565513)
      ·
        refine ⟨10268133108603906247924135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13690844144805208330565513 10268133108603906247924135)
        ·
          refine ⟨15402199662905859371886203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268133108603906247924135 15402199662905859371886203)
          ·
            refine ⟨23103299494358789057829305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15402199662905859371886203 23103299494358789057829305)
            ·
              refine ⟨17327474620769091793371979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23103299494358789057829305 17327474620769091793371979)
              ·
                refine ⟨25991211931153637690057969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17327474620769091793371979 25991211931153637690057969)
                ·
                  refine ⟨19493408948365228267543477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25991211931153637690057969 19493408948365228267543477)
                  ·
                    refine ⟨1827507088909240150082201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19493408948365228267543477 1827507088909240150082201)
                    ·
                      refine ⟨1370630316681930112561651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827507088909240150082201 1370630316681930112561651)
                      ·
                        rfl

theorem cell23_2669293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2669293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669293 prefixEnd_2669293 := by exact prefixLift 2669293
  have htrace : WordTrace (prefixWord ++ tailWord_2669293) baseStart_2669293 baseEnd_2669293 := by
    simpa [prefixWord, tailWord_2669293, baseEnd_2669293] using wordTrace_append hprefix tailTrace_2669293
  have hstable : (prefixWord ++ tailWord_2669293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669293).length < 2 ^ (prefixWord ++ tailWord_2669293).sum := by decide
  have hdescent : baseEnd_2669293 < baseStart_2669293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669301 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2669301 : Nat := 118140960795 + 2669301 * 2 ^ 59
def prefixEnd_2669301 : Nat := 4983230072969 + 3 ^ 40 * 2669301 * 2
def baseEnd_2669301 : Nat := 1370634424527166081261615

theorem tailTrace_2669301 : CollatzResearch.WordTrace tailWord_2669301 prefixEnd_2669301 1370634424527166081261615 := by
  unfold tailWord_2669301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97357405702585832161423757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64904937135057221440949171 97357405702585832161423757)
  ·
    refine ⟨36509027138469687060533909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97357405702585832161423757 36509027138469687060533909)
    ·
      refine ⟨1711360647115766580962527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36509027138469687060533909 1711360647115766580962527)
      ·
        refine ⟨2567040970673649871443791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711360647115766580962527 2567040970673649871443791)
        ·
          refine ⟨3850561456010474807165687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567040970673649871443791 3850561456010474807165687)
          ·
            refine ⟨5775842184015712210748531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850561456010474807165687 5775842184015712210748531)
            ·
              refine ⟨8663763276023568316122797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5775842184015712210748531 8663763276023568316122797)
              ·
                refine ⟨3248911228508838118546049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8663763276023568316122797 3248911228508838118546049)
                ·
                  refine ⟨2436683421381628588909537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248911228508838118546049 2436683421381628588909537)
                  ·
                    refine ⟨1827512566036221441682153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436683421381628588909537 1827512566036221441682153)
                    ·
                      refine ⟨1370634424527166081261615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827512566036221441682153 1370634424527166081261615)
                      ·
                        rfl

theorem cell23_2669301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2669301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669301 prefixEnd_2669301 := by exact prefixLift 2669301
  have htrace : WordTrace (prefixWord ++ tailWord_2669301) baseStart_2669301 baseEnd_2669301 := by
    simpa [prefixWord, tailWord_2669301, baseEnd_2669301] using wordTrace_append hprefix tailTrace_2669301
  have hstable : (prefixWord ++ tailWord_2669301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669301).length < 2 ^ (prefixWord ++ tailWord_2669301).sum := by decide
  have hdescent : baseEnd_2669301 < baseStart_2669301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669329 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 10]
def baseStart_2669329 : Nat := 118140960795 + 2669329 * 2 ^ 59
def prefixEnd_2669329 : Nat := 4983230072969 + 3 ^ 40 * 2669329 * 2
def baseEnd_2669329 : Nat := 152294311331721330190165

theorem tailTrace_2669329 : CollatzResearch.WordTrace tailWord_2669329 prefixEnd_2669329 152294311331721330190165 := by
  unfold tailWord_2669329
  simp only [CollatzResearch.WordTrace]
  refine ⟨97358426946484392943443041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64905617964322928628962027 97358426946484392943443041)
  ·
    refine ⟨73018820209863294707582281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97358426946484392943443041 73018820209863294707582281)
    ·
      refine ⟨54764115157397471030686711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73018820209863294707582281 54764115157397471030686711)
      ·
        refine ⟨82146172736096206546030067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54764115157397471030686711 82146172736096206546030067)
        ·
          refine ⟨123219259104144309819045101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82146172736096206546030067 123219259104144309819045101)
          ·
            refine ⟨46207222164054116182141913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123219259104144309819045101 46207222164054116182141913)
            ·
              refine ⟨34655416623040587136606435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46207222164054116182141913 34655416623040587136606435)
              ·
                refine ⟨51983124934560880704909653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34655416623040587136606435 51983124934560880704909653)
                ·
                  refine ⟨152294311331721330190165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51983124934560880704909653 152294311331721330190165)
                  ·
                    rfl

theorem cell23_2669329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_2669329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669329 prefixEnd_2669329 := by exact prefixLift 2669329
  have htrace : WordTrace (prefixWord ++ tailWord_2669329) baseStart_2669329 baseEnd_2669329 := by
    simpa [prefixWord, tailWord_2669329, baseEnd_2669329] using wordTrace_append hprefix tailTrace_2669329
  have hstable : (prefixWord ++ tailWord_2669329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669329).length < 2 ^ (prefixWord ++ tailWord_2669329).sum := by decide
  have hdescent : baseEnd_2669329 < baseStart_2669329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669343 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_2669343 : Nat := 118140960795 + 2669343 * 2 ^ 59
def prefixEnd_2669343 : Nat := 4983230072969 + 3 ^ 40 * 2669343 * 2
def baseEnd_2669343 : Nat := 1370655990714654916936421

theorem tailTrace_2669343 : CollatzResearch.WordTrace tailWord_2669343 prefixEnd_2669343 1370655990714654916936421 := by
  unfold tailWord_2669343
  simp only [CollatzResearch.WordTrace]
  refine ⟨97358937568433673334452683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64905958378955782222968455 97358937568433673334452683)
  ·
    refine ⟨146038406352650510001679025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97358937568433673334452683 146038406352650510001679025)
    ·
      refine ⟨109528804764487882501259269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146038406352650510001679025 109528804764487882501259269)
      ·
        refine ⟨20536650893341477968986113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109528804764487882501259269 20536650893341477968986113)
        ·
          refine ⟨15402488170006108476739585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20536650893341477968986113 15402488170006108476739585)
          ·
            refine ⟨11551866127504581357554689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15402488170006108476739585 11551866127504581357554689)
            ·
              refine ⟨8663899595628436018166017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11551866127504581357554689 8663899595628436018166017)
              ·
                refine ⟨6497924696721327013624513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8663899595628436018166017 6497924696721327013624513)
                ·
                  refine ⟨4873443522540995260218385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6497924696721327013624513 4873443522540995260218385)
                  ·
                    refine ⟨3655082641905746445163789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4873443522540995260218385 3655082641905746445163789)
                    ·
                      refine ⟨1370655990714654916936421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3655082641905746445163789 1370655990714654916936421)
                      ·
                        rfl

theorem cell23_2669343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_2669343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669343 prefixEnd_2669343 := by exact prefixLift 2669343
  have htrace : WordTrace (prefixWord ++ tailWord_2669343) baseStart_2669343 baseEnd_2669343 := by
    simpa [prefixWord, tailWord_2669343, baseEnd_2669343] using wordTrace_append hprefix tailTrace_2669343
  have hstable : (prefixWord ++ tailWord_2669343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669343).length < 2 ^ (prefixWord ++ tailWord_2669343).sum := by decide
  have hdescent : baseEnd_2669343 < baseStart_2669343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669359 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 11]
def baseStart_2669359 : Nat := 118140960795 + 2669359 * 2 ^ 59
def prefixEnd_2669359 : Nat := 4983230072969 + 3 ^ 40 * 2669359 * 2
def baseEnd_2669359 : Nat := 456888068801708951445449

theorem tailTrace_2669359 : CollatzResearch.WordTrace tailWord_2669359 prefixEnd_2669359 456888068801708951445449 := by
  unfold tailWord_2669359
  simp only [CollatzResearch.WordTrace]
  refine ⟨97359521136375708067035131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64906347424250472044690087 97359521136375708067035131)
  ·
    refine ⟨146039281704563562100552697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97359521136375708067035131 146039281704563562100552697)
    ·
      refine ⟨109529461278422671575414523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146039281704563562100552697 109529461278422671575414523)
      ·
        refine ⟨164294191917634007363121785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109529461278422671575414523 164294191917634007363121785)
        ·
          refine ⟨123220643938225505522341339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164294191917634007363121785 123220643938225505522341339)
          ·
            refine ⟨184830965907338258283512009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123220643938225505522341339 184830965907338258283512009)
            ·
              refine ⟨138623224430503693712634007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184830965907338258283512009 138623224430503693712634007)
              ·
                refine ⟨207934836645755540568951011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138623224430503693712634007 207934836645755540568951011)
                ·
                  refine ⟨311902254968633310853426517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207934836645755540568951011 311902254968633310853426517)
                  ·
                    refine ⟨456888068801708951445449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 311902254968633310853426517 456888068801708951445449)
                    ·
                      rfl

theorem cell23_2669359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_2669359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669359 prefixEnd_2669359 := by exact prefixLift 2669359
  have htrace : WordTrace (prefixWord ++ tailWord_2669359) baseStart_2669359 baseEnd_2669359 := by
    simpa [prefixWord, tailWord_2669359, baseEnd_2669359] using wordTrace_append hprefix tailTrace_2669359
  have hstable : (prefixWord ++ tailWord_2669359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669359).length < 2 ^ (prefixWord ++ tailWord_2669359).sum := by decide
  have hdescent : baseEnd_2669359 < baseStart_2669359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669423 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 2, 4]
def baseStart_2669423 : Nat := 118140960795 + 2669423 * 2 ^ 59
def prefixEnd_2669423 : Nat := 4983230072969 + 3 ^ 40 * 2669423 * 2
def baseEnd_2669423 : Nat := 456899023055671534645351

theorem tailTrace_2669423 : CollatzResearch.WordTrace tailWord_2669423 prefixEnd_2669423 456899023055671534645351 := by
  unfold tailWord_2669423
  simp only [CollatzResearch.WordTrace]
  refine ⟨97361855408143846997364923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64907903605429231331576615 97361855408143846997364923)
  ·
    refine ⟨146042783112215770496047385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97361855408143846997364923 146042783112215770496047385)
    ·
      refine ⟨109532087334161827872035539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146042783112215770496047385 109532087334161827872035539)
      ·
        refine ⟨164298131001242741808053309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109532087334161827872035539 164298131001242741808053309)
        ·
          refine ⟨61611799125466028178019991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164298131001242741808053309 61611799125466028178019991)
          ·
            refine ⟨92417698688199042267029987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61611799125466028178019991 92417698688199042267029987)
            ·
              refine ⟨138626548032298563400544981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92417698688199042267029987 138626548032298563400544981)
              ·
                refine ⟨3249059719506997579700273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138626548032298563400544981 3249059719506997579700273)
                ·
                  refine ⟨2436794789630248184775205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249059719506997579700273 2436794789630248184775205)
                  ·
                    refine ⟨456899023055671534645351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436794789630248184775205 456899023055671534645351)
                    ·
                      rfl

theorem cell23_2669423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_2669423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669423 prefixEnd_2669423 := by exact prefixLift 2669423
  have htrace : WordTrace (prefixWord ++ tailWord_2669423) baseStart_2669423 baseEnd_2669423 := by
    simpa [prefixWord, tailWord_2669423, baseEnd_2669423] using wordTrace_append hprefix tailTrace_2669423
  have hstable : (prefixWord ++ tailWord_2669423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669423).length < 2 ^ (prefixWord ++ tailWord_2669423).sum := by decide
  have hdescent : baseEnd_2669423 < baseStart_2669423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669450 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2669450 : Nat := 118140960795 + 2669450 * 2 ^ 59
def prefixEnd_2669450 : Nat := 4983230072969 + 3 ^ 40 * 2669450 * 2
def baseEnd_2669450 : Nat := 1370710933144685998298429

theorem tailTrace_2669450 : CollatzResearch.WordTrace tailWord_2669450 prefixEnd_2669450 1370710933144685998298429 := by
  unfold tailWord_2669450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24340710044761507652149451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64908560119364020405731869 24340710044761507652149451)
  ·
    refine ⟨36511065067142261478224177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24340710044761507652149451 36511065067142261478224177)
    ·
      refine ⟨27383298800356696108668133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36511065067142261478224177 27383298800356696108668133)
      ·
        refine ⟨5134368525066880520375275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27383298800356696108668133 5134368525066880520375275)
        ·
          refine ⟨7701552787600320780562913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5134368525066880520375275 7701552787600320780562913)
          ·
            refine ⟨5776164590700240585422185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7701552787600320780562913 5776164590700240585422185)
            ·
              refine ⟨4332123443025180439066639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5776164590700240585422185 4332123443025180439066639)
              ·
                refine ⟨6498185164537770658599959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332123443025180439066639 6498185164537770658599959)
                ·
                  refine ⟨9747277746806655987899939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6498185164537770658599959 9747277746806655987899939)
                  ·
                    refine ⟨14620916620209983981849909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9747277746806655987899939 14620916620209983981849909)
                    ·
                      refine ⟨1370710933144685998298429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14620916620209983981849909 1370710933144685998298429)
                      ·
                        rfl

theorem cell23_2669450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2669450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669450 prefixEnd_2669450 := by exact prefixLift 2669450
  have htrace : WordTrace (prefixWord ++ tailWord_2669450) baseStart_2669450 baseEnd_2669450 := by
    simpa [prefixWord, tailWord_2669450, baseEnd_2669450] using wordTrace_append hprefix tailTrace_2669450
  have hstable : (prefixWord ++ tailWord_2669450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669450).length < 2 ^ (prefixWord ++ tailWord_2669450).sum := by decide
  have hdescent : baseEnd_2669450 < baseStart_2669450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669474 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2669474 : Nat := 118140960795 + 2669474 * 2 ^ 59
def prefixEnd_2669474 : Nat := 4983230072969 + 3 ^ 40 * 2669474 * 2
def baseEnd_2669474 : Nat := 456907752226797968132773

theorem tailTrace_2669474 : CollatzResearch.WordTrace tailWord_2669474 prefixEnd_2669474 456907752226797968132773 := by
  unfold tailWord_2669474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24340928882739770676867869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64909143687306055138314317 24340928882739770676867869)
  ·
    refine ⟨9127848331027414003825451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24340928882739770676867869 9127848331027414003825451)
    ·
      refine ⟨13691772496541121005738177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127848331027414003825451 13691772496541121005738177)
      ·
        refine ⟨10268829372405840754303633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13691772496541121005738177 10268829372405840754303633)
        ·
          refine ⟨7701622029304380565727725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10268829372405840754303633 7701622029304380565727725)
          ·
            refine ⟨2888108260989142712147897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7701622029304380565727725 2888108260989142712147897)
            ·
              refine ⟨2166081195741857034110923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888108260989142712147897 2166081195741857034110923)
              ·
                refine ⟨3249121793612785551166385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166081195741857034110923 3249121793612785551166385)
                ·
                  refine ⟨2436841345209589163374789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249121793612785551166385 2436841345209589163374789)
                  ·
                    refine ⟨456907752226797968132773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436841345209589163374789 456907752226797968132773)
                    ·
                      rfl

theorem cell23_2669474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2669474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669474 prefixEnd_2669474 := by exact prefixLift 2669474
  have htrace : WordTrace (prefixWord ++ tailWord_2669474) baseStart_2669474 baseEnd_2669474 := by
    simpa [prefixWord, tailWord_2669474, baseEnd_2669474] using wordTrace_append hprefix tailTrace_2669474
  have hstable : (prefixWord ++ tailWord_2669474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669474).length < 2 ^ (prefixWord ++ tailWord_2669474).sum := by decide
  have hdescent : baseEnd_2669474 < baseStart_2669474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669543 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 9]
def baseStart_2669543 : Nat := 118140960795 + 2669543 * 2 ^ 59
def prefixEnd_2669543 : Nat := 4983230072969 + 3 ^ 40 * 2669543 * 2
def baseEnd_2669543 : Nat := 152306520760617126048389

theorem tailTrace_2669543 : CollatzResearch.WordTrace tailWord_2669543 prefixEnd_2669543 152306520760617126048389 := by
  unfold tailWord_2669543
  simp only [CollatzResearch.WordTrace]
  refine ⟨97366232167709107491733283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64910821445139404994488855 97366232167709107491733283)
  ·
    refine ⟨146049348251563661237599925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97366232167709107491733283 146049348251563661237599925)
    ·
      refine ⟨13692126398584093241024993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146049348251563661237599925 13692126398584093241024993)
      ·
        refine ⟨10269094798938069930768745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13692126398584093241024993 10269094798938069930768745)
        ·
          refine ⟨7701821099203552448076559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10269094798938069930768745 7701821099203552448076559)
          ·
            refine ⟨11552731648805328672114839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701821099203552448076559 11552731648805328672114839)
            ·
              refine ⟨17329097473207993008172259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11552731648805328672114839 17329097473207993008172259)
              ·
                refine ⟨25993646209811989512258389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17329097473207993008172259 25993646209811989512258389)
                ·
                  refine ⟨152306520760617126048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25993646209811989512258389 152306520760617126048389)
                  ·
                    rfl

theorem cell23_2669543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 9].length) (baseStart_2669543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669543 prefixEnd_2669543 := by exact prefixLift 2669543
  have htrace : WordTrace (prefixWord ++ tailWord_2669543) baseStart_2669543 baseEnd_2669543 := by
    simpa [prefixWord, tailWord_2669543, baseEnd_2669543] using wordTrace_append hprefix tailTrace_2669543
  have hstable : (prefixWord ++ tailWord_2669543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669543).length < 2 ^ (prefixWord ++ tailWord_2669543).sum := by decide
  have hdescent : baseEnd_2669543 < baseStart_2669543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669573 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2669573 : Nat := 118140960795 + 2669573 * 2 ^ 59
def prefixEnd_2669573 : Nat := 4983230072969 + 3 ^ 40 * 2669573 * 2
def baseEnd_2669573 : Nat := 456924697088396339020121

theorem tailTrace_2669573 : CollatzResearch.WordTrace tailWord_2669573 prefixEnd_2669573 456924697088396339020121 := by
  unfold tailWord_2669573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97367326357600422615325373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64911550905066948410216915 97367326357600422615325373)
  ·
    refine ⟨36512747384100158480747015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97367326357600422615325373 36512747384100158480747015)
    ·
      refine ⟨54769121076150237721120523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36512747384100158480747015 54769121076150237721120523)
      ·
        refine ⟨82153681614225356581680785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54769121076150237721120523 82153681614225356581680785)
        ·
          refine ⟨61615261210669017436260589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82153681614225356581680785 61615261210669017436260589)
          ·
            refine ⟨23105722954000881538597721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61615261210669017436260589 23105722954000881538597721)
            ·
              refine ⟨17329292215500661153948291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23105722954000881538597721 17329292215500661153948291)
              ·
                refine ⟨25993938323250991730922437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17329292215500661153948291 25993938323250991730922437)
                ·
                  refine ⟨4873863435609560949547957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25993938323250991730922437 4873863435609560949547957)
                  ·
                    refine ⟨456924697088396339020121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4873863435609560949547957 456924697088396339020121)
                    ·
                      rfl

theorem cell23_2669573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2669573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669573 prefixEnd_2669573 := by exact prefixLift 2669573
  have htrace : WordTrace (prefixWord ++ tailWord_2669573) baseStart_2669573 baseEnd_2669573 := by
    simpa [prefixWord, tailWord_2669573, baseEnd_2669573] using wordTrace_append hprefix tailTrace_2669573
  have hstable : (prefixWord ++ tailWord_2669573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669573).length < 2 ^ (prefixWord ++ tailWord_2669573).sum := by decide
  have hdescent : baseEnd_2669573 < baseStart_2669573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669593 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2669593 : Nat := 118140960795 + 2669593 * 2 ^ 59
def prefixEnd_2669593 : Nat := 4983230072969 + 3 ^ 40 * 2669593 * 2
def baseEnd_2669593 : Nat := 1370784360878278938810271

theorem tailTrace_2669593 : CollatzResearch.WordTrace tailWord_2669593 prefixEnd_2669593 1370784360878278938810271 := by
  unfold tailWord_2669593
  simp only [CollatzResearch.WordTrace]
  refine ⟨97368055817527966031053433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64912037211685310687368955 97368055817527966031053433)
  ·
    refine ⟨73026041863145974523290075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97368055817527966031053433 73026041863145974523290075)
    ·
      refine ⟨109539062794718961784935113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73026041863145974523290075 109539062794718961784935113)
      ·
        refine ⟨82154297096039221338701335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109539062794718961784935113 82154297096039221338701335)
        ·
          refine ⟨123231445644058832008052003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82154297096039221338701335 123231445644058832008052003)
          ·
            refine ⟨184847168466088248012078005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123231445644058832008052003 184847168466088248012078005)
            ·
              refine ⟨17329422043695773251132313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184847168466088248012078005 17329422043695773251132313)
              ·
                refine ⟨12997066532771829938349235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17329422043695773251132313 12997066532771829938349235)
                ·
                  refine ⟨19495599799157744907523853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12997066532771829938349235 19495599799157744907523853)
                  ·
                    refine ⟨7310849924684154340321445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19495599799157744907523853 7310849924684154340321445)
                    ·
                      refine ⟨1370784360878278938810271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7310849924684154340321445 1370784360878278938810271)
                      ·
                        rfl

theorem cell23_2669593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2669593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669593 prefixEnd_2669593 := by exact prefixLift 2669593
  have htrace : WordTrace (prefixWord ++ tailWord_2669593) baseStart_2669593 baseEnd_2669593 := by
    simpa [prefixWord, tailWord_2669593, baseEnd_2669593] using wordTrace_append hprefix tailTrace_2669593
  have hstable : (prefixWord ++ tailWord_2669593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669593).length < 2 ^ (prefixWord ++ tailWord_2669593).sum := by decide
  have hdescent : baseEnd_2669593 < baseStart_2669593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669637 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_2669637 : Nat := 118140960795 + 2669637 * 2 ^ 59
def prefixEnd_2669637 : Nat := 4983230072969 + 3 ^ 40 * 2669637 * 2
def baseEnd_2669637 : Nat := 456935651342358922220023

theorem tailTrace_2669637 : CollatzResearch.WordTrace tailWord_2669637 prefixEnd_2669637 456935651342358922220023 := by
  unfold tailWord_2669637
  simp only [CollatzResearch.WordTrace]
  refine ⟨97369660629368561545655165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64913107086245707697103443 97369660629368561545655165)
  ·
    refine ⟨36513622736013210579620687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97369660629368561545655165 36513622736013210579620687)
    ·
      refine ⟨54770434104019815869431031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36513622736013210579620687 54770434104019815869431031)
      ·
        refine ⟨82155651156029723804146547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54770434104019815869431031 82155651156029723804146547)
        ·
          refine ⟨123233476734044585706219821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82155651156029723804146547 123233476734044585706219821)
          ·
            refine ⟨46212553775266719639832433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123233476734044585706219821 46212553775266719639832433)
            ·
              refine ⟨34659415331450039729874325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46212553775266719639832433 34659415331450039729874325)
              ·
                refine ⟨1624660093661720612337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34659415331450039729874325 1624660093661720612337859)
                ·
                  refine ⟨2436990140492580918506789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624660093661720612337859 2436990140492580918506789)
                  ·
                    refine ⟨456935651342358922220023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2436990140492580918506789 456935651342358922220023)
                    ·
                      rfl

theorem cell23_2669637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_2669637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669637 prefixEnd_2669637 := by exact prefixLift 2669637
  have htrace : WordTrace (prefixWord ++ tailWord_2669637) baseStart_2669637 baseEnd_2669637 := by
    simpa [prefixWord, tailWord_2669637, baseEnd_2669637] using wordTrace_append hprefix tailTrace_2669637
  have hstable : (prefixWord ++ tailWord_2669637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669637).length < 2 ^ (prefixWord ++ tailWord_2669637).sum := by decide
  have hdescent : baseEnd_2669637 < baseStart_2669637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669687 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_2669687 : Nat := 118140960795 + 2669687 * 2 ^ 59
def prefixEnd_2669687 : Nat := 4983230072969 + 3 ^ 40 * 2669687 * 2
def baseEnd_2669687 : Nat := 1370832628059801571034839

theorem tailTrace_2669687 : CollatzResearch.WordTrace tailWord_2669687 prefixEnd_2669687 1370832628059801571034839 := by
  unfold tailWord_2669687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97371484279187420084975315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64914322852791613389983543 97371484279187420084975315)
  ·
    refine ⟨146057226418781130127462973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97371484279187420084975315 146057226418781130127462973)
    ·
      refine ⟨54771459907042923797798615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146057226418781130127462973 54771459907042923797798615)
      ·
        refine ⟨82157189860564385696697923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54771459907042923797798615 82157189860564385696697923)
        ·
          refine ⟨123235784790846578545046885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82157189860564385696697923 123235784790846578545046885)
          ·
            refine ⟨23106709648283733477196291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123235784790846578545046885 23106709648283733477196291)
            ·
              refine ⟨34660064472425600215794437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23106709648283733477196291 34660064472425600215794437)
              ·
                refine ⟨6498762088579800040461457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34660064472425600215794437 6498762088579800040461457)
                ·
                  refine ⟨4874071566434850030346093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6498762088579800040461457 4874071566434850030346093)
                  ·
                    refine ⟨1827776837413068761379785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874071566434850030346093 1827776837413068761379785)
                    ·
                      refine ⟨1370832628059801571034839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827776837413068761379785 1370832628059801571034839)
                      ·
                        rfl

theorem cell23_2669687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_2669687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669687 prefixEnd_2669687 := by exact prefixLift 2669687
  have htrace : WordTrace (prefixWord ++ tailWord_2669687) baseStart_2669687 baseEnd_2669687 := by
    simpa [prefixWord, tailWord_2669687, baseEnd_2669687] using wordTrace_append hprefix tailTrace_2669687
  have hstable : (prefixWord ++ tailWord_2669687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669687).length < 2 ^ (prefixWord ++ tailWord_2669687).sum := by decide
  have hdescent : baseEnd_2669687 < baseStart_2669687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669751 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_2669751 : Nat := 118140960795 + 2669751 * 2 ^ 59
def prefixEnd_2669751 : Nat := 4983230072969 + 3 ^ 40 * 2669751 * 2
def baseEnd_2669751 : Nat := 1370865490821689320634545

theorem tailTrace_2669751 : CollatzResearch.WordTrace tailWord_2669751 prefixEnd_2669751 1370865490821689320634545 := by
  unfold tailWord_2669751
  simp only [CollatzResearch.WordTrace]
  refine ⟨97373818550955559015305107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64915879033970372676870071 97373818550955559015305107)
  ·
    refine ⟨146060727826433338522957661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97373818550955559015305107 146060727826433338522957661)
    ·
      refine ⟨54772772934912501946109123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146060727826433338522957661 54772772934912501946109123)
      ·
        refine ⟨82159159402368752919163685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54772772934912501946109123 82159159402368752919163685)
        ·
          refine ⟨15404842387944141172343191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82159159402368752919163685 15404842387944141172343191)
          ·
            refine ⟨23107263581916211758514787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15404842387944141172343191 23107263581916211758514787)
            ·
              refine ⟨34660895372874317637772181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23107263581916211758514787 34660895372874317637772181)
              ·
                refine ⟨1624729470603483639270571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34660895372874317637772181 1624729470603483639270571)
                ·
                  refine ⟨2437094205905225458905857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624729470603483639270571 2437094205905225458905857)
                  ·
                    refine ⟨1827820654428919094179393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437094205905225458905857 1827820654428919094179393)
                    ·
                      refine ⟨1370865490821689320634545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827820654428919094179393 1370865490821689320634545)
                      ·
                        rfl

theorem cell23_2669751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_2669751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669751 prefixEnd_2669751 := by exact prefixLift 2669751
  have htrace : WordTrace (prefixWord ++ tailWord_2669751) baseStart_2669751 baseEnd_2669751 := by
    simpa [prefixWord, tailWord_2669751, baseEnd_2669751] using wordTrace_append hprefix tailTrace_2669751
  have hstable : (prefixWord ++ tailWord_2669751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669751).length < 2 ^ (prefixWord ++ tailWord_2669751).sum := by decide
  have hdescent : baseEnd_2669751 < baseStart_2669751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669774 : List Nat := [4, 1, 1, 1, 5, 2, 2, 7]
def baseStart_2669774 : Nat := 118140960795 + 2669774 * 2 ^ 59
def prefixEnd_2669774 : Nat := 4983230072969 + 3 ^ 40 * 2669774 * 2
def baseEnd_2669774 : Nat := 50773233365805286320257

theorem tailTrace_2669774 : CollatzResearch.WordTrace tailWord_2669774 prefixEnd_2669774 50773233365805286320257 := by
  unfold tailWord_2669774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12171832178734029242924047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64916438286581489295594917 12171832178734029242924047)
  ·
    refine ⟨18257748268101043864386071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12171832178734029242924047 18257748268101043864386071)
    ·
      refine ⟨27386622402151565796579107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18257748268101043864386071 27386622402151565796579107)
      ·
        refine ⟨41079933603227348694868661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27386622402151565796579107 41079933603227348694868661)
        ·
          refine ⟨3851243775302563940143937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41079933603227348694868661 3851243775302563940143937)
          ·
            refine ⟨2888432831476922955107953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851243775302563940143937 2888432831476922955107953)
            ·
              refine ⟨2166324623607692216330965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888432831476922955107953 2166324623607692216330965)
              ·
                refine ⟨50773233365805286320257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2166324623607692216330965 50773233365805286320257)
                ·
                  rfl

theorem cell23_2669774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_2669774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669774 prefixEnd_2669774 := by exact prefixLift 2669774
  have htrace : WordTrace (prefixWord ++ tailWord_2669774) baseStart_2669774 baseEnd_2669774 := by
    simpa [prefixWord, tailWord_2669774, baseEnd_2669774] using wordTrace_append hprefix tailTrace_2669774
  have hstable : (prefixWord ++ tailWord_2669774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669774).length < 2 ^ (prefixWord ++ tailWord_2669774).sum := by decide
  have hdescent : baseEnd_2669774 < baseStart_2669774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669812 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2669812 : Nat := 118140960795 + 2669812 * 2 ^ 59
def prefixEnd_2669812 : Nat := 4983230072969 + 3 ^ 40 * 2669812 * 2
def baseEnd_2669812 : Nat := 456965604380537860657255

theorem tailTrace_2669812 : CollatzResearch.WordTrace tailWord_2669812 prefixEnd_2669812 456965604380537860657255 := by
  unfold tailWord_2669812
  simp only [CollatzResearch.WordTrace]
  refine ⟨48688021701867283216637845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64917362269156377622183793 48688021701867283216637845)
  ·
    refine ⟨2282251017275028900779899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48688021701867283216637845 2282251017275028900779899)
    ·
      refine ⟨3423376525912543351169849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282251017275028900779899 3423376525912543351169849)
      ·
        refine ⟨2567532394434407513377387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423376525912543351169849 2567532394434407513377387)
        ·
          refine ⟨3851298591651611270066081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567532394434407513377387 3851298591651611270066081)
          ·
            refine ⟨2888473943738708452549561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851298591651611270066081 2888473943738708452549561)
            ·
              refine ⟨2166355457804031339412171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888473943738708452549561 2166355457804031339412171)
              ·
                refine ⟨3249533186706047009118257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166355457804031339412171 3249533186706047009118257)
                ·
                  refine ⟨2437149890029535256838693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249533186706047009118257 2437149890029535256838693)
                  ·
                    refine ⟨456965604380537860657255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437149890029535256838693 456965604380537860657255)
                    ·
                      rfl

theorem cell23_2669812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2669812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669812 prefixEnd_2669812 := by exact prefixLift 2669812
  have htrace : WordTrace (prefixWord ++ tailWord_2669812) baseStart_2669812 baseEnd_2669812 := by
    simpa [prefixWord, tailWord_2669812, baseEnd_2669812] using wordTrace_append hprefix tailTrace_2669812
  have hstable : (prefixWord ++ tailWord_2669812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669812).length < 2 ^ (prefixWord ++ tailWord_2669812).sum := by decide
  have hdescent : baseEnd_2669812 < baseStart_2669812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669828 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2669828 : Nat := 118140960795 + 2669828 * 2 ^ 59
def prefixEnd_2669828 : Nat := 4983230072969 + 3 ^ 40 * 2669828 * 2
def baseEnd_2669828 : Nat := 1370905028832085519371691

theorem tailTrace_2669828 : CollatzResearch.WordTrace tailWord_2669828 prefixEnd_2669828 1370905028832085519371691 := by
  unfold tailWord_2669828
  simp only [CollatzResearch.WordTrace]
  refine ⟨48688313485838300582929069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64917751314451067443905425 48688313485838300582929069)
  ·
    refine ⟨18258117557189362718598401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48688313485838300582929069 18258117557189362718598401)
    ·
      refine ⟨13693588167892022038948801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18258117557189362718598401 13693588167892022038948801)
      ·
        refine ⟨10270191125919016529211601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13693588167892022038948801 10270191125919016529211601)
        ·
          refine ⟨7702643344439262396908701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270191125919016529211601 7702643344439262396908701)
          ·
            refine ⟨2888491254164723398840763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7702643344439262396908701 2888491254164723398840763)
            ·
              refine ⟨4332736881247085098261145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888491254164723398840763 4332736881247085098261145)
              ·
                refine ⟨3249552660935313823695859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4332736881247085098261145 3249552660935313823695859)
                ·
                  refine ⟨4874328991402970735543789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249552660935313823695859 4874328991402970735543789)
                  ·
                    refine ⟨1827873371776114025828921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874328991402970735543789 1827873371776114025828921)
                    ·
                      refine ⟨1370905028832085519371691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827873371776114025828921 1370905028832085519371691)
                      ·
                        rfl

theorem cell23_2669828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2669828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669828 prefixEnd_2669828 := by exact prefixLift 2669828
  have htrace : WordTrace (prefixWord ++ tailWord_2669828) baseStart_2669828 baseEnd_2669828 := by
    simpa [prefixWord, tailWord_2669828, baseEnd_2669828] using wordTrace_append hprefix tailTrace_2669828
  have hstable : (prefixWord ++ tailWord_2669828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669828).length < 2 ^ (prefixWord ++ tailWord_2669828).sum := by decide
  have hdescent : baseEnd_2669828 < baseStart_2669828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669857 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2669857 : Nat := 118140960795 + 2669857 * 2 ^ 59
def prefixEnd_2669857 : Nat := 4983230072969 + 3 ^ 40 * 2669857 * 2
def baseEnd_2669857 : Nat := 1370919919771065905909057

theorem tailTrace_2669857 : CollatzResearch.WordTrace tailWord_2669857 prefixEnd_2669857 1370919919771065905909057 := by
  unfold tailWord_2669857
  simp only [CollatzResearch.WordTrace]
  refine ⟨97377684688571539118663825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64918456459047692745775883 97377684688571539118663825)
  ·
    refine ⟨73033263516428654338997869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97377684688571539118663825 73033263516428654338997869)
    ·
      refine ⟨27387473818660745377124201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73033263516428654338997869 27387473818660745377124201)
      ·
        refine ⟨20540605363995559032843151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27387473818660745377124201 20540605363995559032843151)
        ·
          refine ⟨30810908045993338549264727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20540605363995559032843151 30810908045993338549264727)
          ·
            refine ⟨46216362068990007823897091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30810908045993338549264727 46216362068990007823897091)
            ·
              refine ⟨69324543103485011735845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46216362068990007823897091 69324543103485011735845637)
              ·
                refine ⟨12998351831903439700471057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69324543103485011735845637 12998351831903439700471057)
                ·
                  refine ⟨9748763873927579775353293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998351831903439700471057 9748763873927579775353293)
                  ·
                    refine ⟨3655786452722842415757485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9748763873927579775353293 3655786452722842415757485)
                    ·
                      refine ⟨1370919919771065905909057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3655786452722842415757485 1370919919771065905909057)
                      ·
                        rfl

theorem cell23_2669857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2669857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669857 prefixEnd_2669857 := by exact prefixLift 2669857
  have htrace : WordTrace (prefixWord ++ tailWord_2669857) baseStart_2669857 baseEnd_2669857 := by
    simpa [prefixWord, tailWord_2669857, baseEnd_2669857] using wordTrace_append hprefix tailTrace_2669857
  have hstable : (prefixWord ++ tailWord_2669857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669857).length < 2 ^ (prefixWord ++ tailWord_2669857).sum := by decide
  have hdescent : baseEnd_2669857 < baseStart_2669857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669874 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_2669874 : Nat := 118140960795 + 2669874 * 2 ^ 59
def prefixEnd_2669874 : Nat := 4983230072969 + 3 ^ 40 * 2669874 * 2
def baseEnd_2669874 : Nat := 1370928648942192339396479

theorem tailTrace_2669874 : CollatzResearch.WordTrace tailWord_2669874 prefixEnd_2669874 1370928648942192339396479 := by
  unfold tailWord_2669874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344576182377487755508169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64918869819673300681355117 24344576182377487755508169)
  ·
    refine ⟨18258432136783115816631127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24344576182377487755508169 18258432136783115816631127)
    ·
      refine ⟨27387648205174673724946691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258432136783115816631127 27387648205174673724946691)
      ·
        refine ⟨41081472307762010587420037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27387648205174673724946691 41081472307762010587420037)
        ·
          refine ⟨7702776057705376985141257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41081472307762010587420037 7702776057705376985141257)
          ·
            refine ⟨5777082043279032738855943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7702776057705376985141257 5777082043279032738855943)
            ·
              refine ⟨8665623064918549108283915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5777082043279032738855943 8665623064918549108283915)
              ·
                refine ⟨12998434597377823662425873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8665623064918549108283915 12998434597377823662425873)
                ·
                  refine ⟨9748825948033367746819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998434597377823662425873 9748825948033367746819405)
                  ·
                    refine ⟨3655809730512512905057277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9748825948033367746819405 3655809730512512905057277)
                    ·
                      refine ⟨1370928648942192339396479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3655809730512512905057277 1370928648942192339396479)
                      ·
                        rfl

theorem cell23_2669874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_2669874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669874 prefixEnd_2669874 := by exact prefixLift 2669874
  have htrace : WordTrace (prefixWord ++ tailWord_2669874) baseStart_2669874 baseEnd_2669874 := by
    simpa [prefixWord, tailWord_2669874, baseEnd_2669874] using wordTrace_append hprefix tailTrace_2669874
  have hstable : (prefixWord ++ tailWord_2669874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669874).length < 2 ^ (prefixWord ++ tailWord_2669874).sum := by decide
  have hdescent : baseEnd_2669874 < baseStart_2669874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669907 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 5, 4]
def baseStart_2669907 : Nat := 118140960795 + 2669907 * 2 ^ 59
def prefixEnd_2669907 : Nat := 4983230072969 + 3 ^ 40 * 2669907 * 2
def baseEnd_2669907 : Nat := 456981864601263570094609

theorem tailTrace_2669907 : CollatzResearch.WordTrace tailWord_2669907 prefixEnd_2669907 456981864601263570094609 := by
  unfold tailWord_2669907
  simp only [CollatzResearch.WordTrace]
  refine ⟨97379508338390397657983975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64919672225593598438655983 97379508338390397657983975)
  ·
    refine ⟨146069262507585596486975963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97379508338390397657983975 146069262507585596486975963)
    ·
      refine ⟨219103893761378394730463945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146069262507585596486975963 219103893761378394730463945)
      ·
        refine ⟨164327920321033796047847959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219103893761378394730463945 164327920321033796047847959)
        ·
          refine ⟨246491880481550694071771939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164327920321033796047847959 246491880481550694071771939)
          ·
            refine ⟨369737820722326041107657909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246491880481550694071771939 369737820722326041107657909)
            ·
              refine ⟨34662920692718066353842929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 369737820722326041107657909 34662920692718066353842929)
              ·
                refine ⟨25997190519538549765382197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34662920692718066353842929 25997190519538549765382197)
                ·
                  refine ⟨2437236611206739040504581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25997190519538549765382197 2437236611206739040504581)
                  ·
                    refine ⟨456981864601263570094609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437236611206739040504581 456981864601263570094609)
                    ·
                      rfl

theorem cell23_2669907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 4].length) (baseStart_2669907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669907 prefixEnd_2669907 := by exact prefixLift 2669907
  have htrace : WordTrace (prefixWord ++ tailWord_2669907) baseStart_2669907 baseEnd_2669907 := by
    simpa [prefixWord, tailWord_2669907, baseEnd_2669907] using wordTrace_append hprefix tailTrace_2669907
  have hstable : (prefixWord ++ tailWord_2669907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669907).length < 2 ^ (prefixWord ++ tailWord_2669907).sum := by decide
  have hdescent : baseEnd_2669907 < baseStart_2669907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669914 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_2669914 : Nat := 118140960795 + 2669914 * 2 ^ 59
def prefixEnd_2669914 : Nat := 4983230072969 + 3 ^ 40 * 2669914 * 2
def baseEnd_2669914 : Nat := 1370949188168372182896295

theorem tailTrace_2669914 : CollatzResearch.WordTrace tailWord_2669914 prefixEnd_2669914 1370949188168372182896295 := by
  unfold tailWord_2669914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344940912341259463372199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64919842432910025235659197 24344940912341259463372199)
  ·
    refine ⟨36517411368511889195058299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24344940912341259463372199 36517411368511889195058299)
    ·
      refine ⟨54776117052767833792587449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36517411368511889195058299 54776117052767833792587449)
      ·
        refine ⟨41082087789575875344440587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54776117052767833792587449 41082087789575875344440587)
        ·
          refine ⟨61623131684363813016660881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41082087789575875344440587 61623131684363813016660881)
          ·
            refine ⟨46217348763272859762495661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61623131684363813016660881 46217348763272859762495661)
            ·
              refine ⟨17331505786227322410935873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46217348763272859762495661 17331505786227322410935873)
              ·
                refine ⟨12998629339670491808201905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17331505786227322410935873 12998629339670491808201905)
                ·
                  refine ⟨9748972004752868856151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12998629339670491808201905 9748972004752868856151429)
                  ·
                    refine ⟨1827932250891162910528393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9748972004752868856151429 1827932250891162910528393)
                    ·
                      refine ⟨1370949188168372182896295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827932250891162910528393 1370949188168372182896295)
                      ·
                        rfl

theorem cell23_2669914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_2669914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669914 prefixEnd_2669914 := by exact prefixLift 2669914
  have htrace : WordTrace (prefixWord ++ tailWord_2669914) baseStart_2669914 baseEnd_2669914 := by
    simpa [prefixWord, tailWord_2669914, baseEnd_2669914] using wordTrace_append hprefix tailTrace_2669914
  have hstable : (prefixWord ++ tailWord_2669914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669914).length < 2 ^ (prefixWord ++ tailWord_2669914).sum := by decide
  have hdescent : baseEnd_2669914 < baseStart_2669914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669924 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2669924 : Nat := 118140960795 + 2669924 * 2 ^ 59
def prefixEnd_2669924 : Nat := 4983230072969 + 3 ^ 40 * 2669924 * 2
def baseEnd_2669924 : Nat := 456984774324972381257083

theorem tailTrace_2669924 : CollatzResearch.WordTrace tailWord_2669924 prefixEnd_2669924 456984774324972381257083 := by
  unfold tailWord_2669924
  simp only [CollatzResearch.WordTrace]
  refine ⟨48690064189664404780676413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64920085586219206374235217 48690064189664404780676413)
  ·
    refine ⟨18258774071124151792753655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48690064189664404780676413 18258774071124151792753655)
    ·
      refine ⟨27388161106686227689130483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258774071124151792753655 27388161106686227689130483)
      ·
        refine ⟨41082241660029341533695725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27388161106686227689130483 41082241660029341533695725)
        ·
          refine ⟨15405840622511003075135897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41082241660029341533695725 15405840622511003075135897)
          ·
            refine ⟨11554380466883252306351923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15405840622511003075135897 11554380466883252306351923)
            ·
              refine ⟨17331570700324878459527885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11554380466883252306351923 17331570700324878459527885)
              ·
                refine ⟨6499339012621829422322957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17331570700324878459527885 6499339012621829422322957)
                ·
                  refine ⟨2437252129733186033371109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6499339012621829422322957 2437252129733186033371109)
                  ·
                    refine ⟨456984774324972381257083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437252129733186033371109 456984774324972381257083)
                    ·
                      rfl

theorem cell23_2669924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2669924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669924 prefixEnd_2669924 := by exact prefixLift 2669924
  have htrace : WordTrace (prefixWord ++ tailWord_2669924) baseStart_2669924 baseEnd_2669924 := by
    simpa [prefixWord, tailWord_2669924, baseEnd_2669924] using wordTrace_append hprefix tailTrace_2669924
  have hstable : (prefixWord ++ tailWord_2669924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669924).length < 2 ^ (prefixWord ++ tailWord_2669924).sum := by decide
  have hdescent : baseEnd_2669924 < baseStart_2669924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669937 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 6]
def baseStart_2669937 : Nat := 118140960795 + 2669937 * 2 ^ 59
def prefixEnd_2669937 : Nat := 4983230072969 + 3 ^ 40 * 2669937 * 2
def baseEnd_2669937 : Nat := 152328999802602843656521

theorem tailTrace_2669937 : CollatzResearch.WordTrace tailWord_2669937 prefixEnd_2669937 152328999802602843656521 := by
  unfold tailWord_2669937
  simp only [CollatzResearch.WordTrace]
  refine ⟨97380602528281712781576065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64920401685521141854384043 97380602528281712781576065)
  ·
    refine ⟨73035451896211284586182049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97380602528281712781576065 73035451896211284586182049)
    ·
      refine ⟨54776588922158463439636537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73035451896211284586182049 54776588922158463439636537)
      ·
        refine ⟨41082441691618847579727403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54776588922158463439636537 41082441691618847579727403)
        ·
          refine ⟨61623662537428271369591105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41082441691618847579727403 61623662537428271369591105)
          ·
            refine ⟨46217746903071203527193329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61623662537428271369591105 46217746903071203527193329)
            ·
              refine ⟨34663310177303402645394997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46217746903071203527193329 34663310177303402645394997)
              ·
                refine ⟨3249685329122193998005781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34663310177303402645394997 3249685329122193998005781)
                ·
                  refine ⟨152328999802602843656521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3249685329122193998005781 152328999802602843656521)
                  ·
                    rfl

theorem cell23_2669937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_2669937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669937 prefixEnd_2669937 := by exact prefixLift 2669937
  have htrace : WordTrace (prefixWord ++ tailWord_2669937) baseStart_2669937 baseEnd_2669937 := by
    simpa [prefixWord, tailWord_2669937, baseEnd_2669937] using wordTrace_append hprefix tailTrace_2669937
  have hstable : (prefixWord ++ tailWord_2669937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669937).length < 2 ^ (prefixWord ++ tailWord_2669937).sum := by decide
  have hdescent : baseEnd_2669937 < baseStart_2669937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669947 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3]
def baseStart_2669947 : Nat := 118140960795 + 2669947 * 2 ^ 59
def prefixEnd_2669947 : Nat := 4983230072969 + 3 ^ 40 * 2669947 * 2
def baseEnd_2669947 : Nat := 1370966133029970553783643

theorem tailTrace_2669947 : CollatzResearch.WordTrace tailWord_2669947 prefixEnd_2669947 1370966133029970553783643 := by
  unfold tailWord_2669947
  simp only [CollatzResearch.WordTrace]
  refine ⟨97380967258245484489440095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64920644838830322992960063 97380967258245484489440095)
  ·
    refine ⟨146071450887368226734160143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97380967258245484489440095 146071450887368226734160143)
    ·
      refine ⟨219107176331052340101240215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146071450887368226734160143 219107176331052340101240215)
      ·
        refine ⟨328660764496578510151860323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219107176331052340101240215 328660764496578510151860323)
        ·
          refine ⟨492991146744867765227790485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328660764496578510151860323 492991146744867765227790485)
          ·
            refine ⟨23108960003665676495052679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 492991146744867765227790485 23108960003665676495052679)
            ·
              refine ⟨34663440005498514742579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23108960003665676495052679 34663440005498514742579019)
              ·
                refine ⟨51995160008247772113868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34663440005498514742579019 51995160008247772113868529)
                ·
                  refine ⟨38996370006185829085401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51995160008247772113868529 38996370006185829085401397)
                  ·
                    refine ⟨3655909688079921476756381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38996370006185829085401397 3655909688079921476756381)
                    ·
                      refine ⟨1370966133029970553783643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3655909688079921476756381 1370966133029970553783643)
                      ·
                        rfl

theorem cell23_2669947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].length) (baseStart_2669947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669947 prefixEnd_2669947 := by exact prefixLift 2669947
  have htrace : WordTrace (prefixWord ++ tailWord_2669947) baseStart_2669947 baseEnd_2669947 := by
    simpa [prefixWord, tailWord_2669947, baseEnd_2669947] using wordTrace_append hprefix tailTrace_2669947
  have hstable : (prefixWord ++ tailWord_2669947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669947).length < 2 ^ (prefixWord ++ tailWord_2669947).sum := by decide
  have hdescent : baseEnd_2669947 < baseStart_2669947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2669991 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2669991 : Nat := 118140960795 + 2669991 * 2 ^ 59
def prefixEnd_2669991 : Nat := 4983230072969 + 3 ^ 40 * 2669991 * 2
def baseEnd_2669991 : Nat := 1370988726178768381633441

theorem tailTrace_2669991 : CollatzResearch.WordTrace tailWord_2669991 prefixEnd_2669991 1370988726178768381633441 := by
  unfold tailWord_2669991
  simp only [CollatzResearch.WordTrace]
  refine ⟨97382572070086080004041827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64921714713390720002694551 97382572070086080004041827)
  ·
    refine ⟨146073858105129120006062741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97382572070086080004041827 146073858105129120006062741)
    ·
      refine ⟨6847212098677927500284191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146073858105129120006062741 6847212098677927500284191)
      ·
        refine ⟨10270818148016891250426287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847212098677927500284191 10270818148016891250426287)
        ·
          refine ⟨15406227222025336875639431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270818148016891250426287 15406227222025336875639431)
          ·
            refine ⟨23109340833038005313459147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15406227222025336875639431 23109340833038005313459147)
            ·
              refine ⟨34664011249557007970188721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23109340833038005313459147 34664011249557007970188721)
              ·
                refine ⟨25998008437167755977641541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34664011249557007970188721 25998008437167755977641541)
                ·
                  refine ⟨4874626581968954245807789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25998008437167755977641541 4874626581968954245807789)
                  ·
                    refine ⟨1827984968238357842177921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874626581968954245807789 1827984968238357842177921)
                    ·
                      refine ⟨1370988726178768381633441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1827984968238357842177921 1370988726178768381633441)
                      ·
                        rfl

theorem cell23_2669991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2669991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2669991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2669991 prefixEnd_2669991 := by exact prefixLift 2669991
  have htrace : WordTrace (prefixWord ++ tailWord_2669991) baseStart_2669991 baseEnd_2669991 := by
    simpa [prefixWord, tailWord_2669991, baseEnd_2669991] using wordTrace_append hprefix tailTrace_2669991
  have hstable : (prefixWord ++ tailWord_2669991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2669991).length < 2 ^ (prefixWord ++ tailWord_2669991).sum := by decide
  have hdescent : baseEnd_2669991 < baseStart_2669991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2669991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670051 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2670051 : Nat := 118140960795 + 2670051 * 2 ^ 59
def prefixEnd_2670051 : Nat := 4983230072969 + 3 ^ 40 * 2670051 * 2
def baseEnd_2670051 : Nat := 1371019535018038146883165

theorem tailTrace_2670051 : CollatzResearch.WordTrace tailWord_2670051 prefixEnd_2670051 1371019535018038146883165 := by
  unfold tailWord_2670051
  simp only [CollatzResearch.WordTrace]
  refine ⟨97384760449868710251226007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64923173633245806834150671 97384760449868710251226007)
  ·
    refine ⟨146077140674803065376839011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97384760449868710251226007 146077140674803065376839011)
    ·
      refine ⟨219115711012204598065258517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146077140674803065376839011 219115711012204598065258517)
      ·
        refine ⟨10271048953697090534308993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 219115711012204598065258517 10271048953697090534308993)
        ·
          refine ⟨7703286715272817900731745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10271048953697090534308993 7703286715272817900731745)
          ·
            refine ⟨5777465036454613425548809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7703286715272817900731745 5777465036454613425548809)
            ·
              refine ⟨4333098777340960069161607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777465036454613425548809 4333098777340960069161607)
              ·
                refine ⟨6499648166011440103742411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333098777340960069161607 6499648166011440103742411)
                ·
                  refine ⟨9749472249017160155613617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6499648166011440103742411 9749472249017160155613617)
                  ·
                    refine ⟨7312104186762870116710213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9749472249017160155613617 7312104186762870116710213)
                    ·
                      refine ⟨1371019535018038146883165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7312104186762870116710213 1371019535018038146883165)
                      ·
                        rfl

theorem cell23_2670051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2670051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670051 prefixEnd_2670051 := by exact prefixLift 2670051
  have htrace : WordTrace (prefixWord ++ tailWord_2670051) baseStart_2670051 baseEnd_2670051 := by
    simpa [prefixWord, tailWord_2670051, baseEnd_2670051] using wordTrace_append hprefix tailTrace_2670051
  have hstable : (prefixWord ++ tailWord_2670051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670051).length < 2 ^ (prefixWord ++ tailWord_2670051).sum := by decide
  have hdescent : baseEnd_2670051 < baseStart_2670051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670088 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2670088 : Nat := 118140960795 + 2670088 * 2 ^ 59
def prefixEnd_2670088 : Nat := 4983230072969 + 3 ^ 40 * 2670088 * 2
def baseEnd_2670088 : Nat := 1371038533802254502120495

theorem tailTrace_2670088 : CollatzResearch.WordTrace tailWord_2670088 prefixEnd_2670088 1371038533802254502120495 := by
  unfold tailWord_2670088
  simp only [CollatzResearch.WordTrace]
  refine ⟨48693054975367332785161459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64924073300489777046881945 48693054975367332785161459)
  ·
    refine ⟨73039582463050999177742189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48693054975367332785161459 73039582463050999177742189)
    ·
      refine ⟨27389843423644124691653321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73039582463050999177742189 27389843423644124691653321)
      ·
        refine ⟨20542382567733093518739991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27389843423644124691653321 20542382567733093518739991)
        ·
          refine ⟨30813573851599640278109987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20542382567733093518739991 30813573851599640278109987)
          ·
            refine ⟨46220360777399460417164981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30813573851599640278109987 46220360777399460417164981)
            ·
              refine ⟨4333158822881199414109217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46220360777399460417164981 4333158822881199414109217)
              ·
                refine ⟨3249869117160899560581913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333158822881199414109217 3249869117160899560581913)
                ·
                  refine ⟨2437401837870674670436435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249869117160899560581913 2437401837870674670436435)
                  ·
                    refine ⟨3656102756806012005654653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2437401837870674670436435 3656102756806012005654653)
                    ·
                      refine ⟨1371038533802254502120495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3656102756806012005654653 1371038533802254502120495)
                      ·
                        rfl

theorem cell23_2670088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2670088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670088 prefixEnd_2670088 := by exact prefixLift 2670088
  have htrace : WordTrace (prefixWord ++ tailWord_2670088) baseStart_2670088 baseEnd_2670088 := by
    simpa [prefixWord, tailWord_2670088, baseEnd_2670088] using wordTrace_append hprefix tailTrace_2670088
  have hstable : (prefixWord ++ tailWord_2670088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670088).length < 2 ^ (prefixWord ++ tailWord_2670088).sum := by decide
  have hdescent : baseEnd_2670088 < baseStart_2670088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670107 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_2670107 : Nat := 118140960795 + 2670107 * 2 ^ 59
def prefixEnd_2670107 : Nat := 4983230072969 + 3 ^ 40 * 2670107 * 2
def baseEnd_2670107 : Nat := 1371048289934689927782907

theorem tailTrace_2670107 : CollatzResearch.WordTrace tailWord_2670107 prefixEnd_2670107 1371048289934689927782907 := by
  unfold tailWord_2670107
  simp only [CollatzResearch.WordTrace]
  refine ⟨97386802937665831815264575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64924535291777221210176383 97386802937665831815264575)
  ·
    refine ⟨146080204406498747722896863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97386802937665831815264575 146080204406498747722896863)
    ·
      refine ⟨219120306609748121584345295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146080204406498747722896863 219120306609748121584345295)
      ·
        refine ⟨328680459914622182376517943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219120306609748121584345295 328680459914622182376517943)
        ·
          refine ⟨493020689871933273564776915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328680459914622182376517943 493020689871933273564776915)
          ·
            refine ⟨739531034807899910347165373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493020689871933273564776915 739531034807899910347165373)
            ·
              refine ⟨277324138052962466380187015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739531034807899910347165373 277324138052962466380187015)
              ·
                refine ⟨415986207079443699570280523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277324138052962466380187015 415986207079443699570280523)
                ·
                  refine ⟨623979310619165549355420785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415986207079443699570280523 623979310619165549355420785)
                  ·
                    refine ⟨467984482964374162016565589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623979310619165549355420785 467984482964374162016565589)
                    ·
                      refine ⟨1371048289934689927782907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 467984482964374162016565589 1371048289934689927782907)
                      ·
                        rfl

theorem cell23_2670107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_2670107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670107 prefixEnd_2670107 := by exact prefixLift 2670107
  have htrace : WordTrace (prefixWord ++ tailWord_2670107) baseStart_2670107 baseEnd_2670107 := by
    simpa [prefixWord, tailWord_2670107, baseEnd_2670107] using wordTrace_append hprefix tailTrace_2670107
  have hstable : (prefixWord ++ tailWord_2670107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670107).length < 2 ^ (prefixWord ++ tailWord_2670107).sum := by decide
  have hdescent : baseEnd_2670107 < baseStart_2670107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670115 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 1, 3, 2]
def baseStart_2670115 : Nat := 118140960795 + 2670115 * 2 ^ 59
def prefixEnd_2670115 : Nat := 4983230072969 + 3 ^ 40 * 2670115 * 2
def baseEnd_2670115 : Nat := 1371052397779925896482871

theorem tailTrace_2670115 : CollatzResearch.WordTrace tailWord_2670115 prefixEnd_2670115 1371052397779925896482871 := by
  unfold tailWord_2670115
  simp only [CollatzResearch.WordTrace]
  refine ⟨97387094721636849181555799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64924729814424566121037199 97387094721636849181555799)
  ·
    refine ⟨146080642082455273772333699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97387094721636849181555799 146080642082455273772333699)
    ·
      refine ⟨219120963123682910658500549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146080642082455273772333699 219120963123682910658500549)
      ·
        refine ⟨41085180585690545748468853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219120963123682910658500549 41085180585690545748468853)
        ·
          refine ⟨3851735679908488663918955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41085180585690545748468853 3851735679908488663918955)
          ·
            refine ⟨5777603519862732995878433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3851735679908488663918955 5777603519862732995878433)
            ·
              refine ⟨4333202639897049746908825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777603519862732995878433 4333202639897049746908825)
              ·
                refine ⟨3249901979922787310181619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333202639897049746908825 3249901979922787310181619)
                ·
                  refine ⟨4874852969884180965272429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249901979922787310181619 4874852969884180965272429)
                  ·
                    refine ⟨1828069863706567861977161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874852969884180965272429 1828069863706567861977161)
                    ·
                      refine ⟨1371052397779925896482871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828069863706567861977161 1371052397779925896482871)
                      ·
                        rfl

theorem cell23_2670115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_2670115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670115 prefixEnd_2670115 := by exact prefixLift 2670115
  have htrace : WordTrace (prefixWord ++ tailWord_2670115) baseStart_2670115 baseEnd_2670115 := by
    simpa [prefixWord, tailWord_2670115, baseEnd_2670115] using wordTrace_append hprefix tailTrace_2670115
  have hstable : (prefixWord ++ tailWord_2670115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670115).length < 2 ^ (prefixWord ++ tailWord_2670115).sum := by decide
  have hdescent : baseEnd_2670115 < baseStart_2670115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670145 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2670145 : Nat := 118140960795 + 2670145 * 2 ^ 59
def prefixEnd_2670145 : Nat := 4983230072969 + 3 ^ 40 * 2670145 * 2
def baseEnd_2670145 : Nat := 1371067802199560779107733

theorem tailTrace_2670145 : CollatzResearch.WordTrace tailWord_2670145 prefixEnd_2670145 1371067802199560779107733 := by
  unfold tailWord_2670145
  simp only [CollatzResearch.WordTrace]
  refine ⟨97388188911528164305147889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64925459274352109536765259 97388188911528164305147889)
  ·
    refine ⟨73041141683646123228860917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97388188911528164305147889 73041141683646123228860917)
    ·
      refine ⟨6847607032841824052705711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73041141683646123228860917 6847607032841824052705711)
      ·
        refine ⟨10271410549262736079058567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847607032841824052705711 10271410549262736079058567)
        ·
          refine ⟨15407115823894104118587851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10271410549262736079058567 15407115823894104118587851)
          ·
            refine ⟨23110673735841156177881777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15407115823894104118587851 23110673735841156177881777)
            ·
              refine ⟨17333005301880867133411333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23110673735841156177881777 17333005301880867133411333)
              ·
                refine ⟨3249938494102662587514625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17333005301880867133411333 3249938494102662587514625)
                ·
                  refine ⟨2437453870576996940635969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249938494102662587514625 2437453870576996940635969)
                  ·
                    refine ⟨1828090402932747705476977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437453870576996940635969 1828090402932747705476977)
                    ·
                      refine ⟨1371067802199560779107733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828090402932747705476977 1371067802199560779107733)
                      ·
                        rfl

theorem cell23_2670145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2670145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670145 prefixEnd_2670145 := by exact prefixLift 2670145
  have htrace : WordTrace (prefixWord ++ tailWord_2670145) baseStart_2670145 baseEnd_2670145 := by
    simpa [prefixWord, tailWord_2670145, baseEnd_2670145] using wordTrace_append hprefix tailTrace_2670145
  have hstable : (prefixWord ++ tailWord_2670145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670145).length < 2 ^ (prefixWord ++ tailWord_2670145).sum := by decide
  have hdescent : baseEnd_2670145 < baseStart_2670145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670162 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_2670162 : Nat := 118140960795 + 2670162 * 2 ^ 59
def prefixEnd_2670162 : Nat := 4983230072969 + 3 ^ 40 * 2670162 * 2
def baseEnd_2670162 : Nat := 1371076531370687212595155

theorem tailTrace_2670162 : CollatzResearch.WordTrace tailWord_2670162 prefixEnd_2670162 1371076531370687212595155 := by
  unfold tailWord_2670162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347202238116644052129185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64925872634977717472344493 24347202238116644052129185)
  ·
    refine ⟨18260401678587483039096889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24347202238116644052129185 18260401678587483039096889)
    ·
      refine ⟨13695301258940612279322667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18260401678587483039096889 13695301258940612279322667)
      ·
        refine ⟨20542951888410918418984001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13695301258940612279322667 20542951888410918418984001)
        ·
          refine ⟨15407213916308188814238001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20542951888410918418984001 15407213916308188814238001)
          ·
            refine ⟨11555410437231141610678501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15407213916308188814238001 11555410437231141610678501)
            ·
              refine ⟨2166639456980839052002219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11555410437231141610678501 2166639456980839052002219)
              ·
                refine ⟨3249959185471258578003329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166639456980839052002219 3249959185471258578003329)
                ·
                  refine ⟨2437469389103443933502497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3249959185471258578003329 2437469389103443933502497)
                  ·
                    refine ⟨1828102041827582950126873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437469389103443933502497 1828102041827582950126873)
                    ·
                      refine ⟨1371076531370687212595155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828102041827582950126873 1371076531370687212595155)
                      ·
                        rfl

theorem cell23_2670162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_2670162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670162 prefixEnd_2670162 := by exact prefixLift 2670162
  have htrace : WordTrace (prefixWord ++ tailWord_2670162) baseStart_2670162 baseEnd_2670162 := by
    simpa [prefixWord, tailWord_2670162, baseEnd_2670162] using wordTrace_append hprefix tailTrace_2670162
  have hstable : (prefixWord ++ tailWord_2670162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670162).length < 2 ^ (prefixWord ++ tailWord_2670162).sum := by decide
  have hdescent : baseEnd_2670162 < baseStart_2670162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670166 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2670166 : Nat := 118140960795 + 2670166 * 2 ^ 59
def prefixEnd_2670166 : Nat := 4983230072969 + 3 ^ 40 * 2670166 * 2
def baseEnd_2670166 : Nat := 1371078585293305196945137

theorem tailTrace_2670166 : CollatzResearch.WordTrace tailWord_2670166 prefixEnd_2670166 1371078585293305196945137 := by
  unfold tailWord_2670166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086809677778255305728897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64925969896301389927774901 6086809677778255305728897)
  ·
    refine ⟨4565107258333691479296673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6086809677778255305728897 4565107258333691479296673)
    ·
      refine ⟨3423830443750268609472505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4565107258333691479296673 3423830443750268609472505)
      ·
        refine ⟨2567872832812701457104379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423830443750268609472505 2567872832812701457104379)
        ·
          refine ⟨3851809249219052185656569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567872832812701457104379 3851809249219052185656569)
          ·
            refine ⟨2888856936914289139242427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851809249219052185656569 2888856936914289139242427)
            ·
              refine ⟨4333285405371433708863641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888856936914289139242427 4333285405371433708863641)
              ·
                refine ⟨3249964054028575281647731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333285405371433708863641 3249964054028575281647731)
                ·
                  refine ⟨4874946081042862922471597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249964054028575281647731 4874946081042862922471597)
                  ·
                    refine ⟨1828104780391073595926849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4874946081042862922471597 1828104780391073595926849)
                    ·
                      refine ⟨1371078585293305196945137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828104780391073595926849 1371078585293305196945137)
                      ·
                        rfl

theorem cell23_2670166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2670166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670166 prefixEnd_2670166 := by exact prefixLift 2670166
  have htrace : WordTrace (prefixWord ++ tailWord_2670166) baseStart_2670166 baseEnd_2670166 := by
    simpa [prefixWord, tailWord_2670166, baseEnd_2670166] using wordTrace_append hprefix tailTrace_2670166
  have hstable : (prefixWord ++ tailWord_2670166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670166).length < 2 ^ (prefixWord ++ tailWord_2670166).sum := by decide
  have hdescent : baseEnd_2670166 < baseStart_2670166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670181 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_2670181 : Nat := 118140960795 + 2670181 * 2 ^ 59
def prefixEnd_2670181 : Nat := 4983230072969 + 3 ^ 40 * 2670181 * 2
def baseEnd_2670181 : Nat := 457028762501040879419189

theorem tailTrace_2670181 : CollatzResearch.WordTrace tailWord_2670181 prefixEnd_2670181 457028762501040879419189 := by
  unfold tailWord_2670181
  simp only [CollatzResearch.WordTrace]
  refine ⟨97389501939397742453458397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64926334626265161635638931 97389501939397742453458397)
  ·
    refine ⟨36521063227274153420046899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97389501939397742453458397 36521063227274153420046899)
    ·
      refine ⟨54781594840911230130070349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36521063227274153420046899 54781594840911230130070349)
      ·
        refine ⟨20543098065341711298776381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54781594840911230130070349 20543098065341711298776381)
        ·
          refine ⟨7703661774503141737041143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20543098065341711298776381 7703661774503141737041143)
          ·
            refine ⟨11555492661754712605561715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703661774503141737041143 11555492661754712605561715)
            ·
              refine ⟨17333238992632068908342573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11555492661754712605561715 17333238992632068908342573)
              ·
                refine ⟨6499964622237025840628465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17333238992632068908342573 6499964622237025840628465)
                ·
                  refine ⟨4874973466677769380471349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499964622237025840628465 4874973466677769380471349)
                  ·
                    refine ⟨457028762501040879419189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4874973466677769380471349 457028762501040879419189)
                    ·
                      rfl

theorem cell23_2670181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_2670181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670181 prefixEnd_2670181 := by exact prefixLift 2670181
  have htrace : WordTrace (prefixWord ++ tailWord_2670181) baseStart_2670181 baseEnd_2670181 := by
    simpa [prefixWord, tailWord_2670181, baseEnd_2670181] using wordTrace_append hprefix tailTrace_2670181
  have hstable : (prefixWord ++ tailWord_2670181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670181).length < 2 ^ (prefixWord ++ tailWord_2670181).sum := by decide
  have hdescent : baseEnd_2670181 < baseStart_2670181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670198 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2670198 : Nat := 118140960795 + 2670198 * 2 ^ 59
def prefixEnd_2670198 : Nat := 4983230072969 + 3 ^ 40 * 2670198 * 2
def baseEnd_2670198 : Nat := 457031672224749690581663

theorem tailTrace_2670198 : CollatzResearch.WordTrace tailWord_2670198 prefixEnd_2670198 457031672224749690581663 := by
  unfold tailWord_2670198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086882623771009647301703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64926747986890769571218165 6086882623771009647301703)
  ·
    refine ⟨9130323935656514470952555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6086882623771009647301703 9130323935656514470952555)
    ·
      refine ⟨13695485903484771706428833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9130323935656514470952555 13695485903484771706428833)
      ·
        refine ⟨10271614427613578779821625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13695485903484771706428833 10271614427613578779821625)
        ·
          refine ⟨7703710820710184084866219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10271614427613578779821625 7703710820710184084866219)
          ·
            refine ⟨11555566231065276127299329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703710820710184084866219 11555566231065276127299329)
            ·
              refine ⟨8666674673298957095474497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11555566231065276127299329 8666674673298957095474497)
              ·
                refine ⟨6500006004974217821605873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666674673298957095474497 6500006004974217821605873)
                ·
                  refine ⟨4875004503730663366204405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500006004974217821605873 4875004503730663366204405)
                  ·
                    refine ⟨457031672224749690581663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4875004503730663366204405 457031672224749690581663)
                    ·
                      rfl

theorem cell23_2670198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2670198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670198 prefixEnd_2670198 := by exact prefixLift 2670198
  have htrace : WordTrace (prefixWord ++ tailWord_2670198) baseStart_2670198 baseEnd_2670198 := by
    simpa [prefixWord, tailWord_2670198, baseEnd_2670198] using wordTrace_append hprefix tailTrace_2670198
  have hstable : (prefixWord ++ tailWord_2670198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670198).length < 2 ^ (prefixWord ++ tailWord_2670198).sum := by decide
  have hdescent : baseEnd_2670198 < baseStart_2670198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670201 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2670201 : Nat := 118140960795 + 2670201 * 2 ^ 59
def prefixEnd_2670201 : Nat := 4983230072969 + 3 ^ 40 * 2670201 * 2
def baseEnd_2670201 : Nat := 1371096557116212560007475

theorem tailTrace_2670201 : CollatzResearch.WordTrace tailWord_2670201 prefixEnd_2670201 1371096557116212560007475 := by
  unfold tailWord_2670201
  simp only [CollatzResearch.WordTrace]
  refine ⟨97390231399325285869186457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64926820932883523912790971 97390231399325285869186457)
  ·
    refine ⟨73042673549493964401889843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97390231399325285869186457 73042673549493964401889843)
    ·
      refine ⟨109564010324240946602834765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73042673549493964401889843 109564010324240946602834765)
      ·
        refine ⟨41086503871590354976063037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109564010324240946602834765 41086503871590354976063037)
        ·
          refine ⟨15407438951846383116023639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41086503871590354976063037 15407438951846383116023639)
          ·
            refine ⟨23111158427769574674035459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15407438951846383116023639 23111158427769574674035459)
            ·
              refine ⟨34666737641654362011053189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23111158427769574674035459 34666737641654362011053189)
              ·
                refine ⟨6500013307810192877072473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34666737641654362011053189 6500013307810192877072473)
                ·
                  refine ⟨4875009980857644657804355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6500013307810192877072473 4875009980857644657804355)
                  ·
                    refine ⟨7312514971286466986706533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4875009980857644657804355 7312514971286466986706533)
                    ·
                      refine ⟨1371096557116212560007475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7312514971286466986706533 1371096557116212560007475)
                      ·
                        rfl

theorem cell23_2670201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2670201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670201 prefixEnd_2670201 := by exact prefixLift 2670201
  have htrace : WordTrace (prefixWord ++ tailWord_2670201) baseStart_2670201 baseEnd_2670201 := by
    simpa [prefixWord, tailWord_2670201, baseEnd_2670201] using wordTrace_append hprefix tailTrace_2670201
  have hstable : (prefixWord ++ tailWord_2670201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670201).length < 2 ^ (prefixWord ++ tailWord_2670201).sum := by decide
  have hdescent : baseEnd_2670201 < baseStart_2670201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670204 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2670204 : Nat := 118140960795 + 2670204 * 2 ^ 59
def prefixEnd_2670204 : Nat := 4983230072969 + 3 ^ 40 * 2670204 * 2
def baseEnd_2670204 : Nat := 1371098097558176048269961

theorem tailTrace_2670204 : CollatzResearch.WordTrace tailWord_2670204 prefixEnd_2670204 1371098097558176048269961 := by
  unfold tailWord_2670204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48695170409157208690772833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64926893878876278254363777 48695170409157208690772833)
  ·
    refine ⟨36521377806867906518079625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48695170409157208690772833 36521377806867906518079625)
    ·
      refine ⟨27391033355150929888559719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36521377806867906518079625 27391033355150929888559719)
      ·
        refine ⟨41086550032726394832839579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27391033355150929888559719 41086550032726394832839579)
        ·
          refine ⟨61629825049089592249259369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41086550032726394832839579 61629825049089592249259369)
          ·
            refine ⟨46222368786817194186944527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61629825049089592249259369 46222368786817194186944527)
            ·
              refine ⟨69333553180225791280416791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46222368786817194186944527 69333553180225791280416791)
              ·
                refine ⟨104000329770338686920625187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69333553180225791280416791 104000329770338686920625187)
                ·
                  refine ⟨156000494655508030380937781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104000329770338686920625187 156000494655508030380937781)
                  ·
                    refine ⟨14625046373953877848212917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156000494655508030380937781 14625046373953877848212917)
                    ·
                      refine ⟨1371098097558176048269961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14625046373953877848212917 1371098097558176048269961)
                      ·
                        rfl

theorem cell23_2670204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2670204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670204 prefixEnd_2670204 := by exact prefixLift 2670204
  have htrace : WordTrace (prefixWord ++ tailWord_2670204) baseStart_2670204 baseEnd_2670204 := by
    simpa [prefixWord, tailWord_2670204, baseEnd_2670204] using wordTrace_append hprefix tailTrace_2670204
  have hstable : (prefixWord ++ tailWord_2670204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670204).length < 2 ^ (prefixWord ++ tailWord_2670204).sum := by decide
  have hdescent : baseEnd_2670204 < baseStart_2670204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670211 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 3, 4]
def baseStart_2670211 : Nat := 118140960795 + 2670211 * 2 ^ 59
def prefixEnd_2670211 : Nat := 4983230072969 + 3 ^ 40 * 2670211 * 2
def baseEnd_2670211 : Nat := 457033897307585840294143

theorem tailTrace_2670211 : CollatzResearch.WordTrace tailWord_2670211 prefixEnd_2670211 457033897307585840294143 := by
  unfold tailWord_2670211
  simp only [CollatzResearch.WordTrace]
  refine ⟨97390596129289057577050487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64927064086192705051366991 97390596129289057577050487)
  ·
    refine ⟨146085894193933586365575731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97390596129289057577050487 146085894193933586365575731)
    ·
      refine ⟨219128841290900379548363597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146085894193933586365575731 219128841290900379548363597)
      ·
        refine ⟨82173315484087642330636349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219128841290900379548363597 82173315484087642330636349)
        ·
          refine ⟨30814993306532865873988631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82173315484087642330636349 30814993306532865873988631)
          ·
            refine ⟨46222489959799298810982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30814993306532865873988631 46222489959799298810982947)
            ·
              refine ⟨69333734939698948216474421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46222489959799298810982947 69333734939698948216474421)
              ·
                refine ⟨6500037650596776395294477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69333734939698948216474421 6500037650596776395294477)
                ·
                  refine ⟨2437514118973791148235429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6500037650596776395294477 2437514118973791148235429)
                  ·
                    refine ⟨457033897307585840294143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437514118973791148235429 457033897307585840294143)
                    ·
                      rfl

theorem cell23_2670211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 4].length) (baseStart_2670211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670211 prefixEnd_2670211 := by exact prefixLift 2670211
  have htrace : WordTrace (prefixWord ++ tailWord_2670211) baseStart_2670211 baseEnd_2670211 := by
    simpa [prefixWord, tailWord_2670211, baseEnd_2670211] using wordTrace_append hprefix tailTrace_2670211
  have hstable : (prefixWord ++ tailWord_2670211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670211).length < 2 ^ (prefixWord ++ tailWord_2670211).sum := by decide
  have hdescent : baseEnd_2670211 < baseStart_2670211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670218 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_2670218 : Nat := 118140960795 + 2670218 * 2 ^ 59
def prefixEnd_2670218 : Nat := 4983230072969 + 3 ^ 40 * 2670218 * 2
def baseEnd_2670218 : Nat := 1371105286287338993494897

theorem tailTrace_2670218 : CollatzResearch.WordTrace tailWord_2670218 prefixEnd_2670218 1371105286287338993494897 := by
  unfold tailWord_2670218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347712860065924443138827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64927234293509131848370205 24347712860065924443138827)
  ·
    refine ⟨36521569290098886664708241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24347712860065924443138827 36521569290098886664708241)
    ·
      refine ⟨27391176967574164998531181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36521569290098886664708241 27391176967574164998531181)
      ·
        refine ⟨10271691362840311874449193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27391176967574164998531181 10271691362840311874449193)
        ·
          refine ⟨7703768522130233905836895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10271691362840311874449193 7703768522130233905836895)
          ·
            refine ⟨11555652783195350858755343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703768522130233905836895 11555652783195350858755343)
            ·
              refine ⟨17333479174793026288133015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11555652783195350858755343 17333479174793026288133015)
              ·
                refine ⟨26000218762189539432199523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17333479174793026288133015 26000218762189539432199523)
                ·
                  refine ⟨39000328143284309148299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26000218762189539432199523 39000328143284309148299285)
                  ·
                    refine ⟨1828140381716451991326529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39000328143284309148299285 1828140381716451991326529)
                    ·
                      refine ⟨1371105286287338993494897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828140381716451991326529 1371105286287338993494897)
                      ·
                        rfl

theorem cell23_2670218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_2670218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670218 prefixEnd_2670218 := by exact prefixLift 2670218
  have htrace : WordTrace (prefixWord ++ tailWord_2670218) baseStart_2670218 baseEnd_2670218 := by
    simpa [prefixWord, tailWord_2670218, baseEnd_2670218] using wordTrace_append hprefix tailTrace_2670218
  have hstable : (prefixWord ++ tailWord_2670218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670218).length < 2 ^ (prefixWord ++ tailWord_2670218).sum := by decide
  have hdescent : baseEnd_2670218 < baseStart_2670218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670262 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2670262 : Nat := 118140960795 + 2670262 * 2 ^ 59
def prefixEnd_2670262 : Nat := 4983230072969 + 3 ^ 40 * 2670262 * 2
def baseEnd_2670262 : Nat := 457042626478712273781565

theorem tailTrace_2670262 : CollatzResearch.WordTrace tailWord_2670262 prefixEnd_2670262 457042626478712273781565 := by
  unfold tailWord_2670262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087028515756518330447315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64928304168069528858104693 6087028515756518330447315)
  ·
    refine ⟨9130542773634777495670973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087028515756518330447315 9130542773634777495670973)
    ·
      refine ⟨3423953540113041560876615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9130542773634777495670973 3423953540113041560876615)
      ·
        refine ⟨5135930310169562341314923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3423953540113041560876615 5135930310169562341314923)
        ·
          refine ⟨7703895465254343511972385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135930310169562341314923 7703895465254343511972385)
          ·
            refine ⟨5777921598940757633979289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7703895465254343511972385 5777921598940757633979289)
            ·
              refine ⟨4333441199205568225484467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777921598940757633979289 4333441199205568225484467)
              ·
                refine ⟨6500161798808352338226701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333441199205568225484467 6500161798808352338226701)
                ·
                  refine ⟨2437560674553132126835013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6500161798808352338226701 2437560674553132126835013)
                  ·
                    refine ⟨457042626478712273781565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437560674553132126835013 457042626478712273781565)
                    ·
                      rfl

theorem cell23_2670262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2670262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670262 prefixEnd_2670262 := by exact prefixLift 2670262
  have htrace : WordTrace (prefixWord ++ tailWord_2670262) baseStart_2670262 baseEnd_2670262 := by
    simpa [prefixWord, tailWord_2670262, baseEnd_2670262] using wordTrace_append hprefix tailTrace_2670262
  have hstable : (prefixWord ++ tailWord_2670262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670262).length < 2 ^ (prefixWord ++ tailWord_2670262).sum := by decide
  have hdescent : baseEnd_2670262 < baseStart_2670262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670308 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_2670308 : Nat := 118140960795 + 2670308 * 2 ^ 59
def prefixEnd_2670308 : Nat := 4983230072969 + 3 ^ 40 * 2670308 * 2
def baseEnd_2670308 : Nat := 1371151499546243641369483

theorem tailTrace_2670308 : CollatzResearch.WordTrace tailWord_2670308 prefixEnd_2670308 1371151499546243641369483 := by
  unfold tailWord_2670308
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697067004968821571665789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64929422673291762095554385 48697067004968821571665789)
  ·
    refine ⟨18261400126863308089374671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48697067004968821571665789 18261400126863308089374671)
    ·
      refine ⟨27392100190294962134062007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18261400126863308089374671 27392100190294962134062007)
      ·
        refine ⟨41088150285442443201093011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27392100190294962134062007 41088150285442443201093011)
        ·
          refine ⟨61632225428163664801639517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41088150285442443201093011 61632225428163664801639517)
          ·
            refine ⟨23112084535561374300614819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61632225428163664801639517 23112084535561374300614819)
            ·
              refine ⟨34668126803342061450922229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23112084535561374300614819 34668126803342061450922229)
              ·
                refine ⟨3250136887813318261023959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34668126803342061450922229 3250136887813318261023959)
                ·
                  refine ⟨4875205331719977391535939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250136887813318261023959 4875205331719977391535939)
                  ·
                    refine ⟨7312807997579966087303909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4875205331719977391535939 7312807997579966087303909)
                    ·
                      refine ⟨1371151499546243641369483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7312807997579966087303909 1371151499546243641369483)
                      ·
                        rfl

theorem cell23_2670308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_2670308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670308 prefixEnd_2670308 := by exact prefixLift 2670308
  have htrace : WordTrace (prefixWord ++ tailWord_2670308) baseStart_2670308 baseEnd_2670308 := by
    simpa [prefixWord, tailWord_2670308, baseEnd_2670308] using wordTrace_append hprefix tailTrace_2670308
  have hstable : (prefixWord ++ tailWord_2670308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670308).length < 2 ^ (prefixWord ++ tailWord_2670308).sum := by decide
  have hdescent : baseEnd_2670308 < baseStart_2670308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670318 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2670318 : Nat := 118140960795 + 2670318 * 2 ^ 59
def prefixEnd_2670318 : Nat := 4983230072969 + 3 ^ 40 * 2670318 * 2
def baseEnd_2670318 : Nat := 457052211450929534081479

theorem tailTrace_2670318 : CollatzResearch.WordTrace tailWord_2670318 prefixEnd_2670318 457052211450929534081479 := by
  unfold tailWord_2670318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12174312342487676856399451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64929665826600943234130405 12174312342487676856399451)
  ·
    refine ⟨18261468513731515284599177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12174312342487676856399451 18261468513731515284599177)
    ·
      refine ⟨13696101385298636463449383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18261468513731515284599177 13696101385298636463449383)
      ·
        refine ⟨20544152077947954695174075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13696101385298636463449383 20544152077947954695174075)
        ·
          refine ⟨30816228116921932042761113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20544152077947954695174075 30816228116921932042761113)
          ·
            refine ⟨23112171087691449032070835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30816228116921932042761113 23112171087691449032070835)
            ·
              refine ⟨34668256631537173548106253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23112171087691449032070835 34668256631537173548106253)
              ·
                refine ⟨13000596236826440080539845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34668256631537173548106253 13000596236826440080539845)
                ·
                  refine ⟨2437611794404957515101221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13000596236826440080539845 2437611794404957515101221)
                  ·
                    refine ⟨457052211450929534081479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437611794404957515101221 457052211450929534081479)
                    ·
                      rfl

theorem cell23_2670318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2670318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670318 prefixEnd_2670318 := by exact prefixLift 2670318
  have htrace : WordTrace (prefixWord ++ tailWord_2670318) baseStart_2670318 baseEnd_2670318 := by
    simpa [prefixWord, tailWord_2670318, baseEnd_2670318] using wordTrace_append hprefix tailTrace_2670318
  have hstable : (prefixWord ++ tailWord_2670318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670318).length < 2 ^ (prefixWord ++ tailWord_2670318).sum := by decide
  have hdescent : baseEnd_2670318 < baseStart_2670318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670321 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2670321 : Nat := 118140960795 + 2670321 * 2 ^ 59
def prefixEnd_2670321 : Nat := 4983230072969 + 3 ^ 40 * 2670321 * 2
def baseEnd_2670321 : Nat := 1371158174794752090506923

theorem tailTrace_2670321 : CollatzResearch.WordTrace tailWord_2670321 prefixEnd_2670321 1371158174794752090506923 := by
  unfold tailWord_2670321
  simp only [CollatzResearch.WordTrace]
  refine ⟨97394608158890546363554817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64929738772593697575703211 97394608158890546363554817)
  ·
    refine ⟨73045956119167909772666113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97394608158890546363554817 73045956119167909772666113)
    ·
      refine ⟨54784467089375932329499585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73045956119167909772666113 54784467089375932329499585)
      ·
        refine ⟨41088350317031949247124689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54784467089375932329499585 41088350317031949247124689)
        ·
          refine ⟨30816262737773961935343517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41088350317031949247124689 30816262737773961935343517)
          ·
            refine ⟨11556098526665235725753819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30816262737773961935343517 11556098526665235725753819)
            ·
              refine ⟨17334147789997853588630729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556098526665235725753819 17334147789997853588630729)
              ·
                refine ⟨13000610842498390191473047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17334147789997853588630729 13000610842498390191473047)
                ·
                  refine ⟨19500916263747585287209571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13000610842498390191473047 19500916263747585287209571)
                  ·
                    refine ⟨29251374395621377930814357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19500916263747585287209571 29251374395621377930814357)
                    ·
                      refine ⟨1371158174794752090506923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29251374395621377930814357 1371158174794752090506923)
                      ·
                        rfl

theorem cell23_2670321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2670321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670321 prefixEnd_2670321 := by exact prefixLift 2670321
  have htrace : WordTrace (prefixWord ++ tailWord_2670321) baseStart_2670321 baseEnd_2670321 := by
    simpa [prefixWord, tailWord_2670321, baseEnd_2670321] using wordTrace_append hprefix tailTrace_2670321
  have hstable : (prefixWord ++ tailWord_2670321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670321).length < 2 ^ (prefixWord ++ tailWord_2670321).sum := by decide
  have hdescent : baseEnd_2670321 < baseStart_2670321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670335 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 2, 4]
def baseStart_2670335 : Nat := 118140960795 + 2670335 * 2 ^ 59
def prefixEnd_2670335 : Nat := 4983230072969 + 3 ^ 40 * 2670335 * 2
def baseEnd_2670335 : Nat := 457055121174638345243953

theorem tailTrace_2670335 : CollatzResearch.WordTrace tailWord_2670335 prefixEnd_2670335 457055121174638345243953 := by
  unfold tailWord_2670335
  simp only [CollatzResearch.WordTrace]
  refine ⟨97395118780839826754564459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64930079187226551169709639 97395118780839826754564459)
  ·
    refine ⟨146092678171259740131846689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97395118780839826754564459 146092678171259740131846689)
    ·
      refine ⟨109569508628444805098885017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146092678171259740131846689 109569508628444805098885017)
      ·
        refine ⟨82177131471333603824163763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109569508628444805098885017 82177131471333603824163763)
        ·
          refine ⟨123265697207000405736245645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82177131471333603824163763 123265697207000405736245645)
          ·
            refine ⟨46224636452625152151092117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123265697207000405736245645 46224636452625152151092117)
            ·
              refine ⟨2166779833716804007082443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46224636452625152151092117 2166779833716804007082443)
              ·
                refine ⟨3250169750575206010623665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166779833716804007082443 3250169750575206010623665)
                ·
                  refine ⟨2437627312931404507967749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250169750575206010623665 2437627312931404507967749)
                  ·
                    refine ⟨457055121174638345243953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437627312931404507967749 457055121174638345243953)
                    ·
                      rfl

theorem cell23_2670335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_2670335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670335 prefixEnd_2670335 := by exact prefixLift 2670335
  have htrace : WordTrace (prefixWord ++ tailWord_2670335) baseStart_2670335 baseEnd_2670335 := by
    simpa [prefixWord, tailWord_2670335, baseEnd_2670335] using wordTrace_append hprefix tailTrace_2670335
  have hstable : (prefixWord ++ tailWord_2670335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670335).length < 2 ^ (prefixWord ++ tailWord_2670335).sum := by decide
  have hdescent : baseEnd_2670335 < baseStart_2670335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670338 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2670338 : Nat := 118140960795 + 2670338 * 2 ^ 59
def prefixEnd_2670338 : Nat := 4983230072969 + 3 ^ 40 * 2670338 * 2
def baseEnd_2670338 : Nat := 1371166903965878523994345

theorem tailTrace_2670338 : CollatzResearch.WordTrace tailWord_2670338 prefixEnd_2670338 1371166903965878523994345 := by
  unfold tailWord_2670338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348807049957239566730917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64930152133219305511282445 24348807049957239566730917)
  ·
    refine ⟨4565401321866982418762047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24348807049957239566730917 4565401321866982418762047)
    ·
      refine ⟨6848101982800473628143071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565401321866982418762047 6848101982800473628143071)
      ·
        refine ⟨10272152974200710442214607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848101982800473628143071 10272152974200710442214607)
        ·
          refine ⟨15408229461301065663321911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272152974200710442214607 15408229461301065663321911)
          ·
            refine ⟨23112344191951598494982867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15408229461301065663321911 23112344191951598494982867)
            ·
              refine ⟨34668516287927397742474301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23112344191951598494982867 34668516287927397742474301)
              ·
                refine ⟨13000693607972774153427863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34668516287927397742474301 13000693607972774153427863)
                ·
                  refine ⟨19501040411959161230141795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13000693607972774153427863 19501040411959161230141795)
                  ·
                    refine ⟨29251560617938741845212693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19501040411959161230141795 29251560617938741845212693)
                    ·
                      refine ⟨1371166903965878523994345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29251560617938741845212693 1371166903965878523994345)
                      ·
                        rfl

theorem cell23_2670338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2670338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670338 prefixEnd_2670338 := by exact prefixLift 2670338
  have htrace : WordTrace (prefixWord ++ tailWord_2670338) baseStart_2670338 baseEnd_2670338 := by
    simpa [prefixWord, tailWord_2670338, baseEnd_2670338] using wordTrace_append hprefix tailTrace_2670338
  have hstable : (prefixWord ++ tailWord_2670338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670338).length < 2 ^ (prefixWord ++ tailWord_2670338).sum := by decide
  have hdescent : baseEnd_2670338 < baseStart_2670338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670356 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2670356 : Nat := 118140960795 + 2670356 * 2 ^ 59
def prefixEnd_2670356 : Nat := 4983230072969 + 3 ^ 40 * 2670356 * 2
def baseEnd_2670356 : Nat := 457058715539219817856421

theorem tailTrace_2670356 : CollatzResearch.WordTrace tailWord_2670356 prefixEnd_2670356 457058715539219817856421 := by
  unfold tailWord_2670356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48697942356881873670539461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64930589809175831560719281 48697942356881873670539461)
  ·
    refine ⟨9130864191915351313226149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48697942356881873670539461 9130864191915351313226149)
    ·
      refine ⟨1712037035984128371229903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9130864191915351313226149 1712037035984128371229903)
      ·
        refine ⟨2568055553976192556844855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712037035984128371229903 2568055553976192556844855)
        ·
          refine ⟨3852083330964288835267283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568055553976192556844855 3852083330964288835267283)
          ·
            refine ⟨5778124996446433252900925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852083330964288835267283 5778124996446433252900925)
            ·
              refine ⟨2166796873667412469837847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5778124996446433252900925 2166796873667412469837847)
              ·
                refine ⟨3250195310501118704756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166796873667412469837847 3250195310501118704756771)
                ·
                  refine ⟨4875292965751678057135157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250195310501118704756771 4875292965751678057135157)
                  ·
                    refine ⟨457058715539219817856421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4875292965751678057135157 457058715539219817856421)
                    ·
                      rfl

theorem cell23_2670356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2670356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670356 prefixEnd_2670356 := by exact prefixLift 2670356
  have htrace : WordTrace (prefixWord ++ tailWord_2670356) baseStart_2670356 baseEnd_2670356 := by
    simpa [prefixWord, tailWord_2670356, baseEnd_2670356] using wordTrace_append hprefix tailTrace_2670356
  have hstable : (prefixWord ++ tailWord_2670356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670356).length < 2 ^ (prefixWord ++ tailWord_2670356).sum := by decide
  have hdescent : baseEnd_2670356 < baseStart_2670356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670362 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_2670362 : Nat := 118140960795 + 2670362 * 2 ^ 59
def prefixEnd_2670362 : Nat := 4983230072969 + 3 ^ 40 * 2670362 * 2
def baseEnd_2670362 : Nat := 1371179227501586430094235

theorem tailTrace_2670362 : CollatzResearch.WordTrace tailWord_2670362 prefixEnd_2670362 1371179227501586430094235 := by
  unfold tailWord_2670362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349025887935502591449335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64930735701161340243864893 24349025887935502591449335)
  ·
    refine ⟨36523538831903253887174003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349025887935502591449335 36523538831903253887174003)
    ·
      refine ⟨54785308247854880830761005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523538831903253887174003 54785308247854880830761005)
      ·
        refine ⟨20544490592945580311535377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54785308247854880830761005 20544490592945580311535377)
        ·
          refine ⟨15408367944709185233651533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20544490592945580311535377 15408367944709185233651533)
          ·
            refine ⟨5778137979265944462619325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15408367944709185233651533 5778137979265944462619325)
            ·
              refine ⟨2166801742224729173482247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5778137979265944462619325 2166801742224729173482247)
              ·
                refine ⟨3250202613337093760223371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166801742224729173482247 3250202613337093760223371)
                ·
                  refine ⟨4875303920005640640335057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250202613337093760223371 4875303920005640640335057)
                  ·
                    refine ⟨3656477940004230480251293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4875303920005640640335057 3656477940004230480251293)
                    ·
                      refine ⟨1371179227501586430094235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3656477940004230480251293 1371179227501586430094235)
                      ·
                        rfl

theorem cell23_2670362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_2670362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670362 prefixEnd_2670362 := by exact prefixLift 2670362
  have htrace : WordTrace (prefixWord ++ tailWord_2670362) baseStart_2670362 baseEnd_2670362 := by
    simpa [prefixWord, tailWord_2670362, baseEnd_2670362] using wordTrace_append hprefix tailTrace_2670362
  have hstable : (prefixWord ++ tailWord_2670362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670362).length < 2 ^ (prefixWord ++ tailWord_2670362).sum := by decide
  have hdescent : baseEnd_2670362 < baseStart_2670362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670371 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2670371 : Nat := 118140960795 + 2670371 * 2 ^ 59
def prefixEnd_2670371 : Nat := 4983230072969 + 3 ^ 40 * 2670371 * 2
def baseEnd_2670371 : Nat := 1371183848827476894881693

theorem tailTrace_2670371 : CollatzResearch.WordTrace tailWord_2670371 prefixEnd_2670371 1371183848827476894881693 := by
  unfold tailWord_2670371
  simp only [CollatzResearch.WordTrace]
  refine ⟨97396431808709404902874967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64930954539139603268583311 97396431808709404902874967)
  ·
    refine ⟨146094647713064107354312451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97396431808709404902874967 146094647713064107354312451)
    ·
      refine ⟨219141971569596161031468677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146094647713064107354312451 219141971569596161031468677)
      ·
        refine ⟨41089119669299280193400377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219141971569596161031468677 41089119669299280193400377)
        ·
          refine ⟨30816839751974460145050283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41089119669299280193400377 30816839751974460145050283)
          ·
            refine ⟨46225259627961690217575425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30816839751974460145050283 46225259627961690217575425)
            ·
              refine ⟨34668944720971267663181569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46225259627961690217575425 34668944720971267663181569)
              ·
                refine ⟨26001708540728450747386177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34668944720971267663181569 26001708540728450747386177)
                ·
                  refine ⟨19501281405546338060539633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26001708540728450747386177 19501281405546338060539633)
                  ·
                    refine ⟨14625961054159753545404725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19501281405546338060539633 14625961054159753545404725)
                    ·
                      refine ⟨1371183848827476894881693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14625961054159753545404725 1371183848827476894881693)
                      ·
                        rfl

theorem cell23_2670371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2670371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670371 prefixEnd_2670371 := by exact prefixLift 2670371
  have htrace : WordTrace (prefixWord ++ tailWord_2670371) baseStart_2670371 baseEnd_2670371 := by
    simpa [prefixWord, tailWord_2670371, baseEnd_2670371] using wordTrace_append hprefix tailTrace_2670371
  have hstable : (prefixWord ++ tailWord_2670371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670371).length < 2 ^ (prefixWord ++ tailWord_2670371).sum := by decide
  have hdescent : baseEnd_2670371 < baseStart_2670371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670376 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2670376 : Nat := 118140960795 + 2670376 * 2 ^ 59
def prefixEnd_2670376 : Nat := 4983230072969 + 3 ^ 40 * 2670376 * 2
def baseEnd_2670376 : Nat := 1371186416230749375319171

theorem tailTrace_2670376 : CollatzResearch.WordTrace tailWord_2670376 prefixEnd_2670376 1371186416230749375319171 := by
  unfold tailWord_2670376
  simp only [CollatzResearch.WordTrace]
  refine ⟨48698307086845645378403491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64931076115794193837871321 48698307086845645378403491)
  ·
    refine ⟨73047460630268468067605237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48698307086845645378403491 73047460630268468067605237)
    ·
      refine ⟨6848199434087668881337991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73047460630268468067605237 6848199434087668881337991)
      ·
        refine ⟨10272299151131503322006987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848199434087668881337991 10272299151131503322006987)
        ·
          refine ⟨15408448726697254983010481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272299151131503322006987 15408448726697254983010481)
          ·
            refine ⟨11556336545022941237257861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408448726697254983010481 11556336545022941237257861)
            ·
              refine ⟨2166813102191801481985849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11556336545022941237257861 2166813102191801481985849)
              ·
                refine ⟨1625109826643851111489387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166813102191801481985849 1625109826643851111489387)
                ·
                  refine ⟨2437664739965776667234081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625109826643851111489387 2437664739965776667234081)
                  ·
                    refine ⟨1828248554974332500425561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437664739965776667234081 1828248554974332500425561)
                    ·
                      refine ⟨1371186416230749375319171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828248554974332500425561 1371186416230749375319171)
                      ·
                        rfl

theorem cell23_2670376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2670376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670376 prefixEnd_2670376 := by exact prefixLift 2670376
  have htrace : WordTrace (prefixWord ++ tailWord_2670376) baseStart_2670376 baseEnd_2670376 := by
    simpa [prefixWord, tailWord_2670376, baseEnd_2670376] using wordTrace_append hprefix tailTrace_2670376
  have hstable : (prefixWord ++ tailWord_2670376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670376).length < 2 ^ (prefixWord ++ tailWord_2670376).sum := by decide
  have hdescent : baseEnd_2670376 < baseStart_2670376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670382 : List Nat := [4, 1, 3, 2, 3, 1, 1, 8]
def baseStart_2670382 : Nat := 118140960795 + 2670382 * 2 ^ 59
def prefixEnd_2670382 : Nat := 4983230072969 + 3 ^ 40 * 2670382 * 2
def baseEnd_2670382 : Nat := 50784796189432457475709

theorem tailTrace_2670382 : CollatzResearch.WordTrace tailWord_2670382 prefixEnd_2670382 50784796189432457475709 := by
  unfold tailWord_2670382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12174604126458694222690675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64931222007779702521016933 12174604126458694222690675)
  ·
    refine ⟨18261906189688041334036013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12174604126458694222690675 18261906189688041334036013)
    ·
      refine ⟨6848214821133015500263505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18261906189688041334036013 6848214821133015500263505)
      ·
        refine ⟨5136161115849761625197629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6848214821133015500263505 5136161115849761625197629)
        ·
          refine ⟨1926060418443660609449111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5136161115849761625197629 1926060418443660609449111)
          ·
            refine ⟨2889090627665490914173667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926060418443660609449111 2889090627665490914173667)
            ·
              refine ⟨4333635941498236371260501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889090627665490914173667 4333635941498236371260501)
              ·
                refine ⟨50784796189432457475709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4333635941498236371260501 50784796189432457475709)
                ·
                  rfl

theorem cell23_2670382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_2670382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670382 prefixEnd_2670382 := by exact prefixLift 2670382
  have htrace : WordTrace (prefixWord ++ tailWord_2670382) baseStart_2670382 baseEnd_2670382 := by
    simpa [prefixWord, tailWord_2670382, baseEnd_2670382] using wordTrace_append hprefix tailTrace_2670382
  have hstable : (prefixWord ++ tailWord_2670382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670382).length < 2 ^ (prefixWord ++ tailWord_2670382).sum := by decide
  have hdescent : baseEnd_2670382 < baseStart_2670382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670385 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_2670385 : Nat := 118140960795 + 2670385 * 2 ^ 59
def prefixEnd_2670385 : Nat := 4983230072969 + 3 ^ 40 * 2670385 * 2
def baseEnd_2670385 : Nat := 1371191037556639840106629

theorem tailTrace_2670385 : CollatzResearch.WordTrace tailWord_2670385 prefixEnd_2670385 1371191037556639840106629 := by
  unfold tailWord_2670385
  simp only [CollatzResearch.WordTrace]
  refine ⟨97396942430658685293884609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64931294953772456862589739 97396942430658685293884609)
  ·
    refine ⟨73047706822994013970413457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97396942430658685293884609 73047706822994013970413457)
    ·
      refine ⟨54785780117245510477810093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73047706822994013970413457 54785780117245510477810093)
      ·
        refine ⟨20544667543967066429178785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54785780117245510477810093 20544667543967066429178785)
        ·
          refine ⟨15408500657975299821884089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20544667543967066429178785 15408500657975299821884089)
          ·
            refine ⟨11556375493481474866413067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408500657975299821884089 11556375493481474866413067)
            ·
              refine ⟨17334563240222212299619601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556375493481474866413067 17334563240222212299619601)
              ·
                refine ⟨13000922430166659224714701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17334563240222212299619601 13000922430166659224714701)
                ·
                  refine ⟨4875345911312497209268013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13000922430166659224714701 4875345911312497209268013)
                  ·
                    refine ⟨1828254716742186453475505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4875345911312497209268013 1828254716742186453475505)
                    ·
                      refine ⟨1371191037556639840106629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828254716742186453475505 1371191037556639840106629)
                      ·
                        rfl

theorem cell23_2670385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_2670385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670385 prefixEnd_2670385 := by exact prefixLift 2670385
  have htrace : WordTrace (prefixWord ++ tailWord_2670385) baseStart_2670385 baseEnd_2670385 := by
    simpa [prefixWord, tailWord_2670385, baseEnd_2670385] using wordTrace_append hprefix tailTrace_2670385
  have hstable : (prefixWord ++ tailWord_2670385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670385).length < 2 ^ (prefixWord ++ tailWord_2670385).sum := by decide
  have hdescent : baseEnd_2670385 < baseStart_2670385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670432 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2]
def baseStart_2670432 : Nat := 118140960795 + 2670432 * 2 ^ 59
def prefixEnd_2670432 : Nat := 4983230072969 + 3 ^ 40 * 2670432 * 2
def baseEnd_2670432 : Nat := 1371215171147401156218913

theorem tailTrace_2670432 : CollatzResearch.WordTrace tailWord_2670432 prefixEnd_2670432 1371215171147401156218913 := by
  unfold tailWord_2670432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48699328330744206160422775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64932437774325608213897033 48699328330744206160422775)
  ·
    refine ⟨73048992496116309240634163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48699328330744206160422775 73048992496116309240634163)
    ·
      refine ⟨109573488744174463860951245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73048992496116309240634163 109573488744174463860951245)
      ·
        refine ⟨41090058279065423947856717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109573488744174463860951245 41090058279065423947856717)
        ·
          refine ⟨15408771854649533980446269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41090058279065423947856717 15408771854649533980446269)
          ·
            refine ⟨5778289445493575242667351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15408771854649533980446269 5778289445493575242667351)
            ·
              refine ⟨8667434168240362864001027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778289445493575242667351 8667434168240362864001027)
              ·
                refine ⟨13001151252360544296001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667434168240362864001027 13001151252360544296001541)
                ·
                  refine ⟨2437715859817602055500289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13001151252360544296001541 2437715859817602055500289)
                  ·
                    refine ⟨1828286894863201541625217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437715859817602055500289 1828286894863201541625217)
                    ·
                      refine ⟨1371215171147401156218913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828286894863201541625217 1371215171147401156218913)
                      ·
                        rfl

theorem cell23_2670432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_2670432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670432 prefixEnd_2670432 := by exact prefixLift 2670432
  have htrace : WordTrace (prefixWord ++ tailWord_2670432) baseStart_2670432 baseEnd_2670432 := by
    simpa [prefixWord, tailWord_2670432, baseEnd_2670432] using wordTrace_append hprefix tailTrace_2670432
  have hstable : (prefixWord ++ tailWord_2670432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670432).length < 2 ^ (prefixWord ++ tailWord_2670432).sum := by decide
  have hdescent : baseEnd_2670432 < baseStart_2670432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670449 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_2670449 : Nat := 118140960795 + 2670449 * 2 ^ 59
def prefixEnd_2670449 : Nat := 4983230072969 + 3 ^ 40 * 2670449 * 2
def baseEnd_2670449 : Nat := 1371223900318527589706335

theorem tailTrace_2670449 : CollatzResearch.WordTrace tailWord_2670449 prefixEnd_2670449 1371223900318527589706335 := by
  unfold tailWord_2670449
  simp only [CollatzResearch.WordTrace]
  refine ⟨97399276702426824224214401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64932851134951216149476267 97399276702426824224214401)
  ·
    refine ⟨73049457526820118168160801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97399276702426824224214401 73049457526820118168160801)
    ·
      refine ⟨54787093145115088626120601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73049457526820118168160801 54787093145115088626120601)
      ·
        refine ⟨41090319858836316469590451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54787093145115088626120601 41090319858836316469590451)
        ·
          refine ⟨61635479788254474704385677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41090319858836316469590451 61635479788254474704385677)
          ·
            refine ⟨23113304920595428014144629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61635479788254474704385677 23113304920595428014144629)
            ·
              refine ⟨2166872336305821376326059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23113304920595428014144629 2166872336305821376326059)
              ·
                refine ⟨3250308504458732064489089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166872336305821376326059 3250308504458732064489089)
                ·
                  refine ⟨2437731378344049048366817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250308504458732064489089 2437731378344049048366817)
                  ·
                    refine ⟨1828298533758036786275113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437731378344049048366817 1828298533758036786275113)
                    ·
                      refine ⟨1371223900318527589706335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828298533758036786275113 1371223900318527589706335)
                      ·
                        rfl

theorem cell23_2670449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_2670449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670449 prefixEnd_2670449 := by exact prefixLift 2670449
  have htrace : WordTrace (prefixWord ++ tailWord_2670449) baseStart_2670449 baseEnd_2670449 := by
    simpa [prefixWord, tailWord_2670449, baseEnd_2670449] using wordTrace_append hprefix tailTrace_2670449
  have hstable : (prefixWord ++ tailWord_2670449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670449).length < 2 ^ (prefixWord ++ tailWord_2670449).sum := by decide
  have hdescent : baseEnd_2670449 < baseStart_2670449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670468 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2670468 : Nat := 118140960795 + 2670468 * 2 ^ 59
def prefixEnd_2670468 : Nat := 4983230072969 + 3 ^ 40 * 2670468 * 2
def baseEnd_2670468 : Nat := 457077885483654338456249

theorem tailTrace_2670468 : CollatzResearch.WordTrace tailWord_2670468 prefixEnd_2670468 457077885483654338456249 := by
  unfold tailWord_2670468
  simp only [CollatzResearch.WordTrace]
  refine ⟨48699984844678995234578029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64933313126238660312770705 48699984844678995234578029)
  ·
    refine ⟨18262494316754623212966761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48699984844678995234578029 18262494316754623212966761)
    ·
      refine ⟨13696870737565967409725071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18262494316754623212966761 13696870737565967409725071)
      ·
        refine ⟨20545306106348951114587607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13696870737565967409725071 20545306106348951114587607)
        ·
          refine ⟨30817959159523426671881411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20545306106348951114587607 30817959159523426671881411)
          ·
            refine ⟨46226938739285140007822117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30817959159523426671881411 46226938739285140007822117)
            ·
              refine ⟨8667551013615963751466647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46226938739285140007822117 8667551013615963751466647)
              ·
                refine ⟨13001326520423945627199971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667551013615963751466647 13001326520423945627199971)
                ·
                  refine ⟨19501989780635918440799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13001326520423945627199971 19501989780635918440799957)
                  ·
                    refine ⟨457077885483654338456249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19501989780635918440799957 457077885483654338456249)
                    ·
                      rfl

theorem cell23_2670468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2670468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670468 prefixEnd_2670468 := by exact prefixLift 2670468
  have htrace : WordTrace (prefixWord ++ tailWord_2670468) baseStart_2670468 baseEnd_2670468 := by
    simpa [prefixWord, tailWord_2670468, baseEnd_2670468] using wordTrace_append hprefix tailTrace_2670468
  have hstable : (prefixWord ++ tailWord_2670468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670468).length < 2 ^ (prefixWord ++ tailWord_2670468).sum := by decide
  have hdescent : baseEnd_2670468 < baseStart_2670468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670495 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2670495 : Nat := 118140960795 + 2670495 * 2 ^ 59
def prefixEnd_2670495 : Nat := 4983230072969 + 3 ^ 40 * 2670495 * 2
def baseEnd_2670495 : Nat := 1371247520428634409731123

theorem tailTrace_2670495 : CollatzResearch.WordTrace tailWord_2670495 prefixEnd_2670495 1371247520428634409731123 := by
  unfold tailWord_2670495
  simp only [CollatzResearch.WordTrace]
  refine ⟨97400954460260174080388939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64933969640173449386925959 97400954460260174080388939)
  ·
    refine ⟨146101431690390261120583409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97400954460260174080388939 146101431690390261120583409)
    ·
      refine ⟨109576073767792695840437557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146101431690390261120583409 109576073767792695840437557)
      ·
        refine ⟨10272756915730565235041021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109576073767792695840437557 10272756915730565235041021)
        ·
          refine ⟨3852283843398961963140383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10272756915730565235041021 3852283843398961963140383)
          ·
            refine ⟨5778425765098442944710575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852283843398961963140383 5778425765098442944710575)
            ·
              refine ⟨8667638647647664417065863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778425765098442944710575 8667638647647664417065863)
              ·
                refine ⟨13001457971471496625598795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667638647647664417065863 13001457971471496625598795)
                ·
                  refine ⟨19502186957207244938398193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13001457971471496625598795 19502186957207244938398193)
                  ·
                    refine ⟨14626640217905433703798645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19502186957207244938398193 14626640217905433703798645)
                    ·
                      refine ⟨1371247520428634409731123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14626640217905433703798645 1371247520428634409731123)
                      ·
                        rfl

theorem cell23_2670495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2670495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670495 prefixEnd_2670495 := by exact prefixLift 2670495
  have htrace : WordTrace (prefixWord ++ tailWord_2670495) baseStart_2670495 baseEnd_2670495 := by
    simpa [prefixWord, tailWord_2670495, baseEnd_2670495] using wordTrace_append hprefix tailTrace_2670495
  have hstable : (prefixWord ++ tailWord_2670495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670495).length < 2 ^ (prefixWord ++ tailWord_2670495).sum := by decide
  have hdescent : baseEnd_2670495 < baseStart_2670495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670549 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2670549 : Nat := 118140960795 + 2670549 * 2 ^ 59
def prefixEnd_2670549 : Nat := 4983230072969 + 3 ^ 40 * 2670549 * 2
def baseEnd_2670549 : Nat := 457091749461325732818625

theorem tailTrace_2670549 : CollatzResearch.WordTrace tailWord_2670549 prefixEnd_2670549 457091749461325732818625 := by
  unfold tailWord_2670549
  simp only [CollatzResearch.WordTrace]
  refine ⟨97402924002064541302854701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64935282668043027535236467 97402924002064541302854701)
  ·
    refine ⟨36526096500774202988570513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97402924002064541302854701 36526096500774202988570513)
    ·
      refine ⟨27394572375580652241427885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36526096500774202988570513 27394572375580652241427885)
      ·
        refine ⟨10272964640842744590535457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27394572375580652241427885 10272964640842744590535457)
        ·
          refine ⟨7704723480632058442901593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10272964640842744590535457 7704723480632058442901593)
          ·
            refine ⟨5778542610474043832176195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704723480632058442901593 5778542610474043832176195)
            ·
              refine ⟨8667813915711065748264293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778542610474043832176195 8667813915711065748264293)
              ·
                refine ⟨1625215109195824827799555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8667813915711065748264293 1625215109195824827799555)
                ·
                  refine ⟨2437822663793737241699333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625215109195824827799555 2437822663793737241699333)
                  ·
                    refine ⟨457091749461325732818625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437822663793737241699333 457091749461325732818625)
                    ·
                      rfl

theorem cell23_2670549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2670549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670549 prefixEnd_2670549 := by exact prefixLift 2670549
  have htrace : WordTrace (prefixWord ++ tailWord_2670549) baseStart_2670549 baseEnd_2670549 := by
    simpa [prefixWord, tailWord_2670549, baseEnd_2670549] using wordTrace_append hprefix tailTrace_2670549
  have hstable : (prefixWord ++ tailWord_2670549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670549).length < 2 ^ (prefixWord ++ tailWord_2670549).sum := by decide
  have hdescent : baseEnd_2670549 < baseStart_2670549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670568 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2670568 : Nat := 118140960795 + 2670568 * 2 ^ 59
def prefixEnd_2670568 : Nat := 4983230072969 + 3 ^ 40 * 2670568 * 2
def baseEnd_2670568 : Nat := 1371285004516412624118287

theorem tailTrace_2670568 : CollatzResearch.WordTrace tailWord_2670568 prefixEnd_2670568 1371285004516412624118287 := by
  unfold tailWord_2670568
  simp only [CollatzResearch.WordTrace]
  refine ⟨48701808494497853773898179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64935744659330471698530905 48701808494497853773898179)
  ·
    refine ⟨73052712741746780660847269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48701808494497853773898179 73052712741746780660847269)
    ·
      refine ⟨13697383639077521373908863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73052712741746780660847269 13697383639077521373908863)
      ·
        refine ⟨20546075458616282060863295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13697383639077521373908863 20546075458616282060863295)
        ·
          refine ⟨30819113187924423091294943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20546075458616282060863295 30819113187924423091294943)
          ·
            refine ⟨46228669781886634636942415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30819113187924423091294943 46228669781886634636942415)
            ·
              refine ⟨69343004672829951955413623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46228669781886634636942415 69343004672829951955413623)
              ·
                refine ⟨104014507009244927933120435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69343004672829951955413623 104014507009244927933120435)
                ·
                  refine ⟨156021760513867391899680653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104014507009244927933120435 156021760513867391899680653)
                  ·
                    refine ⟨58508160192700271962380245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156021760513867391899680653 58508160192700271962380245)
                    ·
                      refine ⟨1371285004516412624118287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58508160192700271962380245 1371285004516412624118287)
                      ·
                        rfl

theorem cell23_2670568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2670568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670568 prefixEnd_2670568 := by exact prefixLift 2670568
  have htrace : WordTrace (prefixWord ++ tailWord_2670568) baseStart_2670568 baseEnd_2670568 := by
    simpa [prefixWord, tailWord_2670568, baseEnd_2670568] using wordTrace_append hprefix tailTrace_2670568
  have hstable : (prefixWord ++ tailWord_2670568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670568).length < 2 ^ (prefixWord ++ tailWord_2670568).sum := by decide
  have hdescent : baseEnd_2670568 < baseStart_2670568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670575 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 1, 5]
def baseStart_2670575 : Nat := 118140960795 + 2670575 * 2 ^ 59
def prefixEnd_2670575 : Nat := 4983230072969 + 3 ^ 40 * 2670575 * 2
def baseEnd_2670575 : Nat := 457096199626998032243585

theorem tailTrace_2670575 : CollatzResearch.WordTrace tailWord_2670575 prefixEnd_2670575 457096199626998032243585 := by
  unfold tailWord_2670575
  simp only [CollatzResearch.WordTrace]
  refine ⟨97403872299970347743301179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64935914866646898495534119 97403872299970347743301179)
  ·
    refine ⟨146105808449955521614951769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97403872299970347743301179 146105808449955521614951769)
    ·
      refine ⟨109579356337466641211213827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146105808449955521614951769 109579356337466641211213827)
      ·
        refine ⟨164369034506199961816820741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109579356337466641211213827 164369034506199961816820741)
        ·
          refine ⟨30819193969912492840653889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164369034506199961816820741 30819193969912492840653889)
          ·
            refine ⟨23114395477434369630490417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30819193969912492840653889 23114395477434369630490417)
            ·
              refine ⟨17335796608075777222867813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23114395477434369630490417 17335796608075777222867813)
              ·
                refine ⟨3250461864014208229287715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17335796608075777222867813 3250461864014208229287715)
                ·
                  refine ⟨4875692796021312343931573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3250461864014208229287715 4875692796021312343931573)
                  ·
                    refine ⟨457096199626998032243585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4875692796021312343931573 457096199626998032243585)
                    ·
                      rfl

theorem cell23_2670575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_2670575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670575 prefixEnd_2670575 := by exact prefixLift 2670575
  have htrace : WordTrace (prefixWord ++ tailWord_2670575) baseStart_2670575 baseEnd_2670575 := by
    simpa [prefixWord, tailWord_2670575, baseEnd_2670575] using wordTrace_append hprefix tailTrace_2670575
  have hstable : (prefixWord ++ tailWord_2670575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670575).length < 2 ^ (prefixWord ++ tailWord_2670575).sum := by decide
  have hdescent : baseEnd_2670575 < baseStart_2670575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670589 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_2670589 : Nat := 118140960795 + 2670589 * 2 ^ 59
def prefixEnd_2670589 : Nat := 4983230072969 + 3 ^ 40 * 2670589 * 2
def baseEnd_2670589 : Nat := 1371295787610157041955691

theorem tailTrace_2670589 : CollatzResearch.WordTrace tailWord_2670589 prefixEnd_2670589 1371295787610157041955691 := by
  unfold tailWord_2670589
  simp only [CollatzResearch.WordTrace]
  refine ⟨97404382921919628134310821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64936255281279752089540547 97404382921919628134310821)
  ·
    refine ⟨18263321797859930275183279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97404382921919628134310821 18263321797859930275183279)
    ·
      refine ⟨27394982696789895412774919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18263321797859930275183279 27394982696789895412774919)
      ·
        refine ⟨41092474045184843119162379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27394982696789895412774919 41092474045184843119162379)
        ·
          refine ⟨61638711067777264678743569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41092474045184843119162379 61638711067777264678743569)
          ·
            refine ⟨46229033300832948509057677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61638711067777264678743569 46229033300832948509057677)
            ·
              refine ⟨17335887487812355690896629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46229033300832948509057677 17335887487812355690896629)
              ·
                refine ⟨1625239451982408346021559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17335887487812355690896629 1625239451982408346021559)
                ·
                  refine ⟨2437859177973612519032339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625239451982408346021559 2437859177973612519032339)
                  ·
                    refine ⟨3656788766960418778548509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2437859177973612519032339 3656788766960418778548509)
                    ·
                      refine ⟨1371295787610157041955691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3656788766960418778548509 1371295787610157041955691)
                      ·
                        rfl

theorem cell23_2670589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_2670589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670589 prefixEnd_2670589 := by exact prefixLift 2670589
  have htrace : WordTrace (prefixWord ++ tailWord_2670589) baseStart_2670589 baseEnd_2670589 := by
    simpa [prefixWord, tailWord_2670589, baseEnd_2670589] using wordTrace_append hprefix tailTrace_2670589
  have hstable : (prefixWord ++ tailWord_2670589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670589).length < 2 ^ (prefixWord ++ tailWord_2670589).sum := by decide
  have hdescent : baseEnd_2670589 < baseStart_2670589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670595 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 8, 2]
def baseStart_2670595 : Nat := 118140960795 + 2670595 * 2 ^ 59
def prefixEnd_2670595 : Nat := 4983230072969 + 3 ^ 40 * 2670595 * 2
def baseEnd_2670595 : Nat := 1371298868494084018480663

theorem tailTrace_2670595 : CollatzResearch.WordTrace tailWord_2670595 prefixEnd_2670595 1371298868494084018480663 := by
  unfold tailWord_2670595
  simp only [CollatzResearch.WordTrace]
  refine ⟨97404601759897891159029239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64936401173265260772686159 97404601759897891159029239)
  ·
    refine ⟨146106902639846836738543859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97404601759897891159029239 146106902639846836738543859)
    ·
      refine ⟨219160353959770255107815789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146106902639846836738543859 219160353959770255107815789)
      ·
        refine ⟨82185132734913845665430921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219160353959770255107815789 82185132734913845665430921)
        ·
          refine ⟨61638849551185384249073191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82185132734913845665430921 61638849551185384249073191)
          ·
            refine ⟨92458274326778076373609787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61638849551185384249073191 92458274326778076373609787)
            ·
              refine ⟨138687411490167114560414681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92458274326778076373609787 138687411490167114560414681)
              ·
                refine ⟨104015558617625335920311011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138687411490167114560414681 104015558617625335920311011)
                ·
                  refine ⟨156023337926438003880466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104015558617625335920311011 156023337926438003880466517)
                  ·
                    refine ⟨1828398491325445357974217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 156023337926438003880466517 1828398491325445357974217)
                    ·
                      refine ⟨1371298868494084018480663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828398491325445357974217 1371298868494084018480663)
                      ·
                        rfl

theorem cell23_2670595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_2670595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670595 prefixEnd_2670595 := by exact prefixLift 2670595
  have htrace : WordTrace (prefixWord ++ tailWord_2670595) baseStart_2670595 baseEnd_2670595 := by
    simpa [prefixWord, tailWord_2670595, baseEnd_2670595] using wordTrace_append hprefix tailTrace_2670595
  have hstable : (prefixWord ++ tailWord_2670595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670595).length < 2 ^ (prefixWord ++ tailWord_2670595).sum := by decide
  have hdescent : baseEnd_2670595 < baseStart_2670595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670596 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2670596 : Nat := 118140960795 + 2670596 * 2 ^ 59
def prefixEnd_2670596 : Nat := 4983230072969 + 3 ^ 40 * 2670596 * 2
def baseEnd_2670596 : Nat := 152366597997193168285351

theorem tailTrace_2670596 : CollatzResearch.WordTrace tailWord_2670596 prefixEnd_2670596 152366597997193168285351 := by
  unfold tailWord_2670596
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702319116447134164907821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64936425488596178886543761 48702319116447134164907821)
  ·
    refine ⟨18263369668667675311840433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48702319116447134164907821 18263369668667675311840433)
    ·
      refine ⟨13697527251500756483880325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18263369668667675311840433 13697527251500756483880325)
      ·
        refine ⟨2568286359656391840727561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13697527251500756483880325 2568286359656391840727561)
        ·
          refine ⟨1926214769742293880545671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568286359656391840727561 1926214769742293880545671)
          ·
            refine ⟨2889322154613440820818507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926214769742293880545671 2889322154613440820818507)
            ·
              refine ⟨4333983231920161231227761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889322154613440820818507 4333983231920161231227761)
              ·
                refine ⟨3250487423940120923420821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333983231920161231227761 3250487423940120923420821)
                ·
                  refine ⟨152366597997193168285351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3250487423940120923420821 152366597997193168285351)
                  ·
                    rfl

theorem cell23_2670596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2670596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670596 prefixEnd_2670596 := by exact prefixLift 2670596
  have htrace : WordTrace (prefixWord ++ tailWord_2670596) baseStart_2670596 baseEnd_2670596 := by
    simpa [prefixWord, tailWord_2670596, baseEnd_2670596] using wordTrace_append hprefix tailTrace_2670596
  have hstable : (prefixWord ++ tailWord_2670596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670596).length < 2 ^ (prefixWord ++ tailWord_2670596).sum := by decide
  have hdescent : baseEnd_2670596 < baseStart_2670596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670608 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_2670608 : Nat := 118140960795 + 2670608 * 2 ^ 59
def prefixEnd_2670608 : Nat := 4983230072969 + 3 ^ 40 * 2670608 * 2
def baseEnd_2670608 : Nat := 1371305543742592467618103

theorem tailTrace_2670608 : CollatzResearch.WordTrace tailWord_2670608 prefixEnd_2670608 1371305543742592467618103 := by
  unfold tailWord_2670608
  simp only [CollatzResearch.WordTrace]
  refine ⟨48702537954425397189626239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64936717272567196252834985 48702537954425397189626239)
  ·
    refine ⟨73053806931638095784439359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48702537954425397189626239 73053806931638095784439359)
    ·
      refine ⟨109580710397457143676659039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73053806931638095784439359 109580710397457143676659039)
      ·
        refine ⟨164371065596185715514988559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109580710397457143676659039 164371065596185715514988559)
        ·
          refine ⟨246556598394278573272482839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164371065596185715514988559 246556598394278573272482839)
          ·
            refine ⟨369834897591417859908724259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246556598394278573272482839 369834897591417859908724259)
            ·
              refine ⟨554752346387126789863086389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369834897591417859908724259 554752346387126789863086389)
              ·
                refine ⟨52008032473793136549664349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554752346387126789863086389 52008032473793136549664349)
                ·
                  refine ⟨19503012177672426206124131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52008032473793136549664349 19503012177672426206124131)
                  ·
                    refine ⟨29254518266508639309186197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19503012177672426206124131 29254518266508639309186197)
                    ·
                      refine ⟨1371305543742592467618103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29254518266508639309186197 1371305543742592467618103)
                      ·
                        rfl

theorem cell23_2670608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_2670608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670608 prefixEnd_2670608 := by exact prefixLift 2670608
  have htrace : WordTrace (prefixWord ++ tailWord_2670608) baseStart_2670608 baseEnd_2670608 := by
    simpa [prefixWord, tailWord_2670608, baseEnd_2670608] using wordTrace_append hprefix tailTrace_2670608
  have hstable : (prefixWord ++ tailWord_2670608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670608).length < 2 ^ (prefixWord ++ tailWord_2670608).sum := by decide
  have hdescent : baseEnd_2670608 < baseStart_2670608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670629 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_2670629 : Nat := 118140960795 + 2670629 * 2 ^ 59
def prefixEnd_2670629 : Nat := 4983230072969 + 3 ^ 40 * 2670629 * 2
def baseEnd_2670629 : Nat := 1371316326836336885455507

theorem tailTrace_2670629 : CollatzResearch.WordTrace tailWord_2670629 prefixEnd_2670629 1371316326836336885455507 := by
  unfold tailWord_2670629
  simp only [CollatzResearch.WordTrace]
  refine ⟨97405841841774714965766941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64937227894516476643844627 97405841841774714965766941)
  ·
    refine ⟨36527190690665518112162603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97405841841774714965766941 36527190690665518112162603)
    ·
      refine ⟨54790786035998277168243905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36527190690665518112162603 54790786035998277168243905)
      ·
        refine ⟨41093089526998707876182929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54790786035998277168243905 41093089526998707876182929)
        ·
          refine ⟨30819817145249030907137197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41093089526998707876182929 30819817145249030907137197)
          ·
            refine ⟨11557431429468386590176449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30819817145249030907137197 11557431429468386590176449)
            ·
              refine ⟨8668073572101289942632337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11557431429468386590176449 8668073572101289942632337)
              ·
                refine ⟨6501055179075967456974253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8668073572101289942632337 6501055179075967456974253)
                ·
                  refine ⟨2437895692153487796365345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6501055179075967456974253 2437895692153487796365345)
                  ·
                    refine ⟨1828421769115115847274009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437895692153487796365345 1828421769115115847274009)
                    ·
                      refine ⟨1371316326836336885455507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828421769115115847274009 1371316326836336885455507)
                      ·
                        rfl

theorem cell23_2670629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_2670629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670629 prefixEnd_2670629 := by exact prefixLift 2670629
  have htrace : WordTrace (prefixWord ++ tailWord_2670629) baseStart_2670629 baseEnd_2670629 := by
    simpa [prefixWord, tailWord_2670629, baseEnd_2670629] using wordTrace_append hprefix tailTrace_2670629
  have hstable : (prefixWord ++ tailWord_2670629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670629).length < 2 ^ (prefixWord ++ tailWord_2670629).sum := by decide
  have hdescent : baseEnd_2670629 < baseStart_2670629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670663 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_2670663 : Nat := 118140960795 + 2670663 * 2 ^ 59
def prefixEnd_2670663 : Nat := 4983230072969 + 3 ^ 40 * 2670663 * 2
def baseEnd_2670663 : Nat := 1371333785178589752430351

theorem tailTrace_2670663 : CollatzResearch.WordTrace tailWord_2670663 prefixEnd_2670663 1371333785178589752430351 := by
  unfold tailWord_2670663
  simp only [CollatzResearch.WordTrace]
  refine ⟨97407081923651538772504643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64938054615767692515003095 97407081923651538772504643)
  ·
    refine ⟨146110622885477308158756965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97407081923651538772504643 146110622885477308158756965)
    ·
      refine ⟨27395741791026995279766931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146110622885477308158756965 27395741791026995279766931)
      ·
        refine ⟨41093612686540492919650397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27395741791026995279766931 41093612686540492919650397)
        ·
          refine ⟨15410104757452684844868899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41093612686540492919650397 15410104757452684844868899)
          ·
            refine ⟨23115157136179027267303349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15410104757452684844868899 23115157136179027267303349)
            ·
              refine ⟨2167045981516783806309689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23115157136179027267303349 2167045981516783806309689)
              ·
                refine ⟨1625284486137587854732267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167045981516783806309689 1625284486137587854732267)
                ·
                  refine ⟨2437926729206381782098401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625284486137587854732267 2437926729206381782098401)
                  ·
                    refine ⟨1828445046904786336573801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437926729206381782098401 1828445046904786336573801)
                    ·
                      refine ⟨1371333785178589752430351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828445046904786336573801 1371333785178589752430351)
                      ·
                        rfl

theorem cell23_2670663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_2670663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670663 prefixEnd_2670663 := by exact prefixLift 2670663
  have htrace : WordTrace (prefixWord ++ tailWord_2670663) baseStart_2670663 baseEnd_2670663 := by
    simpa [prefixWord, tailWord_2670663, baseEnd_2670663] using wordTrace_append hprefix tailTrace_2670663
  have hstable : (prefixWord ++ tailWord_2670663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670663).length < 2 ^ (prefixWord ++ tailWord_2670663).sum := by decide
  have hdescent : baseEnd_2670663 < baseStart_2670663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670705 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2670705 : Nat := 118140960795 + 2670705 * 2 ^ 59
def prefixEnd_2670705 : Nat := 4983230072969 + 3 ^ 40 * 2670705 * 2
def baseEnd_2670705 : Nat := 1371355351366078588105157

theorem tailTrace_2670705 : CollatzResearch.WordTrace tailWord_2670705 prefixEnd_2670705 1371355351366078588105157 := by
  unfold tailWord_2670705
  simp only [CollatzResearch.WordTrace]
  refine ⟨97408613789499379945533569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64939075859666253297022379 97408613789499379945533569)
  ·
    refine ⟨73056460342124534959150177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97408613789499379945533569 73056460342124534959150177)
    ·
      refine ⟨54792345256593401219362633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73056460342124534959150177 54792345256593401219362633)
      ·
        refine ⟨41094258942445050914521975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54792345256593401219362633 41094258942445050914521975)
        ·
          refine ⟨61641388413667576371782963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41094258942445050914521975 61641388413667576371782963)
          ·
            refine ⟨92462082620501364557674445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61641388413667576371782963 92462082620501364557674445)
            ·
              refine ⟨34673280982688011709127917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92462082620501364557674445 34673280982688011709127917)
              ·
                refine ⟨13002480368508004390922969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34673280982688011709127917 13002480368508004390922969)
                ·
                  refine ⟨9751860276381003293192227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13002480368508004390922969 9751860276381003293192227)
                  ·
                    refine ⟨14627790414571504939788341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9751860276381003293192227 14627790414571504939788341)
                    ·
                      refine ⟨1371355351366078588105157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14627790414571504939788341 1371355351366078588105157)
                      ·
                        rfl

theorem cell23_2670705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2670705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670705 prefixEnd_2670705 := by exact prefixLift 2670705
  have htrace : WordTrace (prefixWord ++ tailWord_2670705) baseStart_2670705 baseEnd_2670705 := by
    simpa [prefixWord, tailWord_2670705, baseEnd_2670705] using wordTrace_append hprefix tailTrace_2670705
  have hstable : (prefixWord ++ tailWord_2670705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670705).length < 2 ^ (prefixWord ++ tailWord_2670705).sum := by decide
  have hdescent : baseEnd_2670705 < baseStart_2670705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670859 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 3]
def baseStart_2670859 : Nat := 118140960795 + 2670859 * 2 ^ 59
def prefixEnd_2670859 : Nat := 4983230072969 + 3 ^ 40 * 2670859 * 2
def baseEnd_2670859 : Nat := 1371434427386870985579449

theorem tailTrace_2670859 : CollatzResearch.WordTrace tailWord_2670859 prefixEnd_2670859 1371434427386870985579449 := by
  unfold tailWord_2670859
  simp only [CollatzResearch.WordTrace]
  refine ⟨97414230630941464246639631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64942820420627642831093087 97414230630941464246639631)
  ·
    refine ⟨146121345946412196369959447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97414230630941464246639631 146121345946412196369959447)
    ·
      refine ⟨219182018919618294554939171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146121345946412196369959447 219182018919618294554939171)
      ·
        refine ⟨328773028379427441832408757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219182018919618294554939171 328773028379427441832408757)
        ·
          refine ⟨30822471410571322671788321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 328773028379427441832408757 30822471410571322671788321)
          ·
            refine ⟨23116853557928492003841241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30822471410571322671788321 23116853557928492003841241)
            ·
              refine ⟨17337640168446369002880931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23116853557928492003841241 17337640168446369002880931)
              ·
                refine ⟨26006460252669553504321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17337640168446369002880931 26006460252669553504321397)
                ·
                  refine ⟨2438105648687770641030131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26006460252669553504321397 2438105648687770641030131)
                  ·
                    refine ⟨3657158473031655961545197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2438105648687770641030131 3657158473031655961545197)
                    ·
                      refine ⟨1371434427386870985579449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657158473031655961545197 1371434427386870985579449)
                      ·
                        rfl

theorem cell23_2670859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 3].length) (baseStart_2670859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670859 prefixEnd_2670859 := by exact prefixLift 2670859
  have htrace : WordTrace (prefixWord ++ tailWord_2670859) baseStart_2670859 baseEnd_2670859 := by
    simpa [prefixWord, tailWord_2670859, baseEnd_2670859] using wordTrace_append hprefix tailTrace_2670859
  have hstable : (prefixWord ++ tailWord_2670859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670859).length < 2 ^ (prefixWord ++ tailWord_2670859).sum := by decide
  have hdescent : baseEnd_2670859 < baseStart_2670859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670869 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_2670869 : Nat := 118140960795 + 2670869 * 2 ^ 59
def prefixEnd_2670869 : Nat := 4983230072969 + 3 ^ 40 * 2670869 * 2
def baseEnd_2670869 : Nat := 1371439562193415946454403

theorem tailTrace_2670869 : CollatzResearch.WordTrace tailWord_2670869 prefixEnd_2670869 1371439562193415946454403 := by
  unfold tailWord_2670869
  simp only [CollatzResearch.WordTrace]
  refine ⟨97414595360905235954503661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64943063573936823969669107 97414595360905235954503661)
  ·
    refine ⟨36530473260339463482938873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97414595360905235954503661 36530473260339463482938873)
    ·
      refine ⟨27397854945254597612204155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36530473260339463482938873 27397854945254597612204155)
      ·
        refine ⟨41096782417881896418306233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27397854945254597612204155 41096782417881896418306233)
        ·
          refine ⟨30822586813411422313729675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41096782417881896418306233 30822586813411422313729675)
          ·
            refine ⟨46233880220117133470594513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30822586813411422313729675 46233880220117133470594513)
            ·
              refine ⟨34675410165087850102945885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46233880220117133470594513 34675410165087850102945885)
              ·
                refine ⟨13003278811907943788604707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34675410165087850102945885 13003278811907943788604707)
                ·
                  refine ⟨19504918217861915682907061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13003278811907943788604707 19504918217861915682907061)
                  ·
                    refine ⟨1828586082924554595272537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19504918217861915682907061 1828586082924554595272537)
                    ·
                      refine ⟨1371439562193415946454403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828586082924554595272537 1371439562193415946454403)
                      ·
                        rfl

theorem cell23_2670869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_2670869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670869 prefixEnd_2670869 := by exact prefixLift 2670869
  have htrace : WordTrace (prefixWord ++ tailWord_2670869) baseStart_2670869 baseEnd_2670869 := by
    simpa [prefixWord, tailWord_2670869, baseEnd_2670869] using wordTrace_append hprefix tailTrace_2670869
  have hstable : (prefixWord ++ tailWord_2670869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670869).length < 2 ^ (prefixWord ++ tailWord_2670869).sum := by decide
  have hdescent : baseEnd_2670869 < baseStart_2670869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670887 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2670887 : Nat := 118140960795 + 2670887 * 2 ^ 59
def prefixEnd_2670887 : Nat := 4983230072969 + 3 ^ 40 * 2670887 * 2
def baseEnd_2670887 : Nat := 457149601615065625343107

theorem tailTrace_2670887 : CollatzResearch.WordTrace tailWord_2670887 prefixEnd_2670887 457149601615065625343107 := by
  unfold tailWord_2670887
  simp only [CollatzResearch.WordTrace]
  refine ⟨97415251874840025028658915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64943501249893350019105943 97415251874840025028658915)
  ·
    refine ⟨146122877812260037542988373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97415251874840025028658915 146122877812260037542988373)
    ·
      refine ⟨1712377474362422314956895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 146122877812260037542988373 1712377474362422314956895)
      ·
        refine ⟨2568566211543633472435343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712377474362422314956895 2568566211543633472435343)
        ·
          refine ⟨3852849317315450208653015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568566211543633472435343 3852849317315450208653015)
          ·
            refine ⟨5779273975973175312979523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852849317315450208653015 5779273975973175312979523)
            ·
              refine ⟨8668910963959762969469285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779273975973175312979523 8668910963959762969469285)
              ·
                refine ⟨1625420805742455556775491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8668910963959762969469285 1625420805742455556775491)
                ·
                  refine ⟨2438131208613683335163237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625420805742455556775491 2438131208613683335163237)
                  ·
                    refine ⟨457149601615065625343107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438131208613683335163237 457149601615065625343107)
                    ·
                      rfl

theorem cell23_2670887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2670887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670887 prefixEnd_2670887 := by exact prefixLift 2670887
  have htrace : WordTrace (prefixWord ++ tailWord_2670887) baseStart_2670887 baseEnd_2670887 := by
    simpa [prefixWord, tailWord_2670887, baseEnd_2670887] using wordTrace_append hprefix tailTrace_2670887
  have hstable : (prefixWord ++ tailWord_2670887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670887).length < 2 ^ (prefixWord ++ tailWord_2670887).sum := by decide
  have hdescent : baseEnd_2670887 < baseStart_2670887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670919 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2670919 : Nat := 118140960795 + 2670919 * 2 ^ 59
def prefixEnd_2670919 : Nat := 4983230072969 + 3 ^ 40 * 2670919 * 2
def baseEnd_2670919 : Nat := 1371465236226140750829173

theorem tailTrace_2670919 : CollatzResearch.WordTrace tailWord_2670919 prefixEnd_2670919 1371465236226140750829173 := by
  unfold tailWord_2670919
  simp only [CollatzResearch.WordTrace]
  refine ⟨97416419010724094493823811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64944279340482729662549207 97416419010724094493823811)
  ·
    refine ⟨146124628516086141740735717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97416419010724094493823811 146124628516086141740735717)
    ·
      refine ⟨27398367846766151576387947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146124628516086141740735717 27398367846766151576387947)
      ·
        refine ⟨41097551770149227364581921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398367846766151576387947 41097551770149227364581921)
        ·
          refine ⟨30823163827611920523436441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41097551770149227364581921 30823163827611920523436441)
          ·
            refine ⟨23117372870708940392577331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30823163827611920523436441 23117372870708940392577331)
            ·
              refine ⟨34676059306063410588865997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117372870708940392577331 34676059306063410588865997)
              ·
                refine ⟨13003522239773778970824749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34676059306063410588865997 13003522239773778970824749)
                ·
                  refine ⟨4876320839915167114059281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13003522239773778970824749 4876320839915167114059281)
                  ·
                    refine ⟨3657240629936375335544461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876320839915167114059281 3657240629936375335544461)
                    ·
                      refine ⟨1371465236226140750829173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657240629936375335544461 1371465236226140750829173)
                      ·
                        rfl

theorem cell23_2670919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2670919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670919 prefixEnd_2670919 := by exact prefixLift 2670919
  have htrace : WordTrace (prefixWord ++ tailWord_2670919) baseStart_2670919 baseEnd_2670919 := by
    simpa [prefixWord, tailWord_2670919, baseEnd_2670919] using wordTrace_append hprefix tailTrace_2670919
  have hstable : (prefixWord ++ tailWord_2670919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670919).length < 2 ^ (prefixWord ++ tailWord_2670919).sum := by decide
  have hdescent : baseEnd_2670919 < baseStart_2670919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670929 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2670929 : Nat := 118140960795 + 2670929 * 2 ^ 59
def prefixEnd_2670929 : Nat := 4983230072969 + 3 ^ 40 * 2670929 * 2
def baseEnd_2670929 : Nat := 1371470371032685711704127

theorem tailTrace_2670929 : CollatzResearch.WordTrace tailWord_2670929 prefixEnd_2670929 1371470371032685711704127 := by
  unfold tailWord_2670929
  simp only [CollatzResearch.WordTrace]
  refine ⟨97416783740687866201687841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64944522493791910801125227 97416783740687866201687841)
  ·
    refine ⟨73062587805515899651265881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97416783740687866201687841 73062587805515899651265881)
    ·
      refine ⟨54796940854136924738449411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73062587805515899651265881 54796940854136924738449411)
      ·
        refine ⟨82195411281205387107674117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54796940854136924738449411 82195411281205387107674117)
        ·
          refine ⟨15411639615226010082688897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82195411281205387107674117 15411639615226010082688897)
          ·
            refine ⟨11558729711419507562016673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15411639615226010082688897 11558729711419507562016673)
            ·
              refine ⟨8669047283564630671512505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11558729711419507562016673 8669047283564630671512505)
              ·
                refine ⟨6501785462673473003634379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669047283564630671512505 6501785462673473003634379)
                ·
                  refine ⟨9752678194010209505451569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6501785462673473003634379 9752678194010209505451569)
                  ·
                    refine ⟨7314508645507657129088677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9752678194010209505451569 7314508645507657129088677)
                    ·
                      refine ⟨1371470371032685711704127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7314508645507657129088677 1371470371032685711704127)
                      ·
                        rfl

theorem cell23_2670929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2670929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670929 prefixEnd_2670929 := by exact prefixLift 2670929
  have htrace : WordTrace (prefixWord ++ tailWord_2670929) baseStart_2670929 baseEnd_2670929 := by
    simpa [prefixWord, tailWord_2670929, baseEnd_2670929] using wordTrace_append hprefix tailTrace_2670929
  have hstable : (prefixWord ++ tailWord_2670929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670929).length < 2 ^ (prefixWord ++ tailWord_2670929).sum := by decide
  have hdescent : baseEnd_2670929 < baseStart_2670929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670959 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 7, 2]
def baseStart_2670959 : Nat := 118140960795 + 2670959 * 2 ^ 59
def prefixEnd_2670959 : Nat := 4983230072969 + 3 ^ 40 * 2670959 * 2
def baseEnd_2670959 : Nat := 1371485775452320594328989

theorem tailTrace_2670959 : CollatzResearch.WordTrace tailWord_2670959 prefixEnd_2670959 1371485775452320594328989 := by
  unfold tailWord_2670959
  simp only [CollatzResearch.WordTrace]
  refine ⟨97417877930579181325279931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64945251953719454216853287 97417877930579181325279931)
  ·
    refine ⟨146126816895868771987919897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97417877930579181325279931 146126816895868771987919897)
    ·
      refine ⟨109595112671901578990939923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146126816895868771987919897 109595112671901578990939923)
      ·
        refine ⟨164392669007852368486409885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109595112671901578990939923 164392669007852368486409885)
        ·
          refine ⟨61647250877944638182403707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164392669007852368486409885 61647250877944638182403707)
          ·
            refine ⟨92470876316916957273605561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61647250877944638182403707 92470876316916957273605561)
            ·
              refine ⟨69353157237687717955204171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92470876316916957273605561 69353157237687717955204171)
              ·
                refine ⟨104029735856531576932806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69353157237687717955204171 104029735856531576932806257)
                ·
                  refine ⟨78022301892398682699604693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104029735856531576932806257 78022301892398682699604693)
                  ·
                    refine ⟨1828647700603094125771985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78022301892398682699604693 1828647700603094125771985)
                    ·
                      refine ⟨1371485775452320594328989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828647700603094125771985 1371485775452320594328989)
                      ·
                        rfl

theorem cell23_2670959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7, 2].length) (baseStart_2670959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670959 prefixEnd_2670959 := by exact prefixLift 2670959
  have htrace : WordTrace (prefixWord ++ tailWord_2670959) baseStart_2670959 baseEnd_2670959 := by
    simpa [prefixWord, tailWord_2670959, baseEnd_2670959] using wordTrace_append hprefix tailTrace_2670959
  have hstable : (prefixWord ++ tailWord_2670959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670959).length < 2 ^ (prefixWord ++ tailWord_2670959).sum := by decide
  have hdescent : baseEnd_2670959 < baseStart_2670959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2670972 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2670972 : Nat := 118140960795 + 2670972 * 2 ^ 59
def prefixEnd_2670972 : Nat := 4983230072969 + 3 ^ 40 * 2670972 * 2
def baseEnd_2670972 : Nat := 1371492450700829043466429

theorem tailTrace_2670972 : CollatzResearch.WordTrace tailWord_2670972 prefixEnd_2670972 1371492450700829043466429 := by
  unfold tailWord_2670972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48709176039766042272751585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64945568053021389697002113 48709176039766042272751585)
  ·
    refine ⟨36531882029824531704563689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48709176039766042272751585 36531882029824531704563689)
    ·
      refine ⟨27398911522368398778422767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36531882029824531704563689 27398911522368398778422767)
      ·
        refine ⟨41098367283552598167634151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398911522368398778422767 41098367283552598167634151)
        ·
          refine ⟨61647550925328897251451227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41098367283552598167634151 61647550925328897251451227)
          ·
            refine ⟨92471326387993345877176841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61647550925328897251451227 92471326387993345877176841)
            ·
              refine ⟨69353494790995009407882631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92471326387993345877176841 69353494790995009407882631)
              ·
                refine ⟨104030242186492514111823947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69353494790995009407882631 104030242186492514111823947)
                ·
                  refine ⟨156045363279738771167735921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104030242186492514111823947 156045363279738771167735921)
                  ·
                    refine ⟨117034022459804078375801941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156045363279738771167735921 117034022459804078375801941)
                    ·
                      refine ⟨1371492450700829043466429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117034022459804078375801941 1371492450700829043466429)
                      ·
                        rfl

theorem cell23_2670972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2670972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2670972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2670972 prefixEnd_2670972 := by exact prefixLift 2670972
  have htrace : WordTrace (prefixWord ++ tailWord_2670972) baseStart_2670972 baseEnd_2670972 := by
    simpa [prefixWord, tailWord_2670972, baseEnd_2670972] using wordTrace_append hprefix tailTrace_2670972
  have hstable : (prefixWord ++ tailWord_2670972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2670972).length < 2 ^ (prefixWord ++ tailWord_2670972).sum := by decide
  have hdescent : baseEnd_2670972 < baseStart_2670972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2670972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671039 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_2671039 : Nat := 118140960795 + 2671039 * 2 ^ 59
def prefixEnd_2671039 : Nat := 4983230072969 + 3 ^ 40 * 2671039 * 2
def baseEnd_2671039 : Nat := 1371526853904680281328621

theorem tailTrace_2671039 : CollatzResearch.WordTrace tailWord_2671039 prefixEnd_2671039 1371526853904680281328621 := by
  unfold tailWord_2671039
  simp only [CollatzResearch.WordTrace]
  refine ⟨97420795770289354988192171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64947197180192903325461447 97420795770289354988192171)
  ·
    refine ⟨146131193655434032482288257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97420795770289354988192171 146131193655434032482288257)
    ·
      refine ⟨109598395241575524361716193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146131193655434032482288257 109598395241575524361716193)
      ·
        refine ⟨82198796431181643271287145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109598395241575524361716193 82198796431181643271287145)
        ·
          refine ⟨61649097323386232453465359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82198796431181643271287145 61649097323386232453465359)
          ·
            refine ⟨92473645985079348680198039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61649097323386232453465359 92473645985079348680198039)
            ·
              refine ⟨138710468977619023020297059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92473645985079348680198039 138710468977619023020297059)
              ·
                refine ⟨208065703466428534530445589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138710468977619023020297059 208065703466428534530445589)
                ·
                  refine ⟨9753079849988837556114637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208065703466428534530445589 9753079849988837556114637)
                  ·
                    refine ⟨3657404943745814083542989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9753079849988837556114637 3657404943745814083542989)
                    ·
                      refine ⟨1371526853904680281328621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657404943745814083542989 1371526853904680281328621)
                      ·
                        rfl

theorem cell23_2671039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_2671039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671039 prefixEnd_2671039 := by exact prefixLift 2671039
  have htrace : WordTrace (prefixWord ++ tailWord_2671039) baseStart_2671039 baseEnd_2671039 := by
    simpa [prefixWord, tailWord_2671039, baseEnd_2671039] using wordTrace_append hprefix tailTrace_2671039
  have hstable : (prefixWord ++ tailWord_2671039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671039).length < 2 ^ (prefixWord ++ tailWord_2671039).sum := by decide
  have hdescent : baseEnd_2671039 < baseStart_2671039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671066 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_2671066 : Nat := 118140960795 + 2671066 * 2 ^ 59
def prefixEnd_2671066 : Nat := 4983230072969 + 3 ^ 40 * 2671066 * 2
def baseEnd_2671066 : Nat := 1371540717882351675690997

theorem tailTrace_2671066 : CollatzResearch.WordTrace tailWord_2671066 prefixEnd_2671066 1371540717882351675690997 := by
  unfold tailWord_2671066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24355445135297884649856263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64947853694127692399616701 24355445135297884649856263)
  ·
    refine ⟨36533167702946826974784395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24355445135297884649856263 36533167702946826974784395)
    ·
      refine ⟨54799751554420240462176593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36533167702946826974784395 54799751554420240462176593)
      ·
        refine ⟨41099813665815180346632445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54799751554420240462176593 41099813665815180346632445)
        ·
          refine ⟨15412430124680692629987167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41099813665815180346632445 15412430124680692629987167)
          ·
            refine ⟨23118645187021038944980751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15412430124680692629987167 23118645187021038944980751)
            ·
              refine ⟨34677967780531558417471127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23118645187021038944980751 34677967780531558417471127)
              ·
                refine ⟨52016951670797337626206691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34677967780531558417471127 52016951670797337626206691)
                ·
                  refine ⟨78025427506196006439310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52016951670797337626206691 78025427506196006439310037)
                  ·
                    refine ⟨1828720957176468900921329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78025427506196006439310037 1828720957176468900921329)
                    ·
                      refine ⟨1371540717882351675690997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828720957176468900921329 1371540717882351675690997)
                      ·
                        rfl

theorem cell23_2671066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_2671066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671066 prefixEnd_2671066 := by exact prefixLift 2671066
  have htrace : WordTrace (prefixWord ++ tailWord_2671066) baseStart_2671066 baseEnd_2671066 := by
    simpa [prefixWord, tailWord_2671066, baseEnd_2671066] using wordTrace_append hprefix tailTrace_2671066
  have hstable : (prefixWord ++ tailWord_2671066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671066).length < 2 ^ (prefixWord ++ tailWord_2671066).sum := by decide
  have hdescent : baseEnd_2671066 < baseStart_2671066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671093 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2671093 : Nat := 118140960795 + 2671093 * 2 ^ 59
def prefixEnd_2671093 : Nat := 4983230072969 + 3 ^ 40 * 2671093 * 2
def baseEnd_2671093 : Nat := 457184860620007690017791

theorem tailTrace_2671093 : CollatzResearch.WordTrace tailWord_2671093 prefixEnd_2671093 457184860620007690017791 := by
  unfold tailWord_2671093
  simp only [CollatzResearch.WordTrace]
  refine ⟨97422765312093722210657933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64948510208062481473771955 97422765312093722210657933)
  ·
    refine ⟨36533536992035145828996725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97422765312093722210657933 36533536992035145828996725)
    ·
      refine ⟨3425019093003294921468443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36533536992035145828996725 3425019093003294921468443)
      ·
        refine ⟨5137528639504942382202665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425019093003294921468443 5137528639504942382202665)
        ·
          refine ⟨3853146479628706786651999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5137528639504942382202665 3853146479628706786651999)
          ·
            refine ⟨5779719719443060179977999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853146479628706786651999 5779719719443060179977999)
            ·
              refine ⟨8669579579164590269966999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779719719443060179977999 8669579579164590269966999)
              ·
                refine ⟨13004369368746885404950499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8669579579164590269966999 13004369368746885404950499)
                ·
                  refine ⟨19506554053120328107425749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13004369368746885404950499 19506554053120328107425749)
                  ·
                    refine ⟨457184860620007690017791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19506554053120328107425749 457184860620007690017791)
                    ·
                      rfl

theorem cell23_2671093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2671093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671093 prefixEnd_2671093 := by exact prefixLift 2671093
  have htrace : WordTrace (prefixWord ++ tailWord_2671093) baseStart_2671093 baseEnd_2671093 := by
    simpa [prefixWord, tailWord_2671093, baseEnd_2671093] using wordTrace_append hprefix tailTrace_2671093
  have hstable : (prefixWord ++ tailWord_2671093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671093).length < 2 ^ (prefixWord ++ tailWord_2671093).sum := by decide
  have hdescent : baseEnd_2671093 < baseStart_2671093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671096 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_2671096 : Nat := 118140960795 + 2671096 * 2 ^ 59
def prefixEnd_2671096 : Nat := 4983230072969 + 3 ^ 40 * 2671096 * 2
def baseEnd_2671096 : Nat := 1371556122301986558315859

theorem tailTrace_2671096 : CollatzResearch.WordTrace tailWord_2671096 prefixEnd_2671096 1371556122301986558315859 := by
  unfold tailWord_2671096
  simp only [CollatzResearch.WordTrace]
  refine ⟨48711437365541426861508571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64948583154055235815344761 48711437365541426861508571)
  ·
    refine ⟨73067156048312140292262857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48711437365541426861508571 73067156048312140292262857)
    ·
      refine ⟨54800367036234105219197143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73067156048312140292262857 54800367036234105219197143)
      ·
        refine ⟨82200550554351157828795715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54800367036234105219197143 82200550554351157828795715)
        ·
          refine ⟨123300825831526736743193573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82200550554351157828795715 123300825831526736743193573)
          ·
            refine ⟨23118904843411263139348795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123300825831526736743193573 23118904843411263139348795)
            ·
              refine ⟨34678357265116894709023193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23118904843411263139348795 34678357265116894709023193)
              ·
                refine ⟨26008767948837671031767395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34678357265116894709023193 26008767948837671031767395)
                ·
                  refine ⟨39013151923256506547651093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26008767948837671031767395 39013151923256506547651093)
                  ·
                    refine ⟨1828741496402648744421145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39013151923256506547651093 1828741496402648744421145)
                    ·
                      refine ⟨1371556122301986558315859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828741496402648744421145 1371556122301986558315859)
                      ·
                        rfl

theorem cell23_2671096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_2671096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671096 prefixEnd_2671096 := by exact prefixLift 2671096
  have htrace : WordTrace (prefixWord ++ tailWord_2671096) baseStart_2671096 baseEnd_2671096 := by
    simpa [prefixWord, tailWord_2671096, baseEnd_2671096] using wordTrace_append hprefix tailTrace_2671096
  have hstable : (prefixWord ++ tailWord_2671096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671096).length < 2 ^ (prefixWord ++ tailWord_2671096).sum := by decide
  have hdescent : baseEnd_2671096 < baseStart_2671096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671109 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2671109 : Nat := 118140960795 + 2671109 * 2 ^ 59
def prefixEnd_2671109 : Nat := 4983230072969 + 3 ^ 40 * 2671109 * 2
def baseEnd_2671109 : Nat := 1371562797550495007453299

theorem tailTrace_2671109 : CollatzResearch.WordTrace tailWord_2671109 prefixEnd_2671109 1371562797550495007453299 := by
  unfold tailWord_2671109
  simp only [CollatzResearch.WordTrace]
  refine ⟨97423348880035756943240381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64948899253357171295493587 97423348880035756943240381)
  ·
    refine ⟨36533755830013408853715143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97423348880035756943240381 36533755830013408853715143)
    ·
      refine ⟨54800633745020113280572715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36533755830013408853715143 54800633745020113280572715)
      ·
        refine ⟨82200950617530169920859073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54800633745020113280572715 82200950617530169920859073)
        ·
          refine ⟨61650712963147627440644305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82200950617530169920859073 61650712963147627440644305)
          ·
            refine ⟨46238034722360720580483229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61650712963147627440644305 46238034722360720580483229)
            ·
              refine ⟨17339263020885270217681211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46238034722360720580483229 17339263020885270217681211)
              ·
                refine ⟨26008894531327905326521817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17339263020885270217681211 26008894531327905326521817)
                ·
                  refine ⟨19506670898495928994891363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26008894531327905326521817 19506670898495928994891363)
                  ·
                    refine ⟨29260006347743893492337045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19506670898495928994891363 29260006347743893492337045)
                    ·
                      refine ⟨1371562797550495007453299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29260006347743893492337045 1371562797550495007453299)
                      ·
                        rfl

theorem cell23_2671109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2671109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671109 prefixEnd_2671109 := by exact prefixLift 2671109
  have htrace : WordTrace (prefixWord ++ tailWord_2671109) baseStart_2671109 baseEnd_2671109 := by
    simpa [prefixWord, tailWord_2671109, baseEnd_2671109] using wordTrace_append hprefix tailTrace_2671109
  have hstable : (prefixWord ++ tailWord_2671109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671109).length < 2 ^ (prefixWord ++ tailWord_2671109).sum := by decide
  have hdescent : baseEnd_2671109 < baseStart_2671109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671123 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 1, 4]
def baseStart_2671123 : Nat := 118140960795 + 2671123 * 2 ^ 59
def prefixEnd_2671123 : Nat := 4983230072969 + 3 ^ 40 * 2671123 * 2
def baseEnd_2671123 : Nat := 457189995426552650892745

theorem tailTrace_2671123 : CollatzResearch.WordTrace tailWord_2671123 prefixEnd_2671123 457189995426552650892745 := by
  unfold tailWord_2671123
  simp only [CollatzResearch.WordTrace]
  refine ⟨97423859501985037334250023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64949239667990024889500015 97423859501985037334250023)
  ·
    refine ⟨146135789252977556001375035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97423859501985037334250023 146135789252977556001375035)
    ·
      refine ⟨219203683879466334002062553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146135789252977556001375035 219203683879466334002062553)
      ·
        refine ⟨164402762909599750501546915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219203683879466334002062553 164402762909599750501546915)
        ·
          refine ⟨246604144364399625752320373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164402762909599750501546915 246604144364399625752320373)
          ·
            refine ⟨23119138534162464914280035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246604144364399625752320373 23119138534162464914280035)
            ·
              refine ⟨34678707801243697371420053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23119138534162464914280035 34678707801243697371420053)
              ·
                refine ⟨1625564428183298314285315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34678707801243697371420053 1625564428183298314285315)
                ·
                  refine ⟨2438346642274947471427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625564428183298314285315 2438346642274947471427973)
                  ·
                    refine ⟨457189995426552650892745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438346642274947471427973 457189995426552650892745)
                    ·
                      rfl

theorem cell23_2671123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 4].length) (baseStart_2671123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671123 prefixEnd_2671123 := by exact prefixLift 2671123
  have htrace : WordTrace (prefixWord ++ tailWord_2671123) baseStart_2671123 baseEnd_2671123 := by
    simpa [prefixWord, tailWord_2671123, baseEnd_2671123] using wordTrace_append hprefix tailTrace_2671123
  have hstable : (prefixWord ++ tailWord_2671123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671123).length < 2 ^ (prefixWord ++ tailWord_2671123).sum := by decide
  have hdescent : baseEnd_2671123 < baseStart_2671123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671173 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_2671173 : Nat := 118140960795 + 2671173 * 2 ^ 59
def prefixEnd_2671173 : Nat := 4983230072969 + 3 ^ 40 * 2671173 * 2
def baseEnd_2671173 : Nat := 1371595660312382757053005

theorem tailTrace_2671173 : CollatzResearch.WordTrace tailWord_2671173 prefixEnd_2671173 1371595660312382757053005 := by
  unfold tailWord_2671173
  simp only [CollatzResearch.WordTrace]
  refine ⟨97425683151803895873570173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64950455434535930582380115 97425683151803895873570173)
  ·
    refine ⟨36534631181926460952588815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97425683151803895873570173 36534631181926460952588815)
    ·
      refine ⟨54801946772889691428883223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36534631181926460952588815 54801946772889691428883223)
      ·
        refine ⟨82202920159334537143324835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54801946772889691428883223 82202920159334537143324835)
        ·
          refine ⟨123304380239001805714987253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82202920159334537143324835 123304380239001805714987253)
          ·
            refine ⟨11559785647406419285780055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123304380239001805714987253 11559785647406419285780055)
            ·
              refine ⟨17339678471109628928670083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11559785647406419285780055 17339678471109628928670083)
              ·
                refine ⟨26009517706664443393005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17339678471109628928670083 26009517706664443393005125)
                ·
                  refine ⟨4876784569999583136188461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26009517706664443393005125 4876784569999583136188461)
                  ·
                    refine ⟨1828794213749843676070673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4876784569999583136188461 1828794213749843676070673)
                    ·
                      refine ⟨1371595660312382757053005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828794213749843676070673 1371595660312382757053005)
                      ·
                        rfl

theorem cell23_2671173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_2671173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671173 prefixEnd_2671173 := by exact prefixLift 2671173
  have htrace : WordTrace (prefixWord ++ tailWord_2671173) baseStart_2671173 baseEnd_2671173 := by
    simpa [prefixWord, tailWord_2671173, baseEnd_2671173] using wordTrace_append hprefix tailTrace_2671173
  have hstable : (prefixWord ++ tailWord_2671173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671173).length < 2 ^ (prefixWord ++ tailWord_2671173).sum := by decide
  have hdescent : baseEnd_2671173 < baseStart_2671173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671213 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2671213 : Nat := 118140960795 + 2671213 * 2 ^ 59
def prefixEnd_2671213 : Nat := 4983230072969 + 3 ^ 40 * 2671213 * 2
def baseEnd_2671213 : Nat := 457205399846187533517607

theorem tailTrace_2671213 : CollatzResearch.WordTrace tailWord_2671213 prefixEnd_2671213 457205399846187533517607 := by
  unfold tailWord_2671213
  simp only [CollatzResearch.WordTrace]
  refine ⟨97427142071658982705026293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64951428047772655136684195 97427142071658982705026293)
  ·
    refine ⟨9133794569218029628596215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97427142071658982705026293 9133794569218029628596215)
    ·
      refine ⟨13700691853827044442894323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9133794569218029628596215 13700691853827044442894323)
      ·
        refine ⟨20551037780740566664341485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13700691853827044442894323 20551037780740566664341485)
        ·
          refine ⟨7706639167777712499128057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20551037780740566664341485 7706639167777712499128057)
          ·
            refine ⟨5779979375833284374346043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7706639167777712499128057 5779979375833284374346043)
            ·
              refine ⟨8669969063749926561519065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5779979375833284374346043 8669969063749926561519065)
              ·
                refine ⟨6502476797812444921139299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8669969063749926561519065 6502476797812444921139299)
                ·
                  refine ⟨9753715196718667381708949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6502476797812444921139299 9753715196718667381708949)
                  ·
                    refine ⟨457205399846187533517607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9753715196718667381708949 457205399846187533517607)
                    ·
                      rfl

theorem cell23_2671213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2671213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671213 prefixEnd_2671213 := by exact prefixLift 2671213
  have htrace : WordTrace (prefixWord ++ tailWord_2671213) baseStart_2671213 baseEnd_2671213 := by
    simpa [prefixWord, tailWord_2671213, baseEnd_2671213] using wordTrace_append hprefix tailTrace_2671213
  have hstable : (prefixWord ++ tailWord_2671213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671213).length < 2 ^ (prefixWord ++ tailWord_2671213).sum := by decide
  have hdescent : baseEnd_2671213 < baseStart_2671213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671223 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_2671223 : Nat := 118140960795 + 2671223 * 2 ^ 59
def prefixEnd_2671223 : Nat := 4983230072969 + 3 ^ 40 * 2671223 * 2
def baseEnd_2671223 : Nat := 1371621334345107561427775

theorem tailTrace_2671223 : CollatzResearch.WordTrace tailWord_2671223 prefixEnd_2671223 1371621334345107561427775 := by
  unfold tailWord_2671223
  simp only [CollatzResearch.WordTrace]
  refine ⟨97427506801622754412890323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64951671201081836275260215 97427506801622754412890323)
  ·
    refine ⟨146141260202434131619335485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97427506801622754412890323 146141260202434131619335485)
    ·
      refine ⟨54802972575912799357250807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146141260202434131619335485 54802972575912799357250807)
      ·
        refine ⟨82204458863869199035876211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54802972575912799357250807 82204458863869199035876211)
        ·
          refine ⟨123306688295803798553814317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82204458863869199035876211 123306688295803798553814317)
          ·
            refine ⟨46240008110926424457680369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123306688295803798553814317 46240008110926424457680369)
            ·
              refine ⟨34680006083194818343260277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46240008110926424457680369 34680006083194818343260277)
              ·
                refine ⟨3251250570299514219680651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34680006083194818343260277 3251250570299514219680651)
                ·
                  refine ⟨4876875855449271329520977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251250570299514219680651 4876875855449271329520977)
                  ·
                    refine ⟨3657656891586953497140733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876875855449271329520977 3657656891586953497140733)
                    ·
                      refine ⟨1371621334345107561427775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657656891586953497140733 1371621334345107561427775)
                      ·
                        rfl

theorem cell23_2671223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_2671223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671223 prefixEnd_2671223 := by exact prefixLift 2671223
  have htrace : WordTrace (prefixWord ++ tailWord_2671223) baseStart_2671223 baseEnd_2671223 := by
    simpa [prefixWord, tailWord_2671223, baseEnd_2671223] using wordTrace_append hprefix tailTrace_2671223
  have hstable : (prefixWord ++ tailWord_2671223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671223).length < 2 ^ (prefixWord ++ tailWord_2671223).sum := by decide
  have hdescent : baseEnd_2671223 < baseStart_2671223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671250 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2671250 : Nat := 118140960795 + 2671250 * 2 ^ 59
def prefixEnd_2671250 : Nat := 4983230072969 + 3 ^ 40 * 2671250 * 2
def baseEnd_2671250 : Nat := 1371635198322778955790151

theorem tailTrace_2671250 : CollatzResearch.WordTrace tailWord_2671250 prefixEnd_2671250 1371635198322778955790151 := by
  unfold tailWord_2671250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357122893131234506030801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64952327715016625349415469 24357122893131234506030801)
  ·
    refine ⟨18267842169848425879523101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24357122893131234506030801 18267842169848425879523101)
    ·
      refine ⟨6850440813693159704821163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18267842169848425879523101 6850440813693159704821163)
      ·
        refine ⟨10275661220539739557231745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850440813693159704821163 10275661220539739557231745)
        ·
          refine ⟨7706745915404804667923809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10275661220539739557231745 7706745915404804667923809)
          ·
            refine ⟨5780059436553603500942857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7706745915404804667923809 5780059436553603500942857)
            ·
              refine ⟨4335044577415202625707143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5780059436553603500942857 4335044577415202625707143)
              ·
                refine ⟨6502566866122803938560715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335044577415202625707143 6502566866122803938560715)
                ·
                  refine ⟨9753850299184205907841073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6502566866122803938560715 9753850299184205907841073)
                  ·
                    refine ⟨7315387724388154430880805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9753850299184205907841073 7315387724388154430880805)
                    ·
                      refine ⟨1371635198322778955790151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7315387724388154430880805 1371635198322778955790151)
                      ·
                        rfl

theorem cell23_2671250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2671250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671250 prefixEnd_2671250 := by exact prefixLift 2671250
  have htrace : WordTrace (prefixWord ++ tailWord_2671250) baseStart_2671250 baseEnd_2671250 := by
    simpa [prefixWord, tailWord_2671250, baseEnd_2671250] using wordTrace_append hprefix tailTrace_2671250
  have hstable : (prefixWord ++ tailWord_2671250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671250).length < 2 ^ (prefixWord ++ tailWord_2671250).sum := by decide
  have hdescent : baseEnd_2671250 < baseStart_2671250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671253 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_2671253 : Nat := 118140960795 + 2671253 * 2 ^ 59
def prefixEnd_2671253 : Nat := 4983230072969 + 3 ^ 40 * 2671253 * 2
def baseEnd_2671253 : Nat := 1371636738764742444052637

theorem tailTrace_2671253 : CollatzResearch.WordTrace tailWord_2671253 prefixEnd_2671253 1371636738764742444052637 := by
  unfold tailWord_2671253
  simp only [CollatzResearch.WordTrace]
  refine ⟨97428600991514069536482413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64952400661009379690988275 97428600991514069536482413)
  ·
    refine ⟨36535725371817776076180905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97428600991514069536482413 36535725371817776076180905)
    ·
      refine ⟨27401794028863332057135679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36535725371817776076180905 27401794028863332057135679)
      ·
        refine ⟨41102691043294998085703519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27401794028863332057135679 41102691043294998085703519)
        ·
          refine ⟨61654036564942497128555279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41102691043294998085703519 61654036564942497128555279)
          ·
            refine ⟨92481054847413745692832919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61654036564942497128555279 92481054847413745692832919)
            ·
              refine ⟨138721582271120618539249379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92481054847413745692832919 138721582271120618539249379)
              ·
                refine ⟨208082373406680927808874069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138721582271120618539249379 208082373406680927808874069)
                ·
                  refine ⟨2438465313359542122760243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 208082373406680927808874069 2438465313359542122760243)
                  ·
                    refine ⟨3657697970039313184140365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2438465313359542122760243 3657697970039313184140365)
                    ·
                      refine ⟨1371636738764742444052637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657697970039313184140365 1371636738764742444052637)
                      ·
                        rfl

theorem cell23_2671253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_2671253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671253 prefixEnd_2671253 := by exact prefixLift 2671253
  have htrace : WordTrace (prefixWord ++ tailWord_2671253) baseStart_2671253 baseEnd_2671253 := by
    simpa [prefixWord, tailWord_2671253, baseEnd_2671253] using wordTrace_append hprefix tailTrace_2671253
  have hstable : (prefixWord ++ tailWord_2671253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671253).length < 2 ^ (prefixWord ++ tailWord_2671253).sum := by decide
  have hdescent : baseEnd_2671253 < baseStart_2671253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671256 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_2671256 : Nat := 118140960795 + 2671256 * 2 ^ 59
def prefixEnd_2671256 : Nat := 4983230072969 + 3 ^ 40 * 2671256 * 2
def baseEnd_2671256 : Nat := 457212759735568644105041

theorem tailTrace_2671256 : CollatzResearch.WordTrace tailWord_2671256 prefixEnd_2671256 457212759735568644105041 := by
  unfold tailWord_2671256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48714355205251600524420811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64952473607002134032561081 48714355205251600524420811)
  ·
    refine ⟨73071532807877400786631217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48714355205251600524420811 73071532807877400786631217)
    ·
      refine ⟨54803649605908050589973413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73071532807877400786631217 54803649605908050589973413)
      ·
        refine ⟨10275684301107759485620015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54803649605908050589973413 10275684301107759485620015)
        ·
          refine ⟨15413526451661639228430023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10275684301107759485620015 15413526451661639228430023)
          ·
            refine ⟨23120289677492458842645035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15413526451661639228430023 23120289677492458842645035)
            ·
              refine ⟨34680434516238688263967553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23120289677492458842645035 34680434516238688263967553)
              ·
                refine ⟨26010325887179016197975665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34680434516238688263967553 26010325887179016197975665)
                ·
                  refine ⟨19507744415384262148481749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26010325887179016197975665 19507744415384262148481749)
                  ·
                    refine ⟨457212759735568644105041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19507744415384262148481749 457212759735568644105041)
                    ·
                      rfl

theorem cell23_2671256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_2671256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671256 prefixEnd_2671256 := by exact prefixLift 2671256
  have htrace : WordTrace (prefixWord ++ tailWord_2671256) baseStart_2671256 baseEnd_2671256 := by
    simpa [prefixWord, tailWord_2671256, baseEnd_2671256] using wordTrace_append hprefix tailTrace_2671256
  have hstable : (prefixWord ++ tailWord_2671256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671256).length < 2 ^ (prefixWord ++ tailWord_2671256).sum := by decide
  have hdescent : baseEnd_2671256 < baseStart_2671256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671271 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2671271 : Nat := 118140960795 + 2671271 * 2 ^ 59
def prefixEnd_2671271 : Nat := 4983230072969 + 3 ^ 40 * 2671271 * 2
def baseEnd_2671271 : Nat := 1371645981416523373627555

theorem tailTrace_2671271 : CollatzResearch.WordTrace tailWord_2671271 prefixEnd_2671271 1371645981416523373627555 := by
  unfold tailWord_2671271
  simp only [CollatzResearch.WordTrace]
  refine ⟨97429257505448858610637667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64952838336965905740425111 97429257505448858610637667)
  ·
    refine ⟨146143886258173287915956501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97429257505448858610637667 146143886258173287915956501)
    ·
      refine ⟨6850494668351872871060461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146143886258173287915956501 6850494668351872871060461)
      ·
        refine ⟨2568935500631952326647673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6850494668351872871060461 2568935500631952326647673)
        ·
          refine ⟨1926701625473964244985755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568935500631952326647673 1926701625473964244985755)
          ·
            refine ⟨2890052438210946367478633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926701625473964244985755 2890052438210946367478633)
            ·
              refine ⟨2167539328658209775608975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890052438210946367478633 2167539328658209775608975)
              ·
                refine ⟨3251308992987314663413463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167539328658209775608975 3251308992987314663413463)
                ·
                  refine ⟨4876963489480971995120195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251308992987314663413463 4876963489480971995120195)
                  ·
                    refine ⟨7315445234221457992680293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4876963489480971995120195 7315445234221457992680293)
                    ·
                      refine ⟨1371645981416523373627555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7315445234221457992680293 1371645981416523373627555)
                      ·
                        rfl

theorem cell23_2671271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2671271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671271 prefixEnd_2671271 := by exact prefixLift 2671271
  have htrace : WordTrace (prefixWord ++ tailWord_2671271) baseStart_2671271 baseEnd_2671271 := by
    simpa [prefixWord, tailWord_2671271, baseEnd_2671271] using wordTrace_append hprefix tailTrace_2671271
  have hstable : (prefixWord ++ tailWord_2671271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671271).length < 2 ^ (prefixWord ++ tailWord_2671271).sum := by decide
  have hdescent : baseEnd_2671271 < baseStart_2671271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671274 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2671274 : Nat := 118140960795 + 2671274 * 2 ^ 59
def prefixEnd_2671274 : Nat := 4983230072969 + 3 ^ 40 * 2671274 * 2
def baseEnd_2671274 : Nat := 1371647521858486861890041

theorem tailTrace_2671274 : CollatzResearch.WordTrace tailWord_2671274 prefixEnd_2671274 1371647521858486861890041 := by
  unfold tailWord_2671274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357341731109497530749219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64952911282958660081997917 24357341731109497530749219)
  ·
    refine ⟨36536012596664246296123829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24357341731109497530749219 36536012596664246296123829)
    ·
      refine ⟨3425251180937273090261609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36536012596664246296123829 3425251180937273090261609)
      ·
        refine ⟨2568938385702954817696207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3425251180937273090261609 2568938385702954817696207)
        ·
          refine ⟨3853407578554432226544311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568938385702954817696207 3853407578554432226544311)
          ·
            refine ⟨5780111367831648339816467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853407578554432226544311 5780111367831648339816467)
            ·
              refine ⟨8670167051747472509724701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5780111367831648339816467 8670167051747472509724701)
              ·
                refine ⟨3251312644405302191146763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8670167051747472509724701 3251312644405302191146763)
                ·
                  refine ⟨4876968966607953286720145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251312644405302191146763 4876968966607953286720145)
                  ·
                    refine ⟨3657726724955964965040109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4876968966607953286720145 3657726724955964965040109)
                    ·
                      refine ⟨1371647521858486861890041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3657726724955964965040109 1371647521858486861890041)
                      ·
                        rfl

theorem cell23_2671274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2671274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671274 prefixEnd_2671274 := by exact prefixLift 2671274
  have htrace : WordTrace (prefixWord ++ tailWord_2671274) baseStart_2671274 baseEnd_2671274 := by
    simpa [prefixWord, tailWord_2671274, baseEnd_2671274] using wordTrace_append hprefix tailTrace_2671274
  have hstable : (prefixWord ++ tailWord_2671274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671274).length < 2 ^ (prefixWord ++ tailWord_2671274).sum := by decide
  have hdescent : baseEnd_2671274 < baseStart_2671274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671314 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2671314 : Nat := 118140960795 + 2671314 * 2 ^ 59
def prefixEnd_2671314 : Nat := 4983230072969 + 3 ^ 40 * 2671314 * 2
def baseEnd_2671314 : Nat := 1371668061084666705389857

theorem tailTrace_2671314 : CollatzResearch.WordTrace tailWord_2671314 prefixEnd_2671314 1371668061084666705389857 := by
  unfold tailWord_2671314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357706461073269238613249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64953883896195384636301997 24357706461073269238613249)
  ·
    refine ⟨18268279845804951928959937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24357706461073269238613249 18268279845804951928959937)
    ·
      refine ⟨13701209884353713946719953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18268279845804951928959937 13701209884353713946719953)
      ·
        refine ⟨10275907413265285460039965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13701209884353713946719953 10275907413265285460039965)
        ·
          refine ⟨3853465279974482047514987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10275907413265285460039965 3853465279974482047514987)
          ·
            refine ⟨5780197919961723071272481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853465279974482047514987 5780197919961723071272481)
            ·
              refine ⟨4335148439971292303454361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5780197919961723071272481 4335148439971292303454361)
              ·
                refine ⟨3251361329978469227590771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335148439971292303454361 3251361329978469227590771)
                ·
                  refine ⟨4877041994967703841386157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251361329978469227590771 4877041994967703841386157)
                  ·
                    refine ⟨1828890748112888940519809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4877041994967703841386157 1828890748112888940519809)
                    ·
                      refine ⟨1371668061084666705389857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1828890748112888940519809 1371668061084666705389857)
                      ·
                        rfl

theorem cell23_2671314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2671314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671314 prefixEnd_2671314 := by exact prefixLift 2671314
  have htrace : WordTrace (prefixWord ++ tailWord_2671314) baseStart_2671314 baseEnd_2671314 := by
    simpa [prefixWord, tailWord_2671314, baseEnd_2671314] using wordTrace_append hprefix tailTrace_2671314
  have hstable : (prefixWord ++ tailWord_2671314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671314).length < 2 ^ (prefixWord ++ tailWord_2671314).sum := by decide
  have hdescent : baseEnd_2671314 < baseStart_2671314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671400 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2671400 : Nat := 118140960795 + 2671400 * 2 ^ 59
def prefixEnd_2671400 : Nat := 4983230072969 + 3 ^ 40 * 2671400 * 2
def baseEnd_2671400 : Nat := 1371712220420953368914461

theorem tailTrace_2671400 : CollatzResearch.WordTrace tailWord_2671400 prefixEnd_2671400 1371712220420953368914461 := by
  unfold tailWord_2671400
  simp only [CollatzResearch.WordTrace]
  refine ⟨48716981260990756821041827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64955975014654342428055769 48716981260990756821041827)
  ·
    refine ⟨73075471891486135231562741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48716981260990756821041827 73075471891486135231562741)
    ·
      refine ⟨6850825489826825177959007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73075471891486135231562741 6850825489826825177959007)
      ·
        refine ⟨10276238234740237766938511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850825489826825177959007 10276238234740237766938511)
        ·
          refine ⟨15414357352110356650407767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10276238234740237766938511 15414357352110356650407767)
          ·
            refine ⟨23121536028165534975611651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15414357352110356650407767 23121536028165534975611651)
            ·
              refine ⟨34682304042248302463417477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23121536028165534975611651 34682304042248302463417477)
              ·
                refine ⟨6502932007921556711890777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34682304042248302463417477 6502932007921556711890777)
                ·
                  refine ⟨4877199005941167533918083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6502932007921556711890777 4877199005941167533918083)
                  ·
                    refine ⟨7315798508911751300877125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877199005941167533918083 7315798508911751300877125)
                    ·
                      refine ⟨1371712220420953368914461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7315798508911751300877125 1371712220420953368914461)
                      ·
                        rfl

theorem cell23_2671400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2671400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671400 prefixEnd_2671400 := by exact prefixLift 2671400
  have htrace : WordTrace (prefixWord ++ tailWord_2671400) baseStart_2671400 baseEnd_2671400 := by
    simpa [prefixWord, tailWord_2671400, baseEnd_2671400] using wordTrace_append hprefix tailTrace_2671400
  have hstable : (prefixWord ++ tailWord_2671400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671400).length < 2 ^ (prefixWord ++ tailWord_2671400).sum := by decide
  have hdescent : baseEnd_2671400 < baseStart_2671400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671410 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_2671410 : Nat := 118140960795 + 2671410 * 2 ^ 59
def prefixEnd_2671410 : Nat := 4983230072969 + 3 ^ 40 * 2671410 * 2
def baseEnd_2671410 : Nat := 457239118409166109929805

theorem tailTrace_2671410 : CollatzResearch.WordTrace tailWord_2671410 prefixEnd_2671410 457239118409166109929805 := by
  unfold tailWord_2671410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358581812986321337486921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64956218167963523566631789 24358581812986321337486921)
  ·
    refine ⟨18268936359739741003115191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24358581812986321337486921 18268936359739741003115191)
    ·
      refine ⟨27403404539609611504672787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18268936359739741003115191 27403404539609611504672787)
      ·
        refine ⟨41105106809414417257009181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27403404539609611504672787 41105106809414417257009181)
        ·
          refine ⟨15414415053530406471378443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41105106809414417257009181 15414415053530406471378443)
          ·
            refine ⟨23121622580295609707067665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15414415053530406471378443 23121622580295609707067665)
            ·
              refine ⟨17341216935221707280300749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23121622580295609707067665 17341216935221707280300749)
              ·
                refine ⟨6502956350708140230112781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17341216935221707280300749 6502956350708140230112781)
                ·
                  refine ⟨2438608631515552586292293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6502956350708140230112781 2438608631515552586292293)
                  ·
                    refine ⟨457239118409166109929805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438608631515552586292293 457239118409166109929805)
                    ·
                      rfl

theorem cell23_2671410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_2671410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671410 prefixEnd_2671410 := by exact prefixLift 2671410
  have htrace : WordTrace (prefixWord ++ tailWord_2671410) baseStart_2671410 baseEnd_2671410 := by
    simpa [prefixWord, tailWord_2671410, baseEnd_2671410] using wordTrace_append hprefix tailTrace_2671410
  have hstable : (prefixWord ++ tailWord_2671410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671410).length < 2 ^ (prefixWord ++ tailWord_2671410).sum := by decide
  have hdescent : baseEnd_2671410 < baseStart_2671410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671477 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2671477 : Nat := 118140960795 + 2671477 * 2 ^ 59
def prefixEnd_2671477 : Nat := 4983230072969 + 3 ^ 40 * 2671477 * 2
def baseEnd_2671477 : Nat := 1371751758431349567651607

theorem tailTrace_2671477 : CollatzResearch.WordTrace tailWord_2671477 prefixEnd_2671477 1371751758431349567651607 := by
  unfold tailWord_2671477
  simp only [CollatzResearch.WordTrace]
  refine ⟨97436770942702555792636685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64957847295135037195091123 97436770942702555792636685)
  ·
    refine ⟨36538789103513458422238757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97436770942702555792636685 36538789103513458422238757)
    ·
      refine ⟨6851022956908773454169767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36538789103513458422238757 6851022956908773454169767)
      ·
        refine ⟨10276534435363160181254651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6851022956908773454169767 10276534435363160181254651)
        ·
          refine ⟨15414801653044740271881977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10276534435363160181254651 15414801653044740271881977)
          ·
            refine ⟨11561101239783555203911483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15414801653044740271881977 11561101239783555203911483)
            ·
              refine ⟨17341651859675332805867225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11561101239783555203911483 17341651859675332805867225)
              ·
                refine ⟨13006238894756499604400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17341651859675332805867225 13006238894756499604400419)
                ·
                  refine ⟨19509358342134749406600629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13006238894756499604400419 19509358342134749406600629)
                  ·
                    refine ⟨1829002344575132756868809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19509358342134749406600629 1829002344575132756868809)
                    ·
                      refine ⟨1371751758431349567651607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829002344575132756868809 1371751758431349567651607)
                      ·
                        rfl

theorem cell23_2671477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2671477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671477 prefixEnd_2671477 := by exact prefixLift 2671477
  have htrace : WordTrace (prefixWord ++ tailWord_2671477) baseStart_2671477 baseEnd_2671477 := by
    simpa [prefixWord, tailWord_2671477, baseEnd_2671477] using wordTrace_append hprefix tailTrace_2671477
  have hstable : (prefixWord ++ tailWord_2671477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671477).length < 2 ^ (prefixWord ++ tailWord_2671477).sum := by decide
  have hdescent : baseEnd_2671477 < baseStart_2671477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671500 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_2671500 : Nat := 118140960795 + 2671500 * 2 ^ 59
def prefixEnd_2671500 : Nat := 4983230072969 + 3 ^ 40 * 2671500 * 2
def baseEnd_2671500 : Nat := 457254522828800992554667

theorem tailTrace_2671500 : CollatzResearch.WordTrace tailWord_2671500 prefixEnd_2671500 457254522828800992554667 := by
  unfold tailWord_2671500
  simp only [CollatzResearch.WordTrace]
  refine ⟨48718804910809615360361977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64958406547746153813815969 48718804910809615360361977)
  ·
    refine ⟨36539103683107211520271483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48718804910809615360361977 36539103683107211520271483)
    ·
      refine ⟨54808655524660817280407225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36539103683107211520271483 54808655524660817280407225)
      ·
        refine ⟨41106491643495612960305419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54808655524660817280407225 41106491643495612960305419)
        ·
          refine ⟨61659737465243419440458129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41106491643495612960305419 61659737465243419440458129)
          ·
            refine ⟨46244803098932564580343597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61659737465243419440458129 46244803098932564580343597)
            ·
              refine ⟨17341801162099711717628849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46244803098932564580343597 17341801162099711717628849)
              ·
                refine ⟨13006350871574783788221637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17341801162099711717628849 13006350871574783788221637)
                ·
                  refine ⟨2438690788420271960291557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13006350871574783788221637 2438690788420271960291557)
                  ·
                    refine ⟨457254522828800992554667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438690788420271960291557 457254522828800992554667)
                    ·
                      rfl

theorem cell23_2671500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_2671500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671500 prefixEnd_2671500 := by exact prefixLift 2671500
  have htrace : WordTrace (prefixWord ++ tailWord_2671500) baseStart_2671500 baseEnd_2671500 := by
    simpa [prefixWord, tailWord_2671500, baseEnd_2671500] using wordTrace_append hprefix tailTrace_2671500
  have hstable : (prefixWord ++ tailWord_2671500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671500).length < 2 ^ (prefixWord ++ tailWord_2671500).sum := by decide
  have hdescent : baseEnd_2671500 < baseStart_2671500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671517 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2671517 : Nat := 118140960795 + 2671517 * 2 ^ 59
def prefixEnd_2671517 : Nat := 4983230072969 + 3 ^ 40 * 2671517 * 2
def baseEnd_2671517 : Nat := 457257432552509803717141

theorem tailTrace_2671517 : CollatzResearch.WordTrace tailWord_2671517 prefixEnd_2671517 457257432552509803717141 := by
  unfold tailWord_2671517
  simp only [CollatzResearch.WordTrace]
  refine ⟨97438229862557642624092805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64958819908371761749395203 97438229862557642624092805)
  ·
    refine ⟨18269668099229557992017401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97438229862557642624092805 18269668099229557992017401)
    ·
      refine ⟨13702251074422168494013051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18269668099229557992017401 13702251074422168494013051)
      ·
        refine ⟨20553376611633252741019577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13702251074422168494013051 20553376611633252741019577)
        ·
          refine ⟨15415032458724939555764683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20553376611633252741019577 15415032458724939555764683)
          ·
            refine ⟨23122548688087409333647025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15415032458724939555764683 23122548688087409333647025)
            ·
              refine ⟨17341911516065557000235269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23122548688087409333647025 17341911516065557000235269)
              ·
                refine ⟨3251608409262291937544113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17341911516065557000235269 3251608409262291937544113)
                ·
                  refine ⟨2438706306946718953158085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3251608409262291937544113 2438706306946718953158085)
                  ·
                    refine ⟨457257432552509803717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438706306946718953158085 457257432552509803717141)
                    ·
                      rfl

theorem cell23_2671517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2671517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671517 prefixEnd_2671517 := by exact prefixLift 2671517
  have htrace : WordTrace (prefixWord ++ tailWord_2671517) baseStart_2671517 baseEnd_2671517 := by
    simpa [prefixWord, tailWord_2671517, baseEnd_2671517] using wordTrace_append hprefix tailTrace_2671517
  have hstable : (prefixWord ++ tailWord_2671517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671517).length < 2 ^ (prefixWord ++ tailWord_2671517).sum := by decide
  have hdescent : baseEnd_2671517 < baseStart_2671517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671544 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_2671544 : Nat := 118140960795 + 2671544 * 2 ^ 59
def prefixEnd_2671544 : Nat := 4983230072969 + 3 ^ 40 * 2671544 * 2
def baseEnd_2671544 : Nat := 1371786161635200805513799

theorem tailTrace_2671544 : CollatzResearch.WordTrace tailWord_2671544 prefixEnd_2671544 1371786161635200805513799 := by
  unfold tailWord_2671544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48719607316729913117662843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64959476422306550823550457 48719607316729913117662843)
  ·
    refine ⟨73079410975094869676494265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48719607316729913117662843 73079410975094869676494265)
    ·
      refine ⟨54809558231321152257370699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73079410975094869676494265 54809558231321152257370699)
      ·
        refine ⟨82214337346981728386056049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54809558231321152257370699 82214337346981728386056049)
        ·
          refine ⟨61660753010236296289542037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82214337346981728386056049 61660753010236296289542037)
          ·
            refine ⟨2890347797354826388572283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61660753010236296289542037 2890347797354826388572283)
            ·
              refine ⟨4335521696032239582858425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890347797354826388572283 4335521696032239582858425)
              ·
                refine ⟨3251641272024179687143819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335521696032239582858425 3251641272024179687143819)
                ·
                  refine ⟨4877461908036269530715729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251641272024179687143819 4877461908036269530715729)
                  ·
                    refine ⟨3658096431027202148036797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877461908036269530715729 3658096431027202148036797)
                    ·
                      refine ⟨1371786161635200805513799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658096431027202148036797 1371786161635200805513799)
                      ·
                        rfl

theorem cell23_2671544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_2671544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671544 prefixEnd_2671544 := by exact prefixLift 2671544
  have htrace : WordTrace (prefixWord ++ tailWord_2671544) baseStart_2671544 baseEnd_2671544 := by
    simpa [prefixWord, tailWord_2671544, baseEnd_2671544] using wordTrace_append hprefix tailTrace_2671544
  have hstable : (prefixWord ++ tailWord_2671544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671544).length < 2 ^ (prefixWord ++ tailWord_2671544).sum := by decide
  have hdescent : baseEnd_2671544 < baseStart_2671544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_2671600 : Nat := 118140960795 + 2671600 * 2 ^ 59
def prefixEnd_2671600 : Nat := 4983230072969 + 3 ^ 40 * 2671600 * 2
def baseEnd_2671600 : Nat := 1371814916551852586413541

theorem tailTrace_2671600 : CollatzResearch.WordTrace tailWord_2671600 prefixEnd_2671600 1371814916551852586413541 := by
  unfold tailWord_2671600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48720628560628473899682127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64960838080837965199576169 48720628560628473899682127)
  ·
    refine ⟨73080942840942710849523191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48720628560628473899682127 73080942840942710849523191)
    ·
      refine ⟨109621414261414066274284787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73080942840942710849523191 109621414261414066274284787)
      ·
        refine ⟨164432121392121099411427181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109621414261414066274284787 164432121392121099411427181)
        ·
          refine ⟨61662045522045412279285193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164432121392121099411427181 61662045522045412279285193)
          ·
            refine ⟨46246534141534059209463895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61662045522045412279285193 46246534141534059209463895)
            ·
              refine ⟨69369801212301088814195843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46246534141534059209463895 69369801212301088814195843)
              ·
                refine ⟨104054701818451633221293765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69369801212301088814195843 104054701818451633221293765)
                ·
                  refine ⟨19510256590959681228992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104054701818451633221293765 19510256590959681228992581)
                  ·
                    refine ⟨3658173110804940230436109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19510256590959681228992581 3658173110804940230436109)
                    ·
                      refine ⟨1371814916551852586413541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658173110804940230436109 1371814916551852586413541)
                      ·
                        rfl

theorem cell23_2671600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_2671600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671600 prefixEnd_2671600 := by exact prefixLift 2671600
  have htrace : WordTrace (prefixWord ++ tailWord_2671600) baseStart_2671600 baseEnd_2671600 := by
    simpa [prefixWord, tailWord_2671600, baseEnd_2671600] using wordTrace_append hprefix tailTrace_2671600
  have hstable : (prefixWord ++ tailWord_2671600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671600).length < 2 ^ (prefixWord ++ tailWord_2671600).sum := by decide
  have hdescent : baseEnd_2671600 < baseStart_2671600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671637 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 7]
def baseStart_2671637 : Nat := 118140960795 + 2671637 * 2 ^ 59
def prefixEnd_2671637 : Nat := 4983230072969 + 3 ^ 40 * 2671637 * 2
def baseEnd_2671637 : Nat := 152425990592896549072319

theorem tailTrace_2671637 : CollatzResearch.WordTrace tailWord_2671637 prefixEnd_2671637 152425990592896549072319 := by
  unfold tailWord_2671637
  simp only [CollatzResearch.WordTrace]
  refine ⟨97442606622122903118461165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64961737748081935412307443 97442606622122903118461165)
  ·
    refine ⟨36540977483296088669422937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97442606622122903118461165 36540977483296088669422937)
    ·
      refine ⟨27405733112472066502067203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36540977483296088669422937 27405733112472066502067203)
      ·
        refine ⟨41108599668708099753100805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27405733112472066502067203 41108599668708099753100805)
        ·
          refine ⟨7707862437882768703706401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41108599668708099753100805 7707862437882768703706401)
          ·
            refine ⟨5780896828412076527779801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7707862437882768703706401 5780896828412076527779801)
            ·
              refine ⟨4335672621309057395834851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5780896828412076527779801 4335672621309057395834851)
              ·
                refine ⟨6503508931963586093752277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335672621309057395834851 6503508931963586093752277)
                ·
                  refine ⟨152425990592896549072319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6503508931963586093752277 152425990592896549072319)
                  ·
                    rfl

theorem cell23_2671637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_2671637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671637 prefixEnd_2671637 := by exact prefixLift 2671637
  have htrace : WordTrace (prefixWord ++ tailWord_2671637) baseStart_2671637 baseEnd_2671637 := by
    simpa [prefixWord, tailWord_2671637, baseEnd_2671637] using wordTrace_append hprefix tailTrace_2671637
  have hstable : (prefixWord ++ tailWord_2671637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671637).length < 2 ^ (prefixWord ++ tailWord_2671637).sum := by decide
  have hdescent : baseEnd_2671637 < baseStart_2671637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671647 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_2671647 : Nat := 118140960795 + 2671647 * 2 ^ 59
def prefixEnd_2671647 : Nat := 4983230072969 + 3 ^ 40 * 2671647 * 2
def baseEnd_2671647 : Nat := 1371839050142613902525825

theorem tailTrace_2671647 : CollatzResearch.WordTrace tailWord_2671647 prefixEnd_2671647 1371839050142613902525825 := by
  unfold tailWord_2671647
  simp only [CollatzResearch.WordTrace]
  refine ⟨97442971352086674826325195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64961980901391116550883463 97442971352086674826325195)
  ·
    refine ⟨146164457028130012239487793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97442971352086674826325195 146164457028130012239487793)
    ·
      refine ⟨109623342771097509179615845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146164457028130012239487793 109623342771097509179615845)
      ·
        refine ⟨20554376769580782971177971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109623342771097509179615845 20554376769580782971177971)
        ·
          refine ⟨30831565154371174456766957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20554376769580782971177971 30831565154371174456766957)
          ·
            refine ⟨11561836932889190421287609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30831565154371174456766957 11561836932889190421287609)
            ·
              refine ⟨8671377699666892815965707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11561836932889190421287609 8671377699666892815965707)
              ·
                refine ⟨13007066549500339223948561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671377699666892815965707 13007066549500339223948561)
                ·
                  refine ⟨9755299912125254417961421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13007066549500339223948561 9755299912125254417961421)
                  ·
                    refine ⟨3658237467046970406735533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9755299912125254417961421 3658237467046970406735533)
                    ·
                      refine ⟨1371839050142613902525825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658237467046970406735533 1371839050142613902525825)
                      ·
                        rfl

theorem cell23_2671647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_2671647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671647 prefixEnd_2671647 := by exact prefixLift 2671647
  have htrace : WordTrace (prefixWord ++ tailWord_2671647) baseStart_2671647 baseEnd_2671647 := by
    simpa [prefixWord, tailWord_2671647, baseEnd_2671647] using wordTrace_append hprefix tailTrace_2671647
  have hstable : (prefixWord ++ tailWord_2671647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671647).length < 2 ^ (prefixWord ++ tailWord_2671647).sum := by decide
  have hdescent : baseEnd_2671647 < baseStart_2671647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671648 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2671648 : Nat := 118140960795 + 2671648 * 2 ^ 59
def prefixEnd_2671648 : Nat := 4983230072969 + 3 ^ 40 * 2671648 * 2
def baseEnd_2671648 : Nat := 1371839563623268398613321

theorem tailTrace_2671648 : CollatzResearch.WordTrace tailWord_2671648 prefixEnd_2671648 1371839563623268398613321 := by
  unfold tailWord_2671648
  simp only [CollatzResearch.WordTrace]
  refine ⟨48721503912541525998555799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64962005216722034664741065 48721503912541525998555799)
  ·
    refine ⟨73082255868812288997833699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48721503912541525998555799 73082255868812288997833699)
    ·
      refine ⟨109623383803218433496750549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73082255868812288997833699 109623383803218433496750549)
      ·
        refine ⟨2569298057887932035080091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 109623383803218433496750549 2569298057887932035080091)
        ·
          refine ⟨3853947086831898052620137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569298057887932035080091 3853947086831898052620137)
          ·
            refine ⟨2890460315123923539465103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3853947086831898052620137 2890460315123923539465103)
            ·
              refine ⟨4335690472685885309197655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890460315123923539465103 4335690472685885309197655)
              ·
                refine ⟨6503535709028827963796483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335690472685885309197655 6503535709028827963796483)
                ·
                  refine ⟨9755303563543241945694725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6503535709028827963796483 9755303563543241945694725)
                  ·
                    refine ⟨1829119418164357864817761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9755303563543241945694725 1829119418164357864817761)
                    ·
                      refine ⟨1371839563623268398613321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829119418164357864817761 1371839563623268398613321)
                      ·
                        rfl

theorem cell23_2671648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2671648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671648 prefixEnd_2671648 := by exact prefixLift 2671648
  have htrace : WordTrace (prefixWord ++ tailWord_2671648) baseStart_2671648 baseEnd_2671648 := by
    simpa [prefixWord, tailWord_2671648, baseEnd_2671648] using wordTrace_append hprefix tailTrace_2671648
  have hstable : (prefixWord ++ tailWord_2671648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671648).length < 2 ^ (prefixWord ++ tailWord_2671648).sum := by decide
  have hdescent : baseEnd_2671648 < baseStart_2671648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671687 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2671687 : Nat := 118140960795 + 2671687 * 2 ^ 59
def prefixEnd_2671687 : Nat := 4983230072969 + 3 ^ 40 * 2671687 * 2
def baseEnd_2671687 : Nat := 1371859589368793746025641

theorem tailTrace_2671687 : CollatzResearch.WordTrace tailWord_2671687 prefixEnd_2671687 1371859589368793746025641 := by
  unfold tailWord_2671687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97444430271941761657781315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64962953514627841105187543 97444430271941761657781315)
  ·
    refine ⟨146166645407912642486671973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97444430271941761657781315 146166645407912642486671973)
    ·
      refine ⟨27406246013983620466250995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146166645407912642486671973 27406246013983620466250995)
      ·
        refine ⟨41109369020975430699376493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27406246013983620466250995 41109369020975430699376493)
        ·
          refine ⟨15416013382865786512266185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41109369020975430699376493 15416013382865786512266185)
          ·
            refine ⟨11562010037149339884199639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416013382865786512266185 11562010037149339884199639)
            ·
              refine ⟨17343015055724009826299459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11562010037149339884199639 17343015055724009826299459)
              ·
                refine ⟨26014522583586014739449189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17343015055724009826299459 26014522583586014739449189)
                ·
                  refine ⟨4877722984422377763646723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26014522583586014739449189 4877722984422377763646723)
                  ·
                    refine ⟨7316584476633566645470085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4877722984422377763646723 7316584476633566645470085)
                    ·
                      refine ⟨1371859589368793746025641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7316584476633566645470085 1371859589368793746025641)
                      ·
                        rfl

theorem cell23_2671687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2671687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671687 prefixEnd_2671687 := by exact prefixLift 2671687
  have htrace : WordTrace (prefixWord ++ tailWord_2671687) baseStart_2671687 baseEnd_2671687 := by
    simpa [prefixWord, tailWord_2671687, baseEnd_2671687] using wordTrace_append hprefix tailTrace_2671687
  have hstable : (prefixWord ++ tailWord_2671687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671687).length < 2 ^ (prefixWord ++ tailWord_2671687).sum := by decide
  have hdescent : baseEnd_2671687 < baseStart_2671687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671724 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2671724 : Nat := 118140960795 + 2671724 * 2 ^ 59
def prefixEnd_2671724 : Nat := 4983230072969 + 3 ^ 40 * 2671724 * 2
def baseEnd_2671724 : Nat := 1371878588153010101262971

theorem tailTrace_2671724 : CollatzResearch.WordTrace tailWord_2671724 prefixEnd_2671724 1371878588153010101262971 := by
  unfold tailWord_2671724
  simp only [CollatzResearch.WordTrace]
  refine ⟨48722889886403858488439113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64963853181871811317918817 48722889886403858488439113)
  ·
    refine ⟨36542167414802893866329335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48722889886403858488439113 36542167414802893866329335)
    ·
      refine ⟨54813251122204340799494003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36542167414802893866329335 54813251122204340799494003)
      ·
        refine ⟨82219876683306511199241005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54813251122204340799494003 82219876683306511199241005)
        ·
          refine ⟨30832453756239941699715377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82219876683306511199241005 30832453756239941699715377)
          ·
            refine ⟨23124340317179956274786533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30832453756239941699715377 23124340317179956274786533)
            ·
              refine ⟨4335813809471241801522475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23124340317179956274786533 4335813809471241801522475)
              ·
                refine ⟨6503720714206862702283713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335813809471241801522475 6503720714206862702283713)
                ·
                  refine ⟨4877790535655147026712785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6503720714206862702283713 4877790535655147026712785)
                  ·
                    refine ⟨3658342901741360270034589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4877790535655147026712785 3658342901741360270034589)
                    ·
                      refine ⟨1371878588153010101262971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658342901741360270034589 1371878588153010101262971)
                      ·
                        rfl

theorem cell23_2671724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2671724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671724 prefixEnd_2671724 := by exact prefixLift 2671724
  have htrace : WordTrace (prefixWord ++ tailWord_2671724) baseStart_2671724 baseEnd_2671724 := by
    simpa [prefixWord, tailWord_2671724, baseEnd_2671724] using wordTrace_append hprefix tailTrace_2671724
  have hstable : (prefixWord ++ tailWord_2671724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671724).length < 2 ^ (prefixWord ++ tailWord_2671724).sum := by decide
  have hdescent : baseEnd_2671724 < baseStart_2671724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671748 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_2671748 : Nat := 118140960795 + 2671748 * 2 ^ 59
def prefixEnd_2671748 : Nat := 4983230072969 + 3 ^ 40 * 2671748 * 2
def baseEnd_2671748 : Nat := 457296970562906002454287

theorem tailTrace_2671748 : CollatzResearch.WordTrace tailWord_2671748 prefixEnd_2671748 457296970562906002454287 := by
  unfold tailWord_2671748
  simp only [CollatzResearch.WordTrace]
  refine ⟨48723327562360384537875949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64964436749813846050501265 48723327562360384537875949)
  ·
    refine ⟨18271247835885144201703481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48723327562360384537875949 18271247835885144201703481)
    ·
      refine ⟨13703435876913858151277611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18271247835885144201703481 13703435876913858151277611)
      ·
        refine ⟨20555153815370787226916417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703435876913858151277611 20555153815370787226916417)
        ·
          refine ⟨15416365361528090420187313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20555153815370787226916417 15416365361528090420187313)
          ·
            refine ⟨11562274021146067815140485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416365361528090420187313 11562274021146067815140485)
            ·
              refine ⟨2167926378964887715338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11562274021146067815140485 2167926378964887715338841)
              ·
                refine ⟨1625944784223665786504131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167926378964887715338841 1625944784223665786504131)
                ·
                  refine ⟨2438917176335498679756197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625944784223665786504131 2438917176335498679756197)
                  ·
                    refine ⟨457296970562906002454287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2438917176335498679756197 457296970562906002454287)
                    ·
                      rfl

theorem cell23_2671748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_2671748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671748 prefixEnd_2671748 := by exact prefixLift 2671748
  have htrace : WordTrace (prefixWord ++ tailWord_2671748) baseStart_2671748 baseEnd_2671748 := by
    simpa [prefixWord, tailWord_2671748, baseEnd_2671748] using wordTrace_append hprefix tailTrace_2671748
  have hstable : (prefixWord ++ tailWord_2671748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671748).length < 2 ^ (prefixWord ++ tailWord_2671748).sum := by decide
  have hdescent : baseEnd_2671748 < baseStart_2671748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671781 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_2671781 : Nat := 118140960795 + 2671781 * 2 ^ 59
def prefixEnd_2671781 : Nat := 4983230072969 + 3 ^ 40 * 2671781 * 2
def baseEnd_2671781 : Nat := 1371907856550316378250209

theorem tailTrace_2671781 : CollatzResearch.WordTrace tailWord_2671781 prefixEnd_2671781 1371907856550316378250209 := by
  unfold tailWord_2671781
  simp only [CollatzResearch.WordTrace]
  refine ⟨97447858733601215711703197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64965239155734143807802131 97447858733601215711703197)
  ·
    refine ⟨36542947025100455891888699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97447858733601215711703197 36542947025100455891888699)
    ·
      refine ⟨54814420537650683837833049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36542947025100455891888699 54814420537650683837833049)
      ·
        refine ⟨41110815403238012878374787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54814420537650683837833049 41110815403238012878374787)
        ·
          refine ⟨61666223104857019317562181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41110815403238012878374787 61666223104857019317562181)
          ·
            refine ⟨11562416832160691122042909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61666223104857019317562181 11562416832160691122042909)
            ·
              refine ⟨4335906312060259170766091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11562416832160691122042909 4335906312060259170766091)
              ·
                refine ⟨6503859468090388756149137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335906312060259170766091 6503859468090388756149137)
                ·
                  refine ⟨4877894601067791567111853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6503859468090388756149137 4877894601067791567111853)
                  ·
                    refine ⟨1829210475400421837666945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4877894601067791567111853 1829210475400421837666945)
                    ·
                      refine ⟨1371907856550316378250209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829210475400421837666945 1371907856550316378250209)
                      ·
                        rfl

theorem cell23_2671781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_2671781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671781 prefixEnd_2671781 := by exact prefixLift 2671781
  have htrace : WordTrace (prefixWord ++ tailWord_2671781) baseStart_2671781 baseEnd_2671781 := by
    simpa [prefixWord, tailWord_2671781, baseEnd_2671781] using wordTrace_append hprefix tailTrace_2671781
  have hstable : (prefixWord ++ tailWord_2671781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671781).length < 2 ^ (prefixWord ++ tailWord_2671781).sum := by decide
  have hdescent : baseEnd_2671781 < baseStart_2671781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671807 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2671807 : Nat := 118140960795 + 2671807 * 2 ^ 59
def prefixEnd_2671807 : Nat := 4983230072969 + 3 ^ 40 * 2671807 * 2
def baseEnd_2671807 : Nat := 1371921207047333276525089

theorem tailTrace_2671807 : CollatzResearch.WordTrace tailWord_2671807 prefixEnd_2671807 1371921207047333276525089 := by
  unfold tailWord_2671807
  simp only [CollatzResearch.WordTrace]
  refine ⟨97448807031507022152149675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64965871354338014768099783 97448807031507022152149675)
  ·
    refine ⟨146173210547260533228224513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97448807031507022152149675 146173210547260533228224513)
    ·
      refine ⟨109629907910445399921168385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146173210547260533228224513 109629907910445399921168385)
      ·
        refine ⟨82222430932834049940876289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109629907910445399921168385 82222430932834049940876289)
        ·
          refine ⟨61666823199625537455657217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82222430932834049940876289 61666823199625537455657217)
          ·
            refine ⟨46250117399719153091742913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61666823199625537455657217 46250117399719153091742913)
            ·
              refine ⟨34687588049789364818807185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46250117399719153091742913 34687588049789364818807185)
              ·
                refine ⟨26015691037342023614105389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34687588049789364818807185 26015691037342023614105389)
                ·
                  refine ⟨9755884139003258855289521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26015691037342023614105389 9755884139003258855289521)
                  ·
                    refine ⟨7316913104252444141467141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9755884139003258855289521 7316913104252444141467141)
                    ·
                      refine ⟨1371921207047333276525089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7316913104252444141467141 1371921207047333276525089)
                      ·
                        rfl

theorem cell23_2671807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2671807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671807 prefixEnd_2671807 := by exact prefixLift 2671807
  have htrace : WordTrace (prefixWord ++ tailWord_2671807) baseStart_2671807 baseEnd_2671807 := by
    simpa [prefixWord, tailWord_2671807, baseEnd_2671807] using wordTrace_append hprefix tailTrace_2671807
  have hstable : (prefixWord ++ tailWord_2671807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671807).length < 2 ^ (prefixWord ++ tailWord_2671807).sum := by decide
  have hdescent : baseEnd_2671807 < baseStart_2671807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671844 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_2671844 : Nat := 118140960795 + 2671844 * 2 ^ 59
def prefixEnd_2671844 : Nat := 4983230072969 + 3 ^ 40 * 2671844 * 2
def baseEnd_2671844 : Nat := 1371940205831549631762419

theorem tailTrace_2671844 : CollatzResearch.WordTrace tailWord_2671844 prefixEnd_2671844 1371940205831549631762419 := by
  unfold tailWord_2671844
  simp only [CollatzResearch.WordTrace]
  refine ⟨48725078266186488735623293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64966771021581984980831057 48725078266186488735623293)
  ·
    refine ⟨18271904349819933275858735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48725078266186488735623293 18271904349819933275858735)
    ·
      refine ⟨27407856524729899913788103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18271904349819933275858735 27407856524729899913788103)
      ·
        refine ⟨41111784787094849870682155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27407856524729899913788103 41111784787094849870682155)
        ·
          refine ⟨61667677180642274806023233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41111784787094849870682155 61667677180642274806023233)
          ·
            refine ⟨46250757885481706104517425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61667677180642274806023233 46250757885481706104517425)
            ·
              refine ⟨34688068414111279578388069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46250757885481706104517425 34688068414111279578388069)
              ·
                refine ⟨6504012827645864920947763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34688068414111279578388069 6504012827645864920947763)
                ·
                  refine ⟨9756019241468797381421645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504012827645864920947763 9756019241468797381421645)
                  ·
                    refine ⟨3658507215550799018033117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9756019241468797381421645 3658507215550799018033117)
                    ·
                      refine ⟨1371940205831549631762419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658507215550799018033117 1371940205831549631762419)
                      ·
                        rfl

theorem cell23_2671844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_2671844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671844 prefixEnd_2671844 := by exact prefixLift 2671844
  have htrace : WordTrace (prefixWord ++ tailWord_2671844) baseStart_2671844 baseEnd_2671844 := by
    simpa [prefixWord, tailWord_2671844, baseEnd_2671844] using wordTrace_append hprefix tailTrace_2671844
  have hstable : (prefixWord ++ tailWord_2671844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671844).length < 2 ^ (prefixWord ++ tailWord_2671844).sum := by decide
  have hdescent : baseEnd_2671844 < baseStart_2671844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671857 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2671857 : Nat := 118140960795 + 2671857 * 2 ^ 59
def prefixEnd_2671857 : Nat := 4983230072969 + 3 ^ 40 * 2671857 * 2
def baseEnd_2671857 : Nat := 1371946881080058080899859

theorem tailTrace_2671857 : CollatzResearch.WordTrace tailWord_2671857 prefixEnd_2671857 1371946881080058080899859 := by
  unfold tailWord_2671857
  simp only [CollatzResearch.WordTrace]
  refine ⟨97450630681325880691469825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64967087120883920460979883 97450630681325880691469825)
  ·
    refine ⟨73087973010994410518602369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97450630681325880691469825 73087973010994410518602369)
    ·
      refine ⟨54815979758245807888951777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73087973010994410518602369 54815979758245807888951777)
      ·
        refine ⟨41111984818684355916713833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54815979758245807888951777 41111984818684355916713833)
        ·
          refine ⟨30833988614013266937535375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41111984818684355916713833 30833988614013266937535375)
          ·
            refine ⟨46250982921019900406303063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30833988614013266937535375 46250982921019900406303063)
            ·
              refine ⟨69376474381529850609454595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46250982921019900406303063 69376474381529850609454595)
              ·
                refine ⟨104064711572294775914181893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69376474381529850609454595 104064711572294775914181893)
                ·
                  refine ⟨19512133419805270483909105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104064711572294775914181893 19512133419805270483909105)
                  ·
                    refine ⟨14634100064853952862931829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19512133419805270483909105 14634100064853952862931829)
                    ·
                      refine ⟨1371946881080058080899859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14634100064853952862931829 1371946881080058080899859)
                      ·
                        rfl

theorem cell23_2671857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2671857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671857 prefixEnd_2671857 := by exact prefixLift 2671857
  have htrace : WordTrace (prefixWord ++ tailWord_2671857) baseStart_2671857 baseEnd_2671857 := by
    simpa [prefixWord, tailWord_2671857, baseEnd_2671857] using wordTrace_append hprefix tailTrace_2671857
  have hstable : (prefixWord ++ tailWord_2671857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671857).length < 2 ^ (prefixWord ++ tailWord_2671857).sum := by decide
  have hdescent : baseEnd_2671857 < baseStart_2671857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671877 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2671877 : Nat := 118140960795 + 2671877 * 2 ^ 59
def prefixEnd_2671877 : Nat := 4983230072969 + 3 ^ 40 * 2671877 * 2
def baseEnd_2671877 : Nat := 457319050231049334216589

theorem tailTrace_2671877 : CollatzResearch.WordTrace tailWord_2671877 prefixEnd_2671877 457319050231049334216589 := by
  unfold tailWord_2671877
  simp only [CollatzResearch.WordTrace]
  refine ⟨97451360141253424107197885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64967573427502282738131923 97451360141253424107197885)
  ·
    refine ⟨36544260052970034040199207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97451360141253424107197885 36544260052970034040199207)
    ·
      refine ⟨54816390079455051060298811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36544260052970034040199207 54816390079455051060298811)
      ·
        refine ⟨82224585119182576590448217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54816390079455051060298811 82224585119182576590448217)
        ·
          refine ⟨61668438839386932442836163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82224585119182576590448217 61668438839386932442836163)
          ·
            refine ⟨92502658259080398664254245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61668438839386932442836163 92502658259080398664254245)
            ·
              refine ⟨17344248423577574749547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92502658259080398664254245 17344248423577574749547671)
              ·
                refine ⟨26016372635366362124321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17344248423577574749547671 26016372635366362124321507)
                ·
                  refine ⟨39024558953049543186482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26016372635366362124321507 39024558953049543186482261)
                  ·
                    refine ⟨457319050231049334216589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39024558953049543186482261 457319050231049334216589)
                    ·
                      rfl

theorem cell23_2671877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2671877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671877 prefixEnd_2671877 := by exact prefixLift 2671877
  have htrace : WordTrace (prefixWord ++ tailWord_2671877) baseStart_2671877 baseEnd_2671877 := by
    simpa [prefixWord, tailWord_2671877, baseEnd_2671877] using wordTrace_append hprefix tailTrace_2671877
  have hstable : (prefixWord ++ tailWord_2671877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671877).length < 2 ^ (prefixWord ++ tailWord_2671877).sum := by decide
  have hdescent : baseEnd_2671877 < baseStart_2671877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671927 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2671927 : Nat := 118140960795 + 2671927 * 2 ^ 59
def prefixEnd_2671927 : Nat := 4983230072969 + 3 ^ 40 * 2671927 * 2
def baseEnd_2671927 : Nat := 1371982824725872807024537

theorem tailTrace_2671927 : CollatzResearch.WordTrace tailWord_2671927 prefixEnd_2671927 1371982824725872807024537 := by
  unfold tailWord_2671927
  simp only [CollatzResearch.WordTrace]
  refine ⟨97453183791072282646518035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64968789194048188431012023 97453183791072282646518035)
  ·
    refine ⟨146179775686608423969777053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97453183791072282646518035 146179775686608423969777053)
    ·
      refine ⟨54817415882478158988666395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146179775686608423969777053 54817415882478158988666395)
      ·
        refine ⟨82226123823717238482999593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54817415882478158988666395 82226123823717238482999593)
        ·
          refine ⟨61669592867787928862249695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82226123823717238482999593 61669592867787928862249695)
          ·
            refine ⟨92504389301681893293374543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61669592867787928862249695 92504389301681893293374543)
            ·
              refine ⟨138756583952522839940061815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92504389301681893293374543 138756583952522839940061815)
              ·
                refine ⟨208134875928784259910092723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138756583952522839940061815 208134875928784259910092723)
                ·
                  refine ⟨312202313893176389865139085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208134875928784259910092723 312202313893176389865139085)
                  ·
                    refine ⟨117075867709941146199427157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312202313893176389865139085 117075867709941146199427157)
                    ·
                      refine ⟨1371982824725872807024537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117075867709941146199427157 1371982824725872807024537)
                      ·
                        rfl

theorem cell23_2671927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2671927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671927 prefixEnd_2671927 := by exact prefixLift 2671927
  have htrace : WordTrace (prefixWord ++ tailWord_2671927) baseStart_2671927 baseEnd_2671927 := by
    simpa [prefixWord, tailWord_2671927, baseEnd_2671927] using wordTrace_append hprefix tailTrace_2671927
  have hstable : (prefixWord ++ tailWord_2671927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671927).length < 2 ^ (prefixWord ++ tailWord_2671927).sum := by decide
  have hdescent : baseEnd_2671927 < baseStart_2671927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2671991 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_2671991 : Nat := 118140960795 + 2671991 * 2 ^ 59
def prefixEnd_2671991 : Nat := 4983230072969 + 3 ^ 40 * 2671991 * 2
def baseEnd_2671991 : Nat := 1372015687487760556624243

theorem tailTrace_2671991 : CollatzResearch.WordTrace tailWord_2671991 prefixEnd_2671991 1372015687487760556624243 := by
  unfold tailWord_2671991
  simp only [CollatzResearch.WordTrace]
  refine ⟨97455518062840421576847827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64970345375226947717898551 97455518062840421576847827)
  ·
    refine ⟨146183277094260632365271741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97455518062840421576847827 146183277094260632365271741)
    ·
      refine ⟨54818728910347737136976903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146183277094260632365271741 54818728910347737136976903)
      ·
        refine ⟨82228093365521605705465355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54818728910347737136976903 82228093365521605705465355)
        ·
          refine ⟨123342140048282408558198033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82228093365521605705465355 123342140048282408558198033)
          ·
            refine ⟨92506605036211806418648525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123342140048282408558198033 92506605036211806418648525)
            ·
              refine ⟨34689976888579427406993197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92506605036211806418648525 34689976888579427406993197)
              ·
                refine ⟨13008741333217285277622449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34689976888579427406993197 13008741333217285277622449)
                ·
                  refine ⟨9756555999912963958216837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13008741333217285277622449 9756555999912963958216837)
                  ·
                    refine ⟨1829354249983680742165657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9756555999912963958216837 1829354249983680742165657)
                    ·
                      refine ⟨1372015687487760556624243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829354249983680742165657 1372015687487760556624243)
                      ·
                        rfl

theorem cell23_2671991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_2671991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2671991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2671991 prefixEnd_2671991 := by exact prefixLift 2671991
  have htrace : WordTrace (prefixWord ++ tailWord_2671991) baseStart_2671991 baseEnd_2671991 := by
    simpa [prefixWord, tailWord_2671991, baseEnd_2671991] using wordTrace_append hprefix tailTrace_2671991
  have hstable : (prefixWord ++ tailWord_2671991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2671991).length < 2 ^ (prefixWord ++ tailWord_2671991).sum := by decide
  have hdescent : baseEnd_2671991 < baseStart_2671991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2671991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672011 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3]
def baseStart_2672011 : Nat := 118140960795 + 2672011 * 2 ^ 59
def prefixEnd_2672011 : Nat := 4983230072969 + 3 ^ 40 * 2672011 * 2
def baseEnd_2672011 : Nat := 1372025957100850478374151

theorem tailTrace_2672011 : CollatzResearch.WordTrace tailWord_2672011 prefixEnd_2672011 1372025957100850478374151 := by
  unfold tailWord_2672011
  simp only [CollatzResearch.WordTrace]
  refine ⟨97456247522767964992575887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64970831681845309995050591 97456247522767964992575887)
  ·
    refine ⟨146184371284151947488863831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97456247522767964992575887 146184371284151947488863831)
    ·
      refine ⟨219276556926227921233295747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146184371284151947488863831 219276556926227921233295747)
      ·
        refine ⟨328914835389341881849943621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219276556926227921233295747 328914835389341881849943621)
        ·
          refine ⟨61671531635501602846864429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 328914835389341881849943621 61671531635501602846864429)
          ·
            refine ⟨23126824363313101067574161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61671531635501602846864429 23126824363313101067574161)
            ·
              refine ⟨17345118272484825800680621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23126824363313101067574161 17345118272484825800680621)
              ·
                refine ⟨6504419352181809675255233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17345118272484825800680621 6504419352181809675255233)
                ·
                  refine ⟨4878314514136357256441425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504419352181809675255233 4878314514136357256441425)
                  ·
                    refine ⟨3658735885602267942331069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878314514136357256441425 3658735885602267942331069)
                    ·
                      refine ⟨1372025957100850478374151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658735885602267942331069 1372025957100850478374151)
                      ·
                        rfl

theorem cell23_2672011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].length) (baseStart_2672011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672011 prefixEnd_2672011 := by exact prefixLift 2672011
  have htrace : WordTrace (prefixWord ++ tailWord_2672011) baseStart_2672011 baseEnd_2672011 := by
    simpa [prefixWord, tailWord_2672011, baseEnd_2672011] using wordTrace_append hprefix tailTrace_2672011
  have hstable : (prefixWord ++ tailWord_2672011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672011).length < 2 ^ (prefixWord ++ tailWord_2672011).sum := by decide
  have hdescent : baseEnd_2672011 < baseStart_2672011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672035 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 1, 4]
def baseStart_2672035 : Nat := 118140960795 + 2672035 * 2 ^ 59
def prefixEnd_2672035 : Nat := 4983230072969 + 3 ^ 40 * 2672035 * 2
def baseEnd_2672035 : Nat := 457346093545519461491347

theorem tailTrace_2672035 : CollatzResearch.WordTrace tailWord_2672035 prefixEnd_2672035 457346093545519461491347 := by
  unfold tailWord_2672035
  simp only [CollatzResearch.WordTrace]
  refine ⟨97457122874681017091449559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64971415249787344727633039 97457122874681017091449559)
  ·
    refine ⟨146185684312021525637174339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97457122874681017091449559 146185684312021525637174339)
    ·
      refine ⟨219278526468032288455761509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146185684312021525637174339 219278526468032288455761509)
      ·
        refine ⟨41114723712756054085455283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219278526468032288455761509 41114723712756054085455283)
        ·
          refine ⟨61672085569134081128182925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41114723712756054085455283 61672085569134081128182925)
          ·
            refine ⟨23127032088425280423068597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61672085569134081128182925 23127032088425280423068597)
            ·
              refine ⟨2168159258289870039662681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23127032088425280423068597 2168159258289870039662681)
              ·
                refine ⟨1626119443717402529747011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168159258289870039662681 1626119443717402529747011)
                ·
                  refine ⟨2439179165576103794620517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626119443717402529747011 2439179165576103794620517)
                  ·
                    refine ⟨457346093545519461491347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439179165576103794620517 457346093545519461491347)
                    ·
                      rfl

theorem cell23_2672035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 4].length) (baseStart_2672035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672035 prefixEnd_2672035 := by exact prefixLift 2672035
  have htrace : WordTrace (prefixWord ++ tailWord_2672035) baseStart_2672035 baseEnd_2672035 := by
    simpa [prefixWord, tailWord_2672035, baseEnd_2672035] using wordTrace_append hprefix tailTrace_2672035
  have hstable : (prefixWord ++ tailWord_2672035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672035).length < 2 ^ (prefixWord ++ tailWord_2672035).sum := by decide
  have hdescent : baseEnd_2672035 < baseStart_2672035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672051 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 5, 2]
def baseStart_2672051 : Nat := 118140960795 + 2672051 * 2 ^ 59
def prefixEnd_2672051 : Nat := 4983230072969 + 3 ^ 40 * 2672051 * 2
def baseEnd_2672051 : Nat := 1372046496327030321873967

theorem tailTrace_2672051 : CollatzResearch.WordTrace tailWord_2672051 prefixEnd_2672051 1372046496327030321873967 := by
  unfold tailWord_2672051
  simp only [CollatzResearch.WordTrace]
  refine ⟨97457706442623051824032007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64971804295082034549354671 97457706442623051824032007)
  ·
    refine ⟨146186559663934577736048011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97457706442623051824032007 146186559663934577736048011)
    ·
      refine ⟨219279839495901866604072017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146186559663934577736048011 219279839495901866604072017)
      ·
        refine ⟨164459879621926399953054013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219279839495901866604072017 164459879621926399953054013)
        ·
          refine ⟨61672454858222399982395255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164459879621926399953054013 61672454858222399982395255)
          ·
            refine ⟨92508682287333599973592883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61672454858222399982395255 92508682287333599973592883)
            ·
              refine ⟨138763023431000399960389325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92508682287333599973592883 138763023431000399960389325)
              ·
                refine ⟨52036133786625149985145997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138763023431000399960389325 52036133786625149985145997)
                ·
                  refine ⟨19513550169984431244429749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52036133786625149985145997 19513550169984431244429749)
                  ·
                    refine ⟨1829395328436040429165289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19513550169984431244429749 1829395328436040429165289)
                    ·
                      refine ⟨1372046496327030321873967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829395328436040429165289 1372046496327030321873967)
                      ·
                        rfl

theorem cell23_2672051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5, 2].length) (baseStart_2672051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672051 prefixEnd_2672051 := by exact prefixLift 2672051
  have htrace : WordTrace (prefixWord ++ tailWord_2672051) baseStart_2672051 baseEnd_2672051 := by
    simpa [prefixWord, tailWord_2672051, baseEnd_2672051] using wordTrace_append hprefix tailTrace_2672051
  have hstable : (prefixWord ++ tailWord_2672051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672051).length < 2 ^ (prefixWord ++ tailWord_2672051).sum := by decide
  have hdescent : baseEnd_2672051 < baseStart_2672051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672061 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2672061 : Nat := 118140960795 + 2672061 * 2 ^ 59
def prefixEnd_2672061 : Nat := 4983230072969 + 3 ^ 40 * 2672061 * 2
def baseEnd_2672061 : Nat := 457350543711191760916307

theorem tailTrace_2672061 : CollatzResearch.WordTrace tailWord_2672061 prefixEnd_2672061 457350543711191760916307 := by
  unfold tailWord_2672061
  simp only [CollatzResearch.WordTrace]
  refine ⟨97458071172586823531896037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64972047448391215687930691 97458071172586823531896037)
  ·
    refine ⟨18273388344860029412230507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97458071172586823531896037 18273388344860029412230507)
    ·
      refine ⟨27410082517290044118345761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273388344860029412230507 27410082517290044118345761)
      ·
        refine ⟨20557561887967533088759321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27410082517290044118345761 20557561887967533088759321)
        ·
          refine ⟨15418171415975649816569491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20557561887967533088759321 15418171415975649816569491)
          ·
            refine ⟨23127257123963474724854237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15418171415975649816569491 23127257123963474724854237)
            ·
              refine ⟨8672721421486303021820339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23127257123963474724854237 8672721421486303021820339)
              ·
                refine ⟨13009082132229454532730509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672721421486303021820339 13009082132229454532730509)
                ·
                  refine ⟨4878405799586045449773941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13009082132229454532730509 4878405799586045449773941)
                  ·
                    refine ⟨457350543711191760916307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4878405799586045449773941 457350543711191760916307)
                    ·
                      rfl

theorem cell23_2672061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2672061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672061 prefixEnd_2672061 := by exact prefixLift 2672061
  have htrace : WordTrace (prefixWord ++ tailWord_2672061) baseStart_2672061 baseEnd_2672061 := by
    simpa [prefixWord, tailWord_2672061, baseEnd_2672061] using wordTrace_append hprefix tailTrace_2672061
  have hstable : (prefixWord ++ tailWord_2672061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672061).length < 2 ^ (prefixWord ++ tailWord_2672061).sum := by decide
  have hdescent : baseEnd_2672061 < baseStart_2672061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672111 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_2672111 : Nat := 118140960795 + 2672111 * 2 ^ 59
def prefixEnd_2672111 : Nat := 4983230072969 + 3 ^ 40 * 2672111 * 2
def baseEnd_2672111 : Nat := 1372077305166300087123691

theorem tailTrace_2672111 : CollatzResearch.WordTrace tailWord_2672111 prefixEnd_2672111 1372077305166300087123691 := by
  unfold tailWord_2672111
  simp only [CollatzResearch.WordTrace]
  refine ⟨97459894822405682071216187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64973263214937121380810791 97459894822405682071216187)
  ·
    refine ⟨146189842233608523106824281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97459894822405682071216187 146189842233608523106824281)
    ·
      refine ⟨109642381675206392330118211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146189842233608523106824281 109642381675206392330118211)
      ·
        refine ⟨164463572512809588495177317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109642381675206392330118211 164463572512809588495177317)
        ·
          refine ⟨30836919846151797842845747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164463572512809588495177317 30836919846151797842845747)
          ·
            refine ⟨46255379769227696764268621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30836919846151797842845747 46255379769227696764268621)
            ·
              refine ⟨17345767413460386286600733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46255379769227696764268621 17345767413460386286600733)
              ·
                refine ⟨6504662780047644857475275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17345767413460386286600733 6504662780047644857475275)
                ·
                  refine ⟨9756994170071467286212913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504662780047644857475275 9756994170071467286212913)
                  ·
                    refine ⟨7317745627553600464659685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9756994170071467286212913 7317745627553600464659685)
                    ·
                      refine ⟨1372077305166300087123691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7317745627553600464659685 1372077305166300087123691)
                      ·
                        rfl

theorem cell23_2672111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_2672111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672111 prefixEnd_2672111 := by exact prefixLift 2672111
  have htrace : WordTrace (prefixWord ++ tailWord_2672111) baseStart_2672111 baseEnd_2672111 := by
    simpa [prefixWord, tailWord_2672111, baseEnd_2672111] using wordTrace_append hprefix tailTrace_2672111
  have hstable : (prefixWord ++ tailWord_2672111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672111).length < 2 ^ (prefixWord ++ tailWord_2672111).sum := by decide
  have hdescent : baseEnd_2672111 < baseStart_2672111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672126 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2672126 : Nat := 118140960795 + 2672126 * 2 ^ 59
def prefixEnd_2672126 : Nat := 4983230072969 + 3 ^ 40 * 2672126 * 2
def baseEnd_2672126 : Nat := 1372085007376117528436123

theorem tailTrace_2672126 : CollatzResearch.WordTrace tailWord_2672126 prefixEnd_2672126 1372085007376117528436123 := by
  unfold tailWord_2672126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182555239668917454126529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64973627944900893088674821 12182555239668917454126529)
  ·
    refine ⟨9136916429751688090594897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12182555239668917454126529 9136916429751688090594897)
    ·
      refine ⟨6852687322313766067946173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9136916429751688090594897 6852687322313766067946173)
      ·
        refine ⟨2569757745867662275479815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6852687322313766067946173 2569757745867662275479815)
        ·
          refine ⟨3854636618801493413219723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569757745867662275479815 3854636618801493413219723)
          ·
            refine ⟨5781954928202240119829585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854636618801493413219723 5781954928202240119829585)
            ·
              refine ⟨4336466196151680089872189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5781954928202240119829585 4336466196151680089872189)
              ·
                refine ⟨1626174823556880033702071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336466196151680089872189 1626174823556880033702071)
                ·
                  refine ⟨2439262235335320050553107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626174823556880033702071 2439262235335320050553107)
                  ·
                    refine ⟨3658893353002980075829661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439262235335320050553107 3658893353002980075829661)
                    ·
                      refine ⟨1372085007376117528436123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658893353002980075829661 1372085007376117528436123)
                      ·
                        rfl

theorem cell23_2672126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2672126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672126 prefixEnd_2672126 := by exact prefixLift 2672126
  have htrace : WordTrace (prefixWord ++ tailWord_2672126) baseStart_2672126 baseEnd_2672126 := by
    simpa [prefixWord, tailWord_2672126, baseEnd_2672126] using wordTrace_append hprefix tailTrace_2672126
  have hstable : (prefixWord ++ tailWord_2672126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672126).length < 2 ^ (prefixWord ++ tailWord_2672126).sum := by decide
  have hdescent : baseEnd_2672126 < baseStart_2672126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672131 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3]
def baseStart_2672131 : Nat := 118140960795 + 2672131 * 2 ^ 59
def prefixEnd_2672131 : Nat := 4983230072969 + 3 ^ 40 * 2672131 * 2
def baseEnd_2672131 : Nat := 1372087574779390008873599

theorem tailTrace_2672131 : CollatzResearch.WordTrace tailWord_2672131 prefixEnd_2672131 1372087574779390008873599 := by
  unfold tailWord_2672131
  simp only [CollatzResearch.WordTrace]
  refine ⟨97460624282333225486944247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64973749521555483657962831 97460624282333225486944247)
  ·
    refine ⟨146190936423499838230416371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97460624282333225486944247 146190936423499838230416371)
    ·
      refine ⟨219286404635249757345624557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146190936423499838230416371 219286404635249757345624557)
      ·
        refine ⟨82232401738218659004609209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219286404635249757345624557 82232401738218659004609209)
        ·
          refine ⟨61674301303663994253456907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82232401738218659004609209 61674301303663994253456907)
          ·
            refine ⟨92511451955495991380185361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61674301303663994253456907 92511451955495991380185361)
            ·
              refine ⟨69383588966621993535139021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92511451955495991380185361 69383588966621993535139021)
              ·
                refine ⟨26018845862483247575677133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69383588966621993535139021 26018845862483247575677133)
                ·
                  refine ⟨9757067198431217840878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26018845862483247575677133 9757067198431217840878925)
                  ·
                    refine ⟨3658900199411706690329597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9757067198431217840878925 3658900199411706690329597)
                    ·
                      refine ⟨1372087574779390008873599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658900199411706690329597 1372087574779390008873599)
                      ·
                        rfl

theorem cell23_2672131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_2672131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672131 prefixEnd_2672131 := by exact prefixLift 2672131
  have htrace : WordTrace (prefixWord ++ tailWord_2672131) baseStart_2672131 baseEnd_2672131 := by
    simpa [prefixWord, tailWord_2672131, baseEnd_2672131] using wordTrace_append hprefix tailTrace_2672131
  have hstable : (prefixWord ++ tailWord_2672131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672131).length < 2 ^ (prefixWord ++ tailWord_2672131).sum := by decide
  have hdescent : baseEnd_2672131 < baseStart_2672131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672135 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2672135 : Nat := 118140960795 + 2672135 * 2 ^ 59
def prefixEnd_2672135 : Nat := 4983230072969 + 3 ^ 40 * 2672135 * 2
def baseEnd_2672135 : Nat := 1372089628702007993223581

theorem tailTrace_2672135 : CollatzResearch.WordTrace tailWord_2672135 prefixEnd_2672135 1372089628702007993223581 := by
  unfold tailWord_2672135
  simp only [CollatzResearch.WordTrace]
  refine ⟨97460770174318734170089859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64973846782879156113393239 97460770174318734170089859)
  ·
    refine ⟨146191155261478101255134789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97460770174318734170089859 146191155261478101255134789)
    ·
      refine ⟨27410841611527143985337773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146191155261478101255134789 27410841611527143985337773)
      ·
        refine ⟨10279065604322678994501665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27410841611527143985337773 10279065604322678994501665)
        ·
          refine ⟨7709299203242009245876249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10279065604322678994501665 7709299203242009245876249)
          ·
            refine ⟨5781974402431506934407187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7709299203242009245876249 5781974402431506934407187)
            ·
              refine ⟨8672961603647260401610781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781974402431506934407187 8672961603647260401610781)
              ·
                refine ⟨3252360601367722650604043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8672961603647260401610781 3252360601367722650604043)
                ·
                  refine ⟨4878540902051583975906065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252360601367722650604043 4878540902051583975906065)
                  ·
                    refine ⟨3658905676538687981929549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878540902051583975906065 3658905676538687981929549)
                    ·
                      refine ⟨1372089628702007993223581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3658905676538687981929549 1372089628702007993223581)
                      ·
                        rfl

theorem cell23_2672135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2672135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672135 prefixEnd_2672135 := by exact prefixLift 2672135
  have htrace : WordTrace (prefixWord ++ tailWord_2672135) baseStart_2672135 baseEnd_2672135 := by
    simpa [prefixWord, tailWord_2672135, baseEnd_2672135] using wordTrace_append hprefix tailTrace_2672135
  have hstable : (prefixWord ++ tailWord_2672135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672135).length < 2 ^ (prefixWord ++ tailWord_2672135).sum := by decide
  have hdescent : baseEnd_2672135 < baseStart_2672135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672142 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2672142 : Nat := 118140960795 + 2672142 * 2 ^ 59
def prefixEnd_2672142 : Nat := 4983230072969 + 3 ^ 40 * 2672142 * 2
def baseEnd_2672142 : Nat := 457364407688863155278683

theorem tailTrace_2672142 : CollatzResearch.WordTrace tailWord_2672142 prefixEnd_2672142 457364407688863155278683 := by
  unfold tailWord_2672142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182628185661671795699335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64974016990195582910396453 12182628185661671795699335)
  ·
    refine ⟨18273942278492507693549003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12182628185661671795699335 18273942278492507693549003)
    ·
      refine ⟨27410913417738761540323505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273942278492507693549003 27410913417738761540323505)
      ·
        refine ⟨20558185063304071155242629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27410913417738761540323505 20558185063304071155242629)
        ·
          refine ⟨3854659699369513341607993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20558185063304071155242629 3854659699369513341607993)
          ·
            refine ⟨2890994774527135006205995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3854659699369513341607993 2890994774527135006205995)
            ·
              refine ⟨4336492161790702509308993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890994774527135006205995 4336492161790702509308993)
              ·
                refine ⟨3252369121343026881981745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4336492161790702509308993 3252369121343026881981745)
                ·
                  refine ⟨2439276841007270161486309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3252369121343026881981745 2439276841007270161486309)
                  ·
                    refine ⟨457364407688863155278683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439276841007270161486309 457364407688863155278683)
                    ·
                      rfl

theorem cell23_2672142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2672142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672142 prefixEnd_2672142 := by exact prefixLift 2672142
  have htrace : WordTrace (prefixWord ++ tailWord_2672142) baseStart_2672142 baseEnd_2672142 := by
    simpa [prefixWord, tailWord_2672142, baseEnd_2672142] using wordTrace_append hprefix tailTrace_2672142
  have hstable : (prefixWord ++ tailWord_2672142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672142).length < 2 ^ (prefixWord ++ tailWord_2672142).sum := by decide
  have hdescent : baseEnd_2672142 < baseStart_2672142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672191 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2672191 : Nat := 118140960795 + 2672191 * 2 ^ 59
def prefixEnd_2672191 : Nat := 4983230072969 + 3 ^ 40 * 2672191 * 2
def baseEnd_2672191 : Nat := 1372118383618659774123323

theorem tailTrace_2672191 : CollatzResearch.WordTrace tailWord_2672191 prefixEnd_2672191 1372118383618659774123323 := by
  unfold tailWord_2672191
  simp only [CollatzResearch.WordTrace]
  refine ⟨97462812662115855734128427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64975208441410570489418951 97462812662115855734128427)
  ·
    refine ⟨146194218993173783601192641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97462812662115855734128427 146194218993173783601192641)
    ·
      refine ⟨109645664244880337700894481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146194218993173783601192641 109645664244880337700894481)
      ·
        refine ⟨82234248183660253275670861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109645664244880337700894481 82234248183660253275670861)
        ·
          refine ⟨30837843068872594978376573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82234248183660253275670861 30837843068872594978376573)
          ·
            refine ⟨11564191150827223116891215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30837843068872594978376573 11564191150827223116891215)
            ·
              refine ⟨17346286726240834675336823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11564191150827223116891215 17346286726240834675336823)
              ·
                refine ⟨26019430089361252013005235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17346286726240834675336823 26019430089361252013005235)
                ·
                  refine ⟨39029145134041878019507853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26019430089361252013005235 39029145134041878019507853)
                  ·
                    refine ⟨14635929425265704257315445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39029145134041878019507853 14635929425265704257315445)
                    ·
                      refine ⟨1372118383618659774123323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14635929425265704257315445 1372118383618659774123323)
                      ·
                        rfl

theorem cell23_2672191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2672191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672191 prefixEnd_2672191 := by exact prefixLift 2672191
  have htrace : WordTrace (prefixWord ++ tailWord_2672191) baseStart_2672191 baseEnd_2672191 := by
    simpa [prefixWord, tailWord_2672191, baseEnd_2672191] using wordTrace_append hprefix tailTrace_2672191
  have hstable : (prefixWord ++ tailWord_2672191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672191).length < 2 ^ (prefixWord ++ tailWord_2672191).sum := by decide
  have hdescent : baseEnd_2672191 < baseStart_2672191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672201 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_2672201 : Nat := 118140960795 + 2672201 * 2 ^ 59
def prefixEnd_2672201 : Nat := 4983230072969 + 3 ^ 40 * 2672201 * 2
def baseEnd_2672201 : Nat := 1372123518425204734998277

theorem tailTrace_2672201 : CollatzResearch.WordTrace tailWord_2672201 prefixEnd_2672201 1372123518425204734998277 := by
  unfold tailWord_2672201
  simp only [CollatzResearch.WordTrace]
  refine ⟨97463177392079627441992457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64975451594719751627994971 97463177392079627441992457)
  ·
    refine ⟨73097383044059720581494343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97463177392079627441992457 73097383044059720581494343)
    ·
      refine ⟨109646074566089580872241515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73097383044059720581494343 109646074566089580872241515)
      ·
        refine ⟨164469111849134371308362273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109646074566089580872241515 164469111849134371308362273)
        ·
          refine ⟨123351833886850778481271705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164469111849134371308362273 123351833886850778481271705)
          ·
            refine ⟨92513875415138083860953779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123351833886850778481271705 92513875415138083860953779)
            ·
              refine ⟨138770813122707125791430669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92513875415138083860953779 138770813122707125791430669)
              ·
                refine ⟨52039054921015172171786501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138770813122707125791430669 52039054921015172171786501)
                ·
                  refine ⟨9757322797690344782209969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52039054921015172171786501 9757322797690344782209969)
                  ·
                    refine ⟨7317992098267758586657477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9757322797690344782209969 7317992098267758586657477)
                    ·
                      refine ⟨1372123518425204734998277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7317992098267758586657477 1372123518425204734998277)
                      ·
                        rfl

theorem cell23_2672201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_2672201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672201 prefixEnd_2672201 := by exact prefixLift 2672201
  have htrace : WordTrace (prefixWord ++ tailWord_2672201) baseStart_2672201 baseEnd_2672201 := by
    simpa [prefixWord, tailWord_2672201, baseEnd_2672201] using wordTrace_append hprefix tailTrace_2672201
  have hstable : (prefixWord ++ tailWord_2672201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672201).length < 2 ^ (prefixWord ++ tailWord_2672201).sum := by decide
  have hdescent : baseEnd_2672201 < baseStart_2672201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672241 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2672241 : Nat := 118140960795 + 2672241 * 2 ^ 59
def prefixEnd_2672241 : Nat := 4983230072969 + 3 ^ 40 * 2672241 * 2
def baseEnd_2672241 : Nat := 457381352550461526166031

theorem tailTrace_2672241 : CollatzResearch.WordTrace tailWord_2672241 prefixEnd_2672241 457381352550461526166031 := by
  unfold tailWord_2672241
  simp only [CollatzResearch.WordTrace]
  refine ⟨97464636311934714273448577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64976424207956476182299051 97464636311934714273448577)
  ·
    refine ⟨73098477233951035705086433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97464636311934714273448577 73098477233951035705086433)
    ·
      refine ⟨54823857925463276778814825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73098477233951035705086433 54823857925463276778814825)
      ·
        refine ⟨41117893444097457584111119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54823857925463276778814825 41117893444097457584111119)
        ·
          refine ⟨61676840166146186376166679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41117893444097457584111119 61676840166146186376166679)
          ·
            refine ⟨92515260249219279564250019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61676840166146186376166679 92515260249219279564250019)
            ·
              refine ⟨138772890373828919346375029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92515260249219279564250019 138772890373828919346375029)
              ·
                refine ⟨13009958472546461188722659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138772890373828919346375029 13009958472546461188722659)
                ·
                  refine ⟨19514937708819691783083989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13009958472546461188722659 19514937708819691783083989)
                  ·
                    refine ⟨457381352550461526166031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19514937708819691783083989 457381352550461526166031)
                    ·
                      rfl

theorem cell23_2672241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2672241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672241 prefixEnd_2672241 := by exact prefixLift 2672241
  have htrace : WordTrace (prefixWord ++ tailWord_2672241) baseStart_2672241 baseEnd_2672241 := by
    simpa [prefixWord, tailWord_2672241, baseEnd_2672241] using wordTrace_append hprefix tailTrace_2672241
  have hstable : (prefixWord ++ tailWord_2672241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672241).length < 2 ^ (prefixWord ++ tailWord_2672241).sum := by decide
  have hdescent : baseEnd_2672241 < baseStart_2672241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672248 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_2672248 : Nat := 118140960795 + 2672248 * 2 ^ 59
def prefixEnd_2672248 : Nat := 4983230072969 + 3 ^ 40 * 2672248 * 2
def baseEnd_2672248 : Nat := 1372147652015966051110561

theorem tailTrace_2672248 : CollatzResearch.WordTrace tailWord_2672248 prefixEnd_2672248 1372147652015966051110561 := by
  unfold tailWord_2672248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48732445811454677234476699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64976594415272902979302265 48732445811454677234476699)
  ·
    refine ⟨73098668717182015851715049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48732445811454677234476699 73098668717182015851715049)
    ·
      refine ⟨54824001537886511888786287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73098668717182015851715049 54824001537886511888786287)
      ·
        refine ⟨82236002306829767833179431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54824001537886511888786287 82236002306829767833179431)
        ·
          refine ⟨123354003460244651749769147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82236002306829767833179431 123354003460244651749769147)
          ·
            refine ⟨185031005190366977624653721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123354003460244651749769147 185031005190366977624653721)
            ·
              refine ⟨138773253892775233218490291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185031005190366977624653721 138773253892775233218490291)
              ·
                refine ⟨208159880839162849827735437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138773253892775233218490291 208159880839162849827735437)
                ·
                  refine ⟨78059955314686068685400789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208159880839162849827735437 78059955314686068685400789)
                  ·
                    refine ⟨1829530202687954734814081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78059955314686068685400789 1829530202687954734814081)
                    ·
                      refine ⟨1372147652015966051110561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829530202687954734814081 1372147652015966051110561)
                      ·
                        rfl

theorem cell23_2672248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_2672248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672248 prefixEnd_2672248 := by exact prefixLift 2672248
  have htrace : WordTrace (prefixWord ++ tailWord_2672248) baseStart_2672248 baseEnd_2672248 := by
    simpa [prefixWord, tailWord_2672248, baseEnd_2672248] using wordTrace_append hprefix tailTrace_2672248
  have hstable : (prefixWord ++ tailWord_2672248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672248).length < 2 ^ (prefixWord ++ tailWord_2672248).sum := by decide
  have hdescent : baseEnd_2672248 < baseStart_2672248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672251 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_2672251 : Nat := 118140960795 + 2672251 * 2 ^ 59
def prefixEnd_2672251 : Nat := 4983230072969 + 3 ^ 40 * 2672251 * 2
def baseEnd_2672251 : Nat := 1372149192457929539373047

theorem tailTrace_2672251 : CollatzResearch.WordTrace tailWord_2672251 prefixEnd_2672251 1372149192457929539373047 := by
  unfold tailWord_2672251
  simp only [CollatzResearch.WordTrace]
  refine ⟨97465001041898485981312607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64976667361265657320875071 97465001041898485981312607)
  ·
    refine ⟨146197501562847728971968911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97465001041898485981312607 146197501562847728971968911)
    ·
      refine ⟨219296252344271593457953367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146197501562847728971968911 219296252344271593457953367)
      ·
        refine ⟨328944378516407390186930051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219296252344271593457953367 328944378516407390186930051)
        ·
          refine ⟨493416567774611085280395077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328944378516407390186930051 493416567774611085280395077)
          ·
            refine ⟨92515606457739578490074077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493416567774611085280395077 92515606457739578490074077)
            ·
              refine ⟨34693352421652341933777779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92515606457739578490074077 34693352421652341933777779)
              ·
                refine ⟨52040028632478512900666669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34693352421652341933777779 52040028632478512900666669)
                ·
                  refine ⟨19515010737179442337750001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52040028632478512900666669 19515010737179442337750001)
                  ·
                    refine ⟨14636258052884581753312501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19515010737179442337750001 14636258052884581753312501)
                    ·
                      refine ⟨1372149192457929539373047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14636258052884581753312501 1372149192457929539373047)
                      ·
                        rfl

theorem cell23_2672251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_2672251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672251 prefixEnd_2672251 := by exact prefixLift 2672251
  have htrace : WordTrace (prefixWord ++ tailWord_2672251) baseStart_2672251 baseEnd_2672251 := by
    simpa [prefixWord, tailWord_2672251, baseEnd_2672251] using wordTrace_append hprefix tailTrace_2672251
  have hstable : (prefixWord ++ tailWord_2672251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672251).length < 2 ^ (prefixWord ++ tailWord_2672251).sum := by decide
  have hdescent : baseEnd_2672251 < baseStart_2672251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672296 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 5]
def baseStart_2672296 : Nat := 118140960795 + 2672296 * 2 ^ 59
def prefixEnd_2672296 : Nat := 4983230072969 + 3 ^ 40 * 2672296 * 2
def baseEnd_2672296 : Nat := 152463588787486873701149

theorem tailTrace_2672296 : CollatzResearch.WordTrace tailWord_2672296 prefixEnd_2672296 152463588787486873701149 := by
  unfold tailWord_2672296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48733321163367729333350371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64977761551156972444467161 48733321163367729333350371)
  ·
    refine ⟨73099981745051594000025557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48733321163367729333350371 73099981745051594000025557)
    ·
      refine ⟨1713280822149646734375599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 73099981745051594000025557 1713280822149646734375599)
      ·
        refine ⟨2569921233224470101563399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713280822149646734375599 2569921233224470101563399)
        ·
          refine ⟨3854881849836705152345099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569921233224470101563399 3854881849836705152345099)
          ·
            refine ⟨5782322774755057728517649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854881849836705152345099 5782322774755057728517649)
            ·
              refine ⟨4336742081066293296388237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782322774755057728517649 4336742081066293296388237)
              ·
                refine ⟨1626278280399859986145589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336742081066293296388237 1626278280399859986145589)
                ·
                  refine ⟨152463588787486873701149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1626278280399859986145589 152463588787486873701149)
                  ·
                    rfl

theorem cell23_2672296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 5].length) (baseStart_2672296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672296 prefixEnd_2672296 := by exact prefixLift 2672296
  have htrace : WordTrace (prefixWord ++ tailWord_2672296) baseStart_2672296 baseEnd_2672296 := by
    simpa [prefixWord, tailWord_2672296, baseEnd_2672296] using wordTrace_append hprefix tailTrace_2672296
  have hstable : (prefixWord ++ tailWord_2672296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672296).length < 2 ^ (prefixWord ++ tailWord_2672296).sum := by decide
  have hdescent : baseEnd_2672296 < baseStart_2672296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672408 : List Nat := [2, 1, 2, 3, 1, 1, 4, 9]
def baseStart_2672408 : Nat := 118140960795 + 2672408 * 2 ^ 59
def prefixEnd_2672408 : Nat := 4983230072969 + 3 ^ 40 * 2672408 * 2
def baseEnd_2672408 : Nat := 50823326256321682411475

theorem tailTrace_2672408 : CollatzResearch.WordTrace tailWord_2672408 prefixEnd_2672408 50823326256321682411475 := by
  unfold tailWord_2672408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48735363651164850897388939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64980484868219801196518585 48735363651164850897388939)
  ·
    refine ⟨73103045476747276346083409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48735363651164850897388939 73103045476747276346083409)
    ·
      refine ⟨54827284107560457259562557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73103045476747276346083409 54827284107560457259562557)
      ·
        refine ⟨20560231540335171472335959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54827284107560457259562557 20560231540335171472335959)
        ·
          refine ⟨30840347310502757208503939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20560231540335171472335959 30840347310502757208503939)
          ·
            refine ⟨46260520965754135812755909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30840347310502757208503939 46260520965754135812755909)
            ·
              refine ⟨8673847681078900464891733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46260520965754135812755909 8673847681078900464891733)
              ·
                refine ⟨50823326256321682411475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8673847681078900464891733 50823326256321682411475)
                ·
                  rfl

theorem cell23_2672408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 9].length) (baseStart_2672408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672408 prefixEnd_2672408 := by exact prefixLift 2672408
  have htrace : WordTrace (prefixWord ++ tailWord_2672408) baseStart_2672408 baseEnd_2672408 := by
    simpa [prefixWord, tailWord_2672408, baseEnd_2672408] using wordTrace_append hprefix tailTrace_2672408
  have hstable : (prefixWord ++ tailWord_2672408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672408).length < 2 ^ (prefixWord ++ tailWord_2672408).sum := by decide
  have hdescent : baseEnd_2672408 < baseStart_2672408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672415 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2672415 : Nat := 118140960795 + 2672415 * 2 ^ 59
def prefixEnd_2672415 : Nat := 4983230072969 + 3 ^ 40 * 2672415 * 2
def baseEnd_2672415 : Nat := 1372233403285266897722293

theorem tailTrace_2672415 : CollatzResearch.WordTrace tailWord_2672415 prefixEnd_2672415 1372233403285266897722293 := by
  unfold tailWord_2672415
  simp only [CollatzResearch.WordTrace]
  refine ⟨97470982613304341990282699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64980655075536227993521799 97470982613304341990282699)
  ·
    refine ⟨146206473919956512985424049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97470982613304341990282699 146206473919956512985424049)
    ·
      refine ⟨109654855439967384739068037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146206473919956512985424049 109654855439967384739068037)
      ·
        refine ⟨20560285394993884638575257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109654855439967384739068037 20560285394993884638575257)
        ·
          refine ⟨15420214046245413478931443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20560285394993884638575257 15420214046245413478931443)
          ·
            refine ⟨23130321069368120218397165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15420214046245413478931443 23130321069368120218397165)
            ·
              refine ⟨8673870401013045081898937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23130321069368120218397165 8673870401013045081898937)
              ·
                refine ⟨6505402800759783811424203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8673870401013045081898937 6505402800759783811424203)
                ·
                  refine ⟨9758104201139675717136305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6505402800759783811424203 9758104201139675717136305)
                  ·
                    refine ⟨7318578150854756787852229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9758104201139675717136305 7318578150854756787852229)
                    ·
                      refine ⟨1372233403285266897722293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7318578150854756787852229 1372233403285266897722293)
                      ·
                        rfl

theorem cell23_2672415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2672415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672415 prefixEnd_2672415 := by exact prefixLift 2672415
  have htrace : WordTrace (prefixWord ++ tailWord_2672415) baseStart_2672415 baseEnd_2672415 := by
    simpa [prefixWord, tailWord_2672415, baseEnd_2672415] using wordTrace_append hprefix tailTrace_2672415
  have hstable : (prefixWord ++ tailWord_2672415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672415).length < 2 ^ (prefixWord ++ tailWord_2672415).sum := by decide
  have hdescent : baseEnd_2672415 < baseStart_2672415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672430 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2672430 : Nat := 118140960795 + 2672430 * 2 ^ 59
def prefixEnd_2672430 : Nat := 4983230072969 + 3 ^ 40 * 2672430 * 2
def baseEnd_2672430 : Nat := 1372241105495084339034725

theorem tailTrace_2672430 : CollatzResearch.WordTrace tailWord_2672430 prefixEnd_2672430 1372241105495084339034725 := by
  unfold tailWord_2672430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183941213531249944009843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64981019805499999701385829 12183941213531249944009843)
  ·
    refine ⟨18275911820296874916014765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12183941213531249944009843 18275911820296874916014765)
    ·
      refine ⟨6853466932611328093505537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18275911820296874916014765 6853466932611328093505537)
      ·
        refine ⟨5140100199458496070129153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6853466932611328093505537 5140100199458496070129153)
        ·
          refine ⟨3855075149593872052596865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5140100199458496070129153 3855075149593872052596865)
          ·
            refine ⟨2891306362195404039447649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855075149593872052596865 2891306362195404039447649)
            ·
              refine ⟨2168479771646553029585737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891306362195404039447649 2168479771646553029585737)
              ·
                refine ⟨1626359828734914772189303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168479771646553029585737 1626359828734914772189303)
                ·
                  refine ⟨2439539743102372158283955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626359828734914772189303 2439539743102372158283955)
                  ·
                    refine ⟨3659309614653558237425933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439539743102372158283955 3659309614653558237425933)
                    ·
                      refine ⟨1372241105495084339034725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3659309614653558237425933 1372241105495084339034725)
                      ·
                        rfl

theorem cell23_2672430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2672430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672430 prefixEnd_2672430 := by exact prefixLift 2672430
  have htrace : WordTrace (prefixWord ++ tailWord_2672430) baseStart_2672430 baseEnd_2672430 := by
    simpa [prefixWord, tailWord_2672430, baseEnd_2672430] using wordTrace_append hprefix tailTrace_2672430
  have hstable : (prefixWord ++ tailWord_2672430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672430).length < 2 ^ (prefixWord ++ tailWord_2672430).sum := by decide
  have hdescent : baseEnd_2672430 < baseStart_2672430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672448 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_2672448 : Nat := 118140960795 + 2672448 * 2 ^ 59
def prefixEnd_2672448 : Nat := 4983230072969 + 3 ^ 40 * 2672448 * 2
def baseEnd_2672448 : Nat := 1372250348146865268609641

theorem tailTrace_2672448 : CollatzResearch.WordTrace tailWord_2672448 prefixEnd_2672448 1372250348146865268609641 := by
  unfold tailWord_2672448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48736093111092394313116999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64981457481456525750822665 48736093111092394313116999)
  ·
    refine ⟨73104139666638591469675499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48736093111092394313116999 73104139666638591469675499)
    ·
      refine ⟨109656209499957887204513249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73104139666638591469675499 109656209499957887204513249)
      ·
        refine ⟨82242157124968415403384937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109656209499957887204513249 82242157124968415403384937)
        ·
          refine ⟨61681617843726311552538703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82242157124968415403384937 61681617843726311552538703)
          ·
            refine ⟨92522426765589467328808055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61681617843726311552538703 92522426765589467328808055)
            ·
              refine ⟨138783640148384200993212083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92522426765589467328808055 138783640148384200993212083)
              ·
                refine ⟨208175460222576301489818125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138783640148384200993212083 208175460222576301489818125)
                ·
                  refine ⟨78065797583466113058681797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208175460222576301489818125 78065797583466113058681797)
                  ·
                    refine ⟨14637337046899896198502837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78065797583466113058681797 14637337046899896198502837)
                    ·
                      refine ⟨1372250348146865268609641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14637337046899896198502837 1372250348146865268609641)
                      ·
                        rfl

theorem cell23_2672448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2672448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672448 prefixEnd_2672448 := by exact prefixLift 2672448
  have htrace : WordTrace (prefixWord ++ tailWord_2672448) baseStart_2672448 baseEnd_2672448 := by
    simpa [prefixWord, tailWord_2672448, baseEnd_2672448] using wordTrace_append hprefix tailTrace_2672448
  have hstable : (prefixWord ++ tailWord_2672448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672448).length < 2 ^ (prefixWord ++ tailWord_2672448).sum := by decide
  have hdescent : baseEnd_2672448 < baseStart_2672448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672479 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 1, 3, 2]
def baseStart_2672479 : Nat := 118140960795 + 2672479 * 2 ^ 59
def prefixEnd_2672479 : Nat := 4983230072969 + 3 ^ 40 * 2672479 * 2
def baseEnd_2672479 : Nat := 1372266266047154647321999

theorem tailTrace_2672479 : CollatzResearch.WordTrace tailWord_2672479 prefixEnd_2672479 1372266266047154647321999 := by
  unfold tailWord_2672479
  simp only [CollatzResearch.WordTrace]
  refine ⟨97473316885072480920612491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64982211256714987280408327 97473316885072480920612491)
  ·
    refine ⟨146209975327608721380918737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97473316885072480920612491 146209975327608721380918737)
    ·
      refine ⟨109657481495706541035689053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146209975327608721380918737 109657481495706541035689053)
      ·
        refine ⟨41121555560889952888383395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109657481495706541035689053 41121555560889952888383395)
        ·
          refine ⟨61682333341334929332575093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41121555560889952888383395 61682333341334929332575093)
          ·
            refine ⟨5782718750750149624928915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61682333341334929332575093 5782718750750149624928915)
            ·
              refine ⟨8674078126125224437393373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782718750750149624928915 8674078126125224437393373)
              ·
                refine ⟨3252779297296959164022515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8674078126125224437393373 3252779297296959164022515)
                ·
                  refine ⟨4879168945945438746033773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252779297296959164022515 4879168945945438746033773)
                  ·
                    refine ⟨1829688354729539529762665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4879168945945438746033773 1829688354729539529762665)
                    ·
                      refine ⟨1372266266047154647321999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829688354729539529762665 1372266266047154647321999)
                      ·
                        rfl

theorem cell23_2672479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_2672479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672479 prefixEnd_2672479 := by exact prefixLift 2672479
  have htrace : WordTrace (prefixWord ++ tailWord_2672479) baseStart_2672479 baseEnd_2672479 := by
    simpa [prefixWord, tailWord_2672479, baseEnd_2672479] using wordTrace_append hprefix tailTrace_2672479
  have hstable : (prefixWord ++ tailWord_2672479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672479).length < 2 ^ (prefixWord ++ tailWord_2672479).sum := by decide
  have hdescent : baseEnd_2672479 < baseStart_2672479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672505 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2672505 : Nat := 118140960795 + 2672505 * 2 ^ 59
def prefixEnd_2672505 : Nat := 4983230072969 + 3 ^ 40 * 2672505 * 2
def baseEnd_2672505 : Nat := 1372279616544171545596879

theorem tailTrace_2672505 : CollatzResearch.WordTrace tailWord_2672505 prefixEnd_2672505 1372279616544171545596879 := by
  unfold tailWord_2672505
  simp only [CollatzResearch.WordTrace]
  refine ⟨97474265182978287361058969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64982843455318858240705979 97474265182978287361058969)
  ·
    refine ⟨73105698887233715520794227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97474265182978287361058969 73105698887233715520794227)
    ·
      refine ⟨109658548330850573281191341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73105698887233715520794227 109658548330850573281191341)
      ·
        refine ⟨41121955624068964980446753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109658548330850573281191341 41121955624068964980446753)
        ·
          refine ⟨30841466718051723735335065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41121955624068964980446753 30841466718051723735335065)
          ·
            refine ⟨23131100038538792801501299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30841466718051723735335065 23131100038538792801501299)
            ·
              refine ⟨34696650057808189202251949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23131100038538792801501299 34696650057808189202251949)
              ·
                refine ⟨13011243771678070950844481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34696650057808189202251949 13011243771678070950844481)
                ·
                  refine ⟨9758432828758553213133361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13011243771678070950844481 9758432828758553213133361)
                  ·
                    refine ⟨7318824621568914909850021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9758432828758553213133361 7318824621568914909850021)
                    ·
                      refine ⟨1372279616544171545596879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7318824621568914909850021 1372279616544171545596879)
                      ·
                        rfl

theorem cell23_2672505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2672505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672505 prefixEnd_2672505 := by exact prefixLift 2672505
  have htrace : WordTrace (prefixWord ++ tailWord_2672505) baseStart_2672505 baseEnd_2672505 := by
    simpa [prefixWord, tailWord_2672505, baseEnd_2672505] using wordTrace_append hprefix tailTrace_2672505
  have hstable : (prefixWord ++ tailWord_2672505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672505).length < 2 ^ (prefixWord ++ tailWord_2672505).sum := by decide
  have hdescent : baseEnd_2672505 < baseStart_2672505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672513 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2672513 : Nat := 118140960795 + 2672513 * 2 ^ 59
def prefixEnd_2672513 : Nat := 4983230072969 + 3 ^ 40 * 2672513 * 2
def baseEnd_2672513 : Nat := 1372283724389407514296843

theorem tailTrace_2672513 : CollatzResearch.WordTrace tailWord_2672513 prefixEnd_2672513 1372283724389407514296843 := by
  unfold tailWord_2672513
  simp only [CollatzResearch.WordTrace]
  refine ⟨97474556966949304727350193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64983037977966203151566795 97474556966949304727350193)
  ·
    refine ⟨73105917725211978545512645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97474556966949304727350193 73105917725211978545512645)
    ·
      refine ⟨13707359573477245977283621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73105917725211978545512645 13707359573477245977283621)
      ·
        refine ⟨2570129920026983620740679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13707359573477245977283621 2570129920026983620740679)
        ·
          refine ⟨3855194880040475431111019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570129920026983620740679 3855194880040475431111019)
          ·
            refine ⟨5782792320060713146666529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855194880040475431111019 5782792320060713146666529)
            ·
              refine ⟨4337094240045534859999897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782792320060713146666529 4337094240045534859999897)
              ·
                refine ⟨3252820680034151144999923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337094240045534859999897 3252820680034151144999923)
                ·
                  refine ⟨4879231020051226717499885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252820680034151144999923 4879231020051226717499885)
                  ·
                    refine ⟨1829711632519210019062457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4879231020051226717499885 1829711632519210019062457)
                    ·
                      refine ⟨1372283724389407514296843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829711632519210019062457 1372283724389407514296843)
                      ·
                        rfl

theorem cell23_2672513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2672513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672513 prefixEnd_2672513 := by exact prefixLift 2672513
  have htrace : WordTrace (prefixWord ++ tailWord_2672513) baseStart_2672513 baseEnd_2672513 := by
    simpa [prefixWord, tailWord_2672513, baseEnd_2672513] using wordTrace_append hprefix tailTrace_2672513
  have hstable : (prefixWord ++ tailWord_2672513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672513).length < 2 ^ (prefixWord ++ tailWord_2672513).sum := by decide
  have hdescent : baseEnd_2672513 < baseStart_2672513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672515 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 7]
def baseStart_2672515 : Nat := 118140960795 + 2672515 * 2 ^ 59
def prefixEnd_2672515 : Nat := 4983230072969 + 3 ^ 40 * 2672515 * 2
def baseEnd_2672515 : Nat := 152476083483412945163537

theorem tailTrace_2672515 : CollatzResearch.WordTrace tailWord_2672515 prefixEnd_2672515 152476083483412945163537 := by
  unfold tailWord_2672515
  simp only [CollatzResearch.WordTrace]
  refine ⟨97474629912942059068922999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64983086608628039379281999 97474629912942059068922999)
  ·
    refine ⟨146211944869413088603384499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97474629912942059068922999 146211944869413088603384499)
    ·
      refine ⟨219317917304119632905076749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146211944869413088603384499 219317917304119632905076749)
      ·
        refine ⟨82244218989044862339403781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219317917304119632905076749 82244218989044862339403781)
        ·
          refine ⟨15420791060445911688638209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82244218989044862339403781 15420791060445911688638209)
          ·
            refine ⟨11565593295334433766478657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15420791060445911688638209 11565593295334433766478657)
            ·
              refine ⟨8674194971500825324858993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11565593295334433766478657 8674194971500825324858993)
              ·
                refine ⟨6505646228625618993644245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8674194971500825324858993 6505646228625618993644245)
                ·
                  refine ⟨152476083483412945163537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6505646228625618993644245 152476083483412945163537)
                  ·
                    rfl

theorem cell23_2672515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 7].length) (baseStart_2672515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672515 prefixEnd_2672515 := by exact prefixLift 2672515
  have htrace : WordTrace (prefixWord ++ tailWord_2672515) baseStart_2672515 baseEnd_2672515 := by
    simpa [prefixWord, tailWord_2672515, baseEnd_2672515] using wordTrace_append hprefix tailTrace_2672515
  have hstable : (prefixWord ++ tailWord_2672515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672515).length < 2 ^ (prefixWord ++ tailWord_2672515).sum := by decide
  have hdescent : baseEnd_2672515 < baseStart_2672515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672659 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 2, 3, 2]
def baseStart_2672659 : Nat := 118140960795 + 2672659 * 2 ^ 59
def prefixEnd_2672659 : Nat := 4983230072969 + 3 ^ 40 * 2672659 * 2
def baseEnd_2672659 : Nat := 1372358692564963943071171

theorem tailTrace_2672659 : CollatzResearch.WordTrace tailWord_2672659 prefixEnd_2672659 1372358692564963943071171 := by
  unfold tailWord_2672659
  simp only [CollatzResearch.WordTrace]
  refine ⟨97479882024420371662165031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64986588016280247774776687 97479882024420371662165031)
  ·
    refine ⟨146219823036630557493247547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97479882024420371662165031 146219823036630557493247547)
    ·
      refine ⟨219329734554945836239871321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146219823036630557493247547 219329734554945836239871321)
      ·
        refine ⟨164497300916209377179903491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219329734554945836239871321 164497300916209377179903491)
        ·
          refine ⟨246745951374314065769855237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164497300916209377179903491 246745951374314065769855237)
          ·
            refine ⟨46264865882683887331847857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246745951374314065769855237 46264865882683887331847857)
            ·
              refine ⟨34698649412012915498885893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46264865882683887331847857 34698649412012915498885893)
              ·
                refine ⟨6505996764752421656041105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34698649412012915498885893 6505996764752421656041105)
                ·
                  refine ⟨4879497573564316242030829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505996764752421656041105 4879497573564316242030829)
                  ·
                    refine ⟨1829811590086618590761561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4879497573564316242030829 1829811590086618590761561)
                    ·
                      refine ⟨1372358692564963943071171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829811590086618590761561 1372358692564963943071171)
                      ·
                        rfl

theorem cell23_2672659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3, 2].length) (baseStart_2672659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672659 prefixEnd_2672659 := by exact prefixLift 2672659
  have htrace : WordTrace (prefixWord ++ tailWord_2672659) baseStart_2672659 baseEnd_2672659 := by
    simpa [prefixWord, tailWord_2672659, baseEnd_2672659] using wordTrace_append hprefix tailTrace_2672659
  have hstable : (prefixWord ++ tailWord_2672659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672659).length < 2 ^ (prefixWord ++ tailWord_2672659).sum := by decide
  have hdescent : baseEnd_2672659 < baseStart_2672659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672666 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2672666 : Nat := 118140960795 + 2672666 * 2 ^ 59
def prefixEnd_2672666 : Nat := 4983230072969 + 3 ^ 40 * 2672666 * 2
def baseEnd_2672666 : Nat := 1372362286929545415683639

theorem tailTrace_2672666 : CollatzResearch.WordTrace tailWord_2672666 prefixEnd_2672666 1372362286929545415683639 := by
  unfold tailWord_2672666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370034333848752964417463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64986758223596674571779901 24370034333848752964417463)
  ·
    refine ⟨36555051500773129446626195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24370034333848752964417463 36555051500773129446626195)
    ·
      refine ⟨54832577251159694169939293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36555051500773129446626195 54832577251159694169939293)
      ·
        refine ⟨20562216469184885313727235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54832577251159694169939293 20562216469184885313727235)
        ·
          refine ⟨30843324703777327970590853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20562216469184885313727235 30843324703777327970590853)
          ·
            refine ⟨5783123381958248994485785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30843324703777327970590853 5783123381958248994485785)
            ·
              refine ⟨4337342536468686745864339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783123381958248994485785 4337342536468686745864339)
              ·
                refine ⟨6506013804703030118796509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337342536468686745864339 6506013804703030118796509)
                ·
                  refine ⟨2439755176763636294548691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506013804703030118796509 2439755176763636294548691)
                  ·
                    refine ⟨3659632765145454441823037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439755176763636294548691 3659632765145454441823037)
                    ·
                      refine ⟨1372362286929545415683639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3659632765145454441823037 1372362286929545415683639)
                      ·
                        rfl

theorem cell23_2672666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2672666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672666 prefixEnd_2672666 := by exact prefixLift 2672666
  have htrace : WordTrace (prefixWord ++ tailWord_2672666) baseStart_2672666 baseEnd_2672666 := by
    simpa [prefixWord, tailWord_2672666, baseEnd_2672666] using wordTrace_append hprefix tailTrace_2672666
  have hstable : (prefixWord ++ tailWord_2672666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672666).length < 2 ^ (prefixWord ++ tailWord_2672666).sum := by decide
  have hdescent : baseEnd_2672666 < baseStart_2672666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672686 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2672686 : Nat := 118140960795 + 2672686 * 2 ^ 59
def prefixEnd_2672686 : Nat := 4983230072969 + 3 ^ 40 * 2672686 * 2
def baseEnd_2672686 : Nat := 457457518847545112477849

theorem tailTrace_2672686 : CollatzResearch.WordTrace tailWord_2672686 prefixEnd_2672686 457457518847545112477849 := by
  unfold tailWord_2672686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185108349415319409174739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64987244530215036848931941 12185108349415319409174739)
  ·
    refine ⟨18277662524122979113762109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12185108349415319409174739 18277662524122979113762109)
    ·
      refine ⟨6854123446546117167660791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18277662524122979113762109 6854123446546117167660791)
      ·
        refine ⟨10281185169819175751491187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854123446546117167660791 10281185169819175751491187)
        ·
          refine ⟨15421777754728763627236781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10281185169819175751491187 15421777754728763627236781)
          ·
            refine ⟨5783166658023286360213793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15421777754728763627236781 5783166658023286360213793)
            ·
              refine ⟨4337374993517464770160345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783166658023286360213793 4337374993517464770160345)
              ·
                refine ⟨3253031245138098577620259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337374993517464770160345 3253031245138098577620259)
                ·
                  refine ⟨4879546867707147866430389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253031245138098577620259 4879546867707147866430389)
                  ·
                    refine ⟨457457518847545112477849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4879546867707147866430389 457457518847545112477849)
                    ·
                      rfl

theorem cell23_2672686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2672686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672686 prefixEnd_2672686 := by exact prefixLift 2672686
  have htrace : WordTrace (prefixWord ++ tailWord_2672686) baseStart_2672686 baseEnd_2672686 := by
    simpa [prefixWord, tailWord_2672686, baseEnd_2672686] using wordTrace_append hprefix tailTrace_2672686
  have hstable : (prefixWord ++ tailWord_2672686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672686).length < 2 ^ (prefixWord ++ tailWord_2672686).sum := by decide
  have hdescent : baseEnd_2672686 < baseStart_2672686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672689 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2672689 : Nat := 118140960795 + 2672689 * 2 ^ 59
def prefixEnd_2672689 : Nat := 4983230072969 + 3 ^ 40 * 2672689 * 2
def baseEnd_2672689 : Nat := 1372374096984598825696033

theorem tailTrace_2672689 : CollatzResearch.WordTrace tailWord_2672689 prefixEnd_2672689 1372374096984598825696033 := by
  unfold tailWord_2672689
  simp only [CollatzResearch.WordTrace]
  refine ⟨97480976214311686785757121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64987317476207791190504747 97480976214311686785757121)
  ·
    refine ⟨73110732160733765089317841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97480976214311686785757121 73110732160733765089317841)
    ·
      refine ⟨54833049120550323816988381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73110732160733765089317841 54833049120550323816988381)
      ·
        refine ⟨20562393420206371431370643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54833049120550323816988381 20562393420206371431370643)
        ·
          refine ⟨30843590130309557147055965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20562393420206371431370643 30843590130309557147055965)
          ·
            refine ⟨11566346298866083930145987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30843590130309557147055965 11566346298866083930145987)
            ·
              refine ⟨17349519448299125895218981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11566346298866083930145987 17349519448299125895218981)
              ·
                refine ⟨3253034896556086105353559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17349519448299125895218981 3253034896556086105353559)
                ·
                  refine ⟨4879552344834129158030339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253034896556086105353559 4879552344834129158030339)
                  ·
                    refine ⟨7319328517251193737045509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879552344834129158030339 7319328517251193737045509)
                    ·
                      refine ⟨1372374096984598825696033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7319328517251193737045509 1372374096984598825696033)
                      ·
                        rfl

theorem cell23_2672689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2672689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672689 prefixEnd_2672689 := by exact prefixLift 2672689
  have htrace : WordTrace (prefixWord ++ tailWord_2672689) baseStart_2672689 baseEnd_2672689 := by
    simpa [prefixWord, tailWord_2672689, baseEnd_2672689] using wordTrace_append hprefix tailTrace_2672689
  have hstable : (prefixWord ++ tailWord_2672689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672689).length < 2 ^ (prefixWord ++ tailWord_2672689).sum := by decide
  have hdescent : baseEnd_2672689 < baseStart_2672689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672733 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2672733 : Nat := 118140960795 + 2672733 * 2 ^ 59
def prefixEnd_2672733 : Nat := 4983230072969 + 3 ^ 40 * 2672733 * 2
def baseEnd_2672733 : Nat := 457465563377798884515277

theorem tailTrace_2672733 : CollatzResearch.WordTrace tailWord_2672733 prefixEnd_2672733 457465563377798884515277 := by
  unfold tailWord_2672733
  simp only [CollatzResearch.WordTrace]
  refine ⟨97482581026152282300358853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64988387350768188200239235 97482581026152282300358853)
  ·
    refine ⟨18277983942403552931317285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97482581026152282300358853 18277983942403552931317285)
    ·
      refine ⟨3427121989200666174621991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18277983942403552931317285 3427121989200666174621991)
      ·
        refine ⟨5140682983800999261932987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427121989200666174621991 5140682983800999261932987)
        ·
          refine ⟨7711024475701498892899481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140682983800999261932987 7711024475701498892899481)
          ·
            refine ⟨5783268356776124169674611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711024475701498892899481 5783268356776124169674611)
            ·
              refine ⟨8674902535164186254511917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783268356776124169674611 8674902535164186254511917)
              ·
                refine ⟨3253088450686569845441969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8674902535164186254511917 3253088450686569845441969)
                ·
                  refine ⟨2439816338014927384081477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253088450686569845441969 2439816338014927384081477)
                  ·
                    refine ⟨457465563377798884515277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439816338014927384081477 457465563377798884515277)
                    ·
                      rfl

theorem cell23_2672733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2672733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672733 prefixEnd_2672733 := by exact prefixLift 2672733
  have htrace : WordTrace (prefixWord ++ tailWord_2672733) baseStart_2672733 baseEnd_2672733 := by
    simpa [prefixWord, tailWord_2672733, baseEnd_2672733] using wordTrace_append hprefix tailTrace_2672733
  have hstable : (prefixWord ++ tailWord_2672733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672733).length < 2 ^ (prefixWord ++ tailWord_2672733).sum := by decide
  have hdescent : baseEnd_2672733 < baseStart_2672733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672762 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2672762 : Nat := 118140960795 + 2672762 * 2 ^ 59
def prefixEnd_2672762 : Nat := 4983230072969 + 3 ^ 40 * 2672762 * 2
def baseEnd_2672762 : Nat := 1372411581072377040083197

theorem tailTrace_2672762 : CollatzResearch.WordTrace tailWord_2672762 prefixEnd_2672762 1372411581072377040083197 := by
  unfold tailWord_2672762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370909685761805063291135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64989092495364813502109693 24370909685761805063291135)
  ·
    refine ⟨36556364528642707594936703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24370909685761805063291135 36556364528642707594936703)
    ·
      refine ⟨54834546792964061392405055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36556364528642707594936703 54834546792964061392405055)
      ·
        refine ⟨82251820189446092088607583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54834546792964061392405055 82251820189446092088607583)
        ·
          refine ⟨123377730284169138132911375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82251820189446092088607583 123377730284169138132911375)
          ·
            refine ⟨185066595426253707199367063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123377730284169138132911375 185066595426253707199367063)
            ·
              refine ⟨277599893139380560799050595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185066595426253707199367063 277599893139380560799050595)
              ·
                refine ⟨416399839709070841198575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277599893139380560799050595 416399839709070841198575893)
                ·
                  refine ⟨19518742486362695681183245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 416399839709070841198575893 19518742486362695681183245)
                  ·
                    refine ⟨7319528432386010880443717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19518742486362695681183245 7319528432386010880443717)
                    ·
                      refine ⟨1372411581072377040083197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7319528432386010880443717 1372411581072377040083197)
                      ·
                        rfl

theorem cell23_2672762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2672762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672762 prefixEnd_2672762 := by exact prefixLift 2672762
  have htrace : WordTrace (prefixWord ++ tailWord_2672762) baseStart_2672762 baseEnd_2672762 := by
    simpa [prefixWord, tailWord_2672762, baseEnd_2672762] using wordTrace_append hprefix tailTrace_2672762
  have hstable : (prefixWord ++ tailWord_2672762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672762).length < 2 ^ (prefixWord ++ tailWord_2672762).sum := by decide
  have hdescent : baseEnd_2672762 < baseStart_2672762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672773 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_2672773 : Nat := 118140960795 + 2672773 * 2 ^ 59
def prefixEnd_2672773 : Nat := 4983230072969 + 3 ^ 40 * 2672773 * 2
def baseEnd_2672773 : Nat := 1372417229359576497045647

theorem tailTrace_2672773 : CollatzResearch.WordTrace tailWord_2672773 prefixEnd_2672773 1372417229359576497045647 := by
  unfold tailWord_2672773
  simp only [CollatzResearch.WordTrace]
  refine ⟨97484039946007369131814973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64989359964004912754543315 97484039946007369131814973)
  ·
    refine ⟨36556514979752763424430615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97484039946007369131814973 36556514979752763424430615)
    ·
      refine ⟨54834772469629145136645923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36556514979752763424430615 54834772469629145136645923)
      ·
        refine ⟨82252158704443717704968885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54834772469629145136645923 82252158704443717704968885)
        ·
          refine ⟨7711139878541598534840833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82252158704443717704968885 7711139878541598534840833)
          ·
            refine ⟨5783354908906198901130625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711139878541598534840833 5783354908906198901130625)
            ·
              refine ⟨4337516181679649175847969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783354908906198901130625 4337516181679649175847969)
              ·
                refine ⟨3253137136259736881885977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337516181679649175847969 3253137136259736881885977)
                ·
                  refine ⟨2439852852194802661414483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253137136259736881885977 2439852852194802661414483)
                  ·
                    refine ⟨3659779278292203992121725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2439852852194802661414483 3659779278292203992121725)
                    ·
                      refine ⟨1372417229359576497045647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3659779278292203992121725 1372417229359576497045647)
                      ·
                        rfl

theorem cell23_2672773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_2672773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672773 prefixEnd_2672773 := by exact prefixLift 2672773
  have htrace : WordTrace (prefixWord ++ tailWord_2672773) baseStart_2672773 baseEnd_2672773 := by
    simpa [prefixWord, tailWord_2672773, baseEnd_2672773] using wordTrace_append hprefix tailTrace_2672773
  have hstable : (prefixWord ++ tailWord_2672773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672773).length < 2 ^ (prefixWord ++ tailWord_2672773).sum := by decide
  have hdescent : baseEnd_2672773 < baseStart_2672773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672813 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_2672813 : Nat := 118140960795 + 2672813 * 2 ^ 59
def prefixEnd_2672813 : Nat := 4983230072969 + 3 ^ 40 * 2672813 * 2
def baseEnd_2672813 : Nat := 1372437768585756340545463

theorem tailTrace_2672813 : CollatzResearch.WordTrace tailWord_2672813 prefixEnd_2672813 1372437768585756340545463 := by
  unfold tailWord_2672813
  simp only [CollatzResearch.WordTrace]
  refine ⟨97485498865862455963271093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64990332577241637308847395 97485498865862455963271093)
  ·
    refine ⟨9139265518674605246556665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97485498865862455963271093 9139265518674605246556665)
    ·
      refine ⟨6854449139005953934917499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9139265518674605246556665 6854449139005953934917499)
      ·
        refine ⟨10281673708508930902376249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854449139005953934917499 10281673708508930902376249)
        ·
          refine ⟨7711255281381698176782187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10281673708508930902376249 7711255281381698176782187)
          ·
            refine ⟨11566882922072547265173281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711255281381698176782187 11566882922072547265173281)
            ·
              refine ⟨8675162191554410448879961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11566882922072547265173281 8675162191554410448879961)
              ·
                refine ⟨6506371643665807836659971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8675162191554410448879961 6506371643665807836659971)
                ·
                  refine ⟨9759557465498711754989957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506371643665807836659971 9759557465498711754989957)
                  ·
                    refine ⟨1829917024781008454060617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9759557465498711754989957 1829917024781008454060617)
                    ·
                      refine ⟨1372437768585756340545463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829917024781008454060617 1372437768585756340545463)
                      ·
                        rfl

theorem cell23_2672813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_2672813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672813 prefixEnd_2672813 := by exact prefixLift 2672813
  have htrace : WordTrace (prefixWord ++ tailWord_2672813) baseStart_2672813 baseEnd_2672813 := by
    simpa [prefixWord, tailWord_2672813, baseEnd_2672813] using wordTrace_append hprefix tailTrace_2672813
  have hstable : (prefixWord ++ tailWord_2672813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672813).length < 2 ^ (prefixWord ++ tailWord_2672813).sum := by decide
  have hdescent : baseEnd_2672813 < baseStart_2672813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672817 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2672817 : Nat := 118140960795 + 2672817 * 2 ^ 59
def prefixEnd_2672817 : Nat := 4983230072969 + 3 ^ 40 * 2672817 * 2
def baseEnd_2672817 : Nat := 1372439822508374324895445

theorem tailTrace_2672817 : CollatzResearch.WordTrace tailWord_2672817 prefixEnd_2672817 1372439822508374324895445 := by
  unfold tailWord_2672817
  simp only [CollatzResearch.WordTrace]
  refine ⟨97485644757847964646416705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64990429838565309764277803 97485644757847964646416705)
  ·
    refine ⟨73114233568385973484812529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97485644757847964646416705 73114233568385973484812529)
    ·
      refine ⟨54835675176289480113609397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73114233568385973484812529 54835675176289480113609397)
      ·
        refine ⟨5140844547777138760650881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54835675176289480113609397 5140844547777138760650881)
        ·
          refine ⟨3855633410832854070488161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5140844547777138760650881 3855633410832854070488161)
          ·
            refine ⟨2891725058124640552866121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855633410832854070488161 2891725058124640552866121)
            ·
              refine ⟨2168793793593480414649591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891725058124640552866121 2168793793593480414649591)
              ·
                refine ⟨3253190690390220621974387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168793793593480414649591 3253190690390220621974387)
                ·
                  refine ⟨4879786035585330932961581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253190690390220621974387 4879786035585330932961581)
                  ·
                    refine ⟨1829919763344499099860593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4879786035585330932961581 1829919763344499099860593)
                    ·
                      refine ⟨1372439822508374324895445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829919763344499099860593 1372439822508374324895445)
                      ·
                        rfl

theorem cell23_2672817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2672817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672817 prefixEnd_2672817 := by exact prefixLift 2672817
  have htrace : WordTrace (prefixWord ++ tailWord_2672817) baseStart_2672817 baseEnd_2672817 := by
    simpa [prefixWord, tailWord_2672817, baseEnd_2672817] using wordTrace_append hprefix tailTrace_2672817
  have hstable : (prefixWord ++ tailWord_2672817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672817).length < 2 ^ (prefixWord ++ tailWord_2672817).sum := by decide
  have hdescent : baseEnd_2672817 < baseStart_2672817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672830 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2672830 : Nat := 118140960795 + 2672830 * 2 ^ 59
def prefixEnd_2672830 : Nat := 4983230072969 + 3 ^ 40 * 2672830 * 2
def baseEnd_2672830 : Nat := 1372446497756882774032885

theorem tailTrace_2672830 : CollatzResearch.WordTrace tailWord_2672830 prefixEnd_2672830 1372446497756882774032885 := by
  unfold tailWord_2672830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185764863350108483329993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64990745937867245244426629 12185764863350108483329993)
  ·
    refine ⟨9139323647512581362497495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12185764863350108483329993 9139323647512581362497495)
    ·
      refine ⟨13708985471268872043746243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139323647512581362497495 13708985471268872043746243)
      ·
        refine ⟨20563478206903308065619365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13708985471268872043746243 20563478206903308065619365)
        ·
          refine ⟨3855652163794370262303631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20563478206903308065619365 3855652163794370262303631)
          ·
            refine ⟨5783478245691555393455447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855652163794370262303631 5783478245691555393455447)
            ·
              refine ⟨8675217368537333090183171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783478245691555393455447 8675217368537333090183171)
              ·
                refine ⟨13012826052805999635274757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675217368537333090183171 13012826052805999635274757)
                ·
                  refine ⟨2439904884901124931614017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13012826052805999635274757 2439904884901124931614017)
                  ·
                    refine ⟨1829928663675843698710513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2439904884901124931614017 1829928663675843698710513)
                    ·
                      refine ⟨1372446497756882774032885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1829928663675843698710513 1372446497756882774032885)
                      ·
                        rfl

theorem cell23_2672830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2672830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672830 prefixEnd_2672830 := by exact prefixLift 2672830
  have htrace : WordTrace (prefixWord ++ tailWord_2672830) baseStart_2672830 baseEnd_2672830 := by
    simpa [prefixWord, tailWord_2672830, baseEnd_2672830] using wordTrace_append hprefix tailTrace_2672830
  have hstable : (prefixWord ++ tailWord_2672830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672830).length < 2 ^ (prefixWord ++ tailWord_2672830).sum := by decide
  have hdescent : baseEnd_2672830 < baseStart_2672830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672836 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 7]
def baseStart_2672836 : Nat := 118140960795 + 2672836 * 2 ^ 59
def prefixEnd_2672836 : Nat := 4983230072969 + 3 ^ 40 * 2672836 * 2
def baseEnd_2672836 : Nat := 152494397626756638950873

theorem tailTrace_2672836 : CollatzResearch.WordTrace tailWord_2672836 prefixEnd_2672836 152494397626756638950873 := by
  unfold tailWord_2672836
  simp only [CollatzResearch.WordTrace]
  refine ⟨48743168872389565445679181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64990891829852753927572241 48743168872389565445679181)
  ·
    refine ⟨18278688327146087042129693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48743168872389565445679181 18278688327146087042129693)
    ·
      refine ⟨6854508122679782640798635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18278688327146087042129693 6854508122679782640798635)
      ·
        refine ⟨10281762184019673961197953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854508122679782640798635 10281762184019673961197953)
        ·
          refine ⟨7711321638014755470898465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10281762184019673961197953 7711321638014755470898465)
          ·
            refine ⟨5783491228511066603173849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711321638014755470898465 5783491228511066603173849)
            ·
              refine ⟨4337618421383299952380387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783491228511066603173849 4337618421383299952380387)
              ·
                refine ⟨6506427632074949928570581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337618421383299952380387 6506427632074949928570581)
                ·
                  refine ⟨152494397626756638950873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6506427632074949928570581 152494397626756638950873)
                  ·
                    rfl

theorem cell23_2672836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_2672836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672836 prefixEnd_2672836 := by exact prefixLift 2672836
  have htrace : WordTrace (prefixWord ++ tailWord_2672836) baseStart_2672836 baseEnd_2672836 := by
    simpa [prefixWord, tailWord_2672836, baseEnd_2672836] using wordTrace_append hprefix tailTrace_2672836
  have hstable : (prefixWord ++ tailWord_2672836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672836).length < 2 ^ (prefixWord ++ tailWord_2672836).sum := by decide
  have hdescent : baseEnd_2672836 < baseStart_2672836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672846 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2672846 : Nat := 118140960795 + 2672846 * 2 ^ 59
def prefixEnd_2672846 : Nat := 4983230072969 + 3 ^ 40 * 2672846 * 2
def baseEnd_2672846 : Nat := 1372454713447354711432811

theorem tailTrace_2672846 : CollatzResearch.WordTrace tailWord_2672846 prefixEnd_2672846 1372454713447354711432811 := by
  unfold tailWord_2672846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185837809342862824902799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64991134983161935066148261 12185837809342862824902799)
  ·
    refine ⟨18278756714014294237354199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12185837809342862824902799 18278756714014294237354199)
    ·
      refine ⟨27418135071021441356031299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18278756714014294237354199 27418135071021441356031299)
      ·
        refine ⟨41127202606532162034046949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27418135071021441356031299 41127202606532162034046949)
        ·
          refine ⟨7711350488724780381383803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41127202606532162034046949 7711350488724780381383803)
          ·
            refine ⟨11567025733087170572075705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711350488724780381383803 11567025733087170572075705)
            ·
              refine ⟨8675269299815377929056779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11567025733087170572075705 8675269299815377929056779)
              ·
                refine ⟨13012903949723066893585169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675269299815377929056779 13012903949723066893585169)
                ·
                  refine ⟨9759677962292300170188877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13012903949723066893585169 9759677962292300170188877)
                  ·
                    refine ⟨3659879235859612563820829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9759677962292300170188877 3659879235859612563820829)
                    ·
                      refine ⟨1372454713447354711432811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3659879235859612563820829 1372454713447354711432811)
                      ·
                        rfl

theorem cell23_2672846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2672846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672846 prefixEnd_2672846 := by exact prefixLift 2672846
  have htrace : WordTrace (prefixWord ++ tailWord_2672846) baseStart_2672846 baseEnd_2672846 := by
    simpa [prefixWord, tailWord_2672846, baseEnd_2672846] using wordTrace_append hprefix tailTrace_2672846
  have hstable : (prefixWord ++ tailWord_2672846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672846).length < 2 ^ (prefixWord ++ tailWord_2672846).sum := by decide
  have hdescent : baseEnd_2672846 < baseStart_2672846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672886 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2672886 : Nat := 118140960795 + 2672886 * 2 ^ 59
def prefixEnd_2672886 : Nat := 4983230072969 + 3 ^ 40 * 2672886 * 2
def baseEnd_2672886 : Nat := 1372475252673534554932627

theorem tailTrace_2672886 : CollatzResearch.WordTrace tailWord_2672886 prefixEnd_2672886 1372475252673534554932627 := by
  unfold tailWord_2672886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093010087162374339417407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64992107596398659620452341 6093010087162374339417407)
  ·
    refine ⟨9139515130743561509126111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093010087162374339417407 9139515130743561509126111)
    ·
      refine ⟨13709272696115342263689167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139515130743561509126111 13709272696115342263689167)
      ·
        refine ⟨20563909044173013395533751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13709272696115342263689167 20563909044173013395533751)
        ·
          refine ⟨30845863566259520093300627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20563909044173013395533751 30845863566259520093300627)
          ·
            refine ⟨46268795349389280139950941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30845863566259520093300627 46268795349389280139950941)
            ·
              refine ⟨17350798256020980052481603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46268795349389280139950941 17350798256020980052481603)
              ·
                refine ⟨26026197384031470078722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350798256020980052481603 26026197384031470078722405)
                ·
                  refine ⟨4879912009505900639760451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26026197384031470078722405 4879912009505900639760451)
                  ·
                    refine ⟨7319868014258850959640677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879912009505900639760451 7319868014258850959640677)
                    ·
                      refine ⟨1372475252673534554932627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7319868014258850959640677 1372475252673534554932627)
                      ·
                        rfl

theorem cell23_2672886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2672886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672886 prefixEnd_2672886 := by exact prefixLift 2672886
  have htrace : WordTrace (prefixWord ++ tailWord_2672886) baseStart_2672886 baseEnd_2672886 := by
    simpa [prefixWord, tailWord_2672886, baseEnd_2672886] using wordTrace_append hprefix tailTrace_2672886
  have hstable : (prefixWord ++ tailWord_2672886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672886).length < 2 ^ (prefixWord ++ tailWord_2672886).sum := by decide
  have hdescent : baseEnd_2672886 < baseStart_2672886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672889 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2672889 : Nat := 118140960795 + 2672889 * 2 ^ 59
def prefixEnd_2672889 : Nat := 4983230072969 + 3 ^ 40 * 2672889 * 2
def baseEnd_2672889 : Nat := 1372476793115498043195113

theorem tailTrace_2672889 : CollatzResearch.WordTrace tailWord_2672889 prefixEnd_2672889 1372476793115498043195113 := by
  unfold tailWord_2672889
  simp only [CollatzResearch.WordTrace]
  refine ⟨97488270813587120943037721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64992180542391413962025147 97488270813587120943037721)
  ·
    refine ⟨73116203110190340707278291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97488270813587120943037721 73116203110190340707278291)
    ·
      refine ⟨109674304665285511060917437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73116203110190340707278291 109674304665285511060917437)
      ·
        refine ⟨41127864249482066647844039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109674304665285511060917437 41127864249482066647844039)
        ·
          refine ⟨61691796374223099971766059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41127864249482066647844039 61691796374223099971766059)
          ·
            refine ⟨92537694561334649957649089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61691796374223099971766059 92537694561334649957649089)
            ·
              refine ⟨69403270921000987468236817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92537694561334649957649089 69403270921000987468236817)
              ·
                refine ⟨52052453190750740601177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69403270921000987468236817 52052453190750740601177613)
                ·
                  refine ⟨19519669946531527725441605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52052453190750740601177613 19519669946531527725441605)
                  ·
                    refine ⟨3659938114974661448520301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19519669946531527725441605 3659938114974661448520301)
                    ·
                      refine ⟨1372476793115498043195113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3659938114974661448520301 1372476793115498043195113)
                      ·
                        rfl

theorem cell23_2672889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2672889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672889 prefixEnd_2672889 := by exact prefixLift 2672889
  have htrace : WordTrace (prefixWord ++ tailWord_2672889) baseStart_2672889 baseEnd_2672889 := by
    simpa [prefixWord, tailWord_2672889, baseEnd_2672889] using wordTrace_append hprefix tailTrace_2672889
  have hstable : (prefixWord ++ tailWord_2672889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672889).length < 2 ^ (prefixWord ++ tailWord_2672889).sum := by decide
  have hdescent : baseEnd_2672889 < baseStart_2672889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672896 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_2672896 : Nat := 118140960795 + 2672896 * 2 ^ 59
def prefixEnd_2672896 : Nat := 4983230072969 + 3 ^ 40 * 2672896 * 2
def baseEnd_2672896 : Nat := 457493462493359838602527

theorem tailTrace_2672896 : CollatzResearch.WordTrace tailWord_2672896 prefixEnd_2672896 457493462493359838602527 := by
  unfold tailWord_2672896
  simp only [CollatzResearch.WordTrace]
  refine ⟨48744263062280880569271271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64992350749707840759028361 48744263062280880569271271)
  ·
    refine ⟨73116394593421320853906907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48744263062280880569271271 73116394593421320853906907)
    ·
      refine ⟨109674591890131981280860361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73116394593421320853906907 109674591890131981280860361)
      ·
        refine ⟨82255943917598985960645271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109674591890131981280860361 82255943917598985960645271)
        ·
          refine ⟨123383915876398478940967907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82255943917598985960645271 123383915876398478940967907)
          ·
            refine ⟨185075873814597718411451861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123383915876398478940967907 185075873814597718411451861)
            ·
              refine ⟨4337715792529634025268403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185075873814597718411451861 4337715792529634025268403)
              ·
                refine ⟨6506573688794451037902605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337715792529634025268403 6506573688794451037902605)
                ·
                  refine ⟨2439965133297919139213477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506573688794451037902605 2439965133297919139213477)
                  ·
                    refine ⟨457493462493359838602527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439965133297919139213477 457493462493359838602527)
                    ·
                      rfl

theorem cell23_2672896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_2672896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672896 prefixEnd_2672896 := by exact prefixLift 2672896
  have htrace : WordTrace (prefixWord ++ tailWord_2672896) baseStart_2672896 baseEnd_2672896 := by
    simpa [prefixWord, tailWord_2672896, baseEnd_2672896] using wordTrace_append hprefix tailTrace_2672896
  have hstable : (prefixWord ++ tailWord_2672896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672896).length < 2 ^ (prefixWord ++ tailWord_2672896).sum := by decide
  have hdescent : baseEnd_2672896 < baseStart_2672896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672976 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_2672976 : Nat := 118140960795 + 2672976 * 2 ^ 59
def prefixEnd_2672976 : Nat := 4983230072969 + 3 ^ 40 * 2672976 * 2
def baseEnd_2672976 : Nat := 1372521465932439202807213

theorem tailTrace_2672976 : CollatzResearch.WordTrace tailWord_2672976 prefixEnd_2672976 1372521465932439202807213 := by
  unfold tailWord_2672976
  simp only [CollatzResearch.WordTrace]
  refine ⟨48745721982135967400727391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64994295976181289867636521 48745721982135967400727391)
  ·
    refine ⟨73118582973203951101091087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48745721982135967400727391 73118582973203951101091087)
    ·
      refine ⟨109677874459805926651636631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73118582973203951101091087 109677874459805926651636631)
      ·
        refine ⟨164516811689708889977454947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109677874459805926651636631 164516811689708889977454947)
        ·
          refine ⟨246775217534563334966182421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164516811689708889977454947 246775217534563334966182421)
          ·
            refine ⟨11567588321932656326539801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246775217534563334966182421 11567588321932656326539801)
            ·
              refine ⟨8675691241449492244904851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11567588321932656326539801 8675691241449492244904851)
              ·
                refine ⟨13013536862174238367357277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675691241449492244904851 13013536862174238367357277)
                ·
                  refine ⟨4880076323315339387758979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13013536862174238367357277 4880076323315339387758979)
                  ·
                    refine ⟨7320114484973009081638469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4880076323315339387758979 7320114484973009081638469)
                    ·
                      refine ⟨1372521465932439202807213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7320114484973009081638469 1372521465932439202807213)
                      ·
                        rfl

theorem cell23_2672976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_2672976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672976 prefixEnd_2672976 := by exact prefixLift 2672976
  have htrace : WordTrace (prefixWord ++ tailWord_2672976) baseStart_2672976 baseEnd_2672976 := by
    simpa [prefixWord, tailWord_2672976, baseEnd_2672976] using wordTrace_append hprefix tailTrace_2672976
  have hstable : (prefixWord ++ tailWord_2672976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672976).length < 2 ^ (prefixWord ++ tailWord_2672976).sum := by decide
  have hdescent : baseEnd_2672976 < baseStart_2672976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672979 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_2672979 : Nat := 118140960795 + 2672979 * 2 ^ 59
def prefixEnd_2672979 : Nat := 4983230072969 + 3 ^ 40 * 2672979 * 2
def baseEnd_2672979 : Nat := 1372523006374402691069699

theorem tailTrace_2672979 : CollatzResearch.WordTrace tailWord_2672979 prefixEnd_2672979 1372523006374402691069699 := by
  unfold tailWord_2672979
  simp only [CollatzResearch.WordTrace]
  refine ⟨97491553383261066313813991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64994368922174044209209327 97491553383261066313813991)
  ·
    refine ⟨146237330074891599470720987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97491553383261066313813991 146237330074891599470720987)
    ·
      refine ⟨219355995112337399206081481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146237330074891599470720987 219355995112337399206081481)
      ·
        refine ⟨164516996334253049404561111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219355995112337399206081481 164516996334253049404561111)
        ·
          refine ⟨246775494501379574106841667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164516996334253049404561111 246775494501379574106841667)
          ·
            refine ⟨370163241752069361160262501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246775494501379574106841667 370163241752069361160262501)
            ·
              refine ⟨69405607828513005217549219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370163241752069361160262501 69405607828513005217549219)
              ·
                refine ⟨104108411742769507826323829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69405607828513005217549219 104108411742769507826323829)
                ·
                  refine ⟨9760163600884641358717859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104108411742769507826323829 9760163600884641358717859)
                  ·
                    refine ⟨14640245401326962038076789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9760163600884641358717859 14640245401326962038076789)
                    ·
                      refine ⟨1372523006374402691069699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14640245401326962038076789 1372523006374402691069699)
                      ·
                        rfl

theorem cell23_2672979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_2672979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672979 prefixEnd_2672979 := by exact prefixLift 2672979
  have htrace : WordTrace (prefixWord ++ tailWord_2672979) baseStart_2672979 baseEnd_2672979 := by
    simpa [prefixWord, tailWord_2672979, baseEnd_2672979] using wordTrace_append hprefix tailTrace_2672979
  have hstable : (prefixWord ++ tailWord_2672979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672979).length < 2 ^ (prefixWord ++ tailWord_2672979).sum := by decide
  have hdescent : baseEnd_2672979 < baseStart_2672979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672980 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_2672980 : Nat := 118140960795 + 2672980 * 2 ^ 59
def prefixEnd_2672980 : Nat := 4983230072969 + 3 ^ 40 * 2672980 * 2
def baseEnd_2672980 : Nat := 1372523519855057187157195

theorem tailTrace_2672980 : CollatzResearch.WordTrace tailWord_2672980 prefixEnd_2672980 1372523519855057187157195 := by
  unfold tailWord_2672980
  simp only [CollatzResearch.WordTrace]
  refine ⟨48745794928128721742300197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64994393237504962323066929 48745794928128721742300197)
  ·
    refine ⟨9139836549024135326681287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48745794928128721742300197 9139836549024135326681287)
    ·
      refine ⟨13709754823536202990021931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139836549024135326681287 13709754823536202990021931)
      ·
        refine ⟨20564632235304304485032897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13709754823536202990021931 20564632235304304485032897)
        ·
          refine ⟨15423474176478228363774673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20564632235304304485032897 15423474176478228363774673)
          ·
            refine ⟨11567605632358671272831005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15423474176478228363774673 11567605632358671272831005)
            ·
              refine ⟨4337852112134501727311627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11567605632358671272831005 4337852112134501727311627)
              ·
                refine ⟨6506778168201752590967441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337852112134501727311627 6506778168201752590967441)
                ·
                  refine ⟨4880083626151314443225581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6506778168201752590967441 4880083626151314443225581)
                  ·
                    refine ⟨1830031359806742916209593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4880083626151314443225581 1830031359806742916209593)
                    ·
                      refine ⟨1372523519855057187157195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830031359806742916209593 1372523519855057187157195)
                      ·
                        rfl

theorem cell23_2672980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_2672980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672980 prefixEnd_2672980 := by exact prefixLift 2672980
  have htrace : WordTrace (prefixWord ++ tailWord_2672980) baseStart_2672980 baseEnd_2672980 := by
    simpa [prefixWord, tailWord_2672980, baseEnd_2672980] using wordTrace_append hprefix tailTrace_2672980
  have hstable : (prefixWord ++ tailWord_2672980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672980).length < 2 ^ (prefixWord ++ tailWord_2672980).sum := by decide
  have hdescent : baseEnd_2672980 < baseStart_2672980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672986 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_2672986 : Nat := 118140960795 + 2672986 * 2 ^ 59
def prefixEnd_2672986 : Nat := 4983230072969 + 3 ^ 40 * 2672986 * 2
def baseEnd_2672986 : Nat := 457508866912994721227389

theorem tailTrace_2672986 : CollatzResearch.WordTrace tailWord_2672986 prefixEnd_2672986 457508866912994721227389 := by
  unfold tailWord_2672986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372952173558926627329703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64994539129490471006212541 24372952173558926627329703)
  ·
    refine ⟨36559428260338389940994555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24372952173558926627329703 36559428260338389940994555)
    ·
      refine ⟨54839142390507584911491833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36559428260338389940994555 54839142390507584911491833)
      ·
        refine ⟨41129356792880688683618875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54839142390507584911491833 41129356792880688683618875)
        ·
          refine ⟨61694035189321033025428313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41129356792880688683618875 61694035189321033025428313)
          ·
            refine ⟨46270526391990774769071235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61694035189321033025428313 46270526391990774769071235)
            ·
              refine ⟨69405789587986162153606853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46270526391990774769071235 69405789587986162153606853)
              ·
                refine ⟨13013585547747405403801285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69405789587986162153606853 13013585547747405403801285)
                ·
                  refine ⟨2440047290202638513212741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13013585547747405403801285 2440047290202638513212741)
                  ·
                    refine ⟨457508866912994721227389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440047290202638513212741 457508866912994721227389)
                    ·
                      rfl

theorem cell23_2672986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_2672986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672986 prefixEnd_2672986 := by exact prefixLift 2672986
  have htrace : WordTrace (prefixWord ++ tailWord_2672986) baseStart_2672986 baseEnd_2672986 := by
    simpa [prefixWord, tailWord_2672986, baseEnd_2672986] using wordTrace_append hprefix tailTrace_2672986
  have hstable : (prefixWord ++ tailWord_2672986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672986).length < 2 ^ (prefixWord ++ tailWord_2672986).sum := by decide
  have hdescent : baseEnd_2672986 < baseStart_2672986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2672996 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2672996 : Nat := 118140960795 + 2672996 * 2 ^ 59
def prefixEnd_2672996 : Nat := 4983230072969 + 3 ^ 40 * 2672996 * 2
def baseEnd_2672996 : Nat := 1372531735545529124557121

theorem tailTrace_2672996 : CollatzResearch.WordTrace tailWord_2672996 prefixEnd_2672996 1372531735545529124557121 := by
  unfold tailWord_2672996
  simp only [CollatzResearch.WordTrace]
  refine ⟨48746086712099739108591421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64994782282799652144788561 48746086712099739108591421)
  ·
    refine ⟨18279782517037402165721783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48746086712099739108591421 18279782517037402165721783)
    ·
      refine ⟨27419673775556103248582675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279782517037402165721783 27419673775556103248582675)
      ·
        refine ⟨41129510663334154872874013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419673775556103248582675 41129510663334154872874013)
        ·
          refine ⟨15423566498750308077327755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41129510663334154872874013 15423566498750308077327755)
          ·
            refine ⟨23135349748125462115991633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15423566498750308077327755 23135349748125462115991633)
            ·
              refine ⟨17351512311094096586993725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23135349748125462115991633 17351512311094096586993725)
              ·
                refine ⟨6506817116660286220122647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17351512311094096586993725 6506817116660286220122647)
                ·
                  refine ⟨9760225674990429330183971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506817116660286220122647 9760225674990429330183971)
                  ·
                    refine ⟨14640338512485643995275957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9760225674990429330183971 14640338512485643995275957)
                    ·
                      refine ⟨1372531735545529124557121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14640338512485643995275957 1372531735545529124557121)
                      ·
                        rfl

theorem cell23_2672996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2672996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2672996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2672996 prefixEnd_2672996 := by exact prefixLift 2672996
  have htrace : WordTrace (prefixWord ++ tailWord_2672996) baseStart_2672996 baseEnd_2672996 := by
    simpa [prefixWord, tailWord_2672996, baseEnd_2672996] using wordTrace_append hprefix tailTrace_2672996
  have hstable : (prefixWord ++ tailWord_2672996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2672996).length < 2 ^ (prefixWord ++ tailWord_2672996).sum := by decide
  have hdescent : baseEnd_2672996 < baseStart_2672996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2672996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2673009 : Nat := 118140960795 + 2673009 * 2 ^ 59
def prefixEnd_2673009 : Nat := 4983230072969 + 3 ^ 40 * 2673009 * 2
def baseEnd_2673009 : Nat := 1372538410794037573694561

theorem tailTrace_2673009 : CollatzResearch.WordTrace tailWord_2673009 prefixEnd_2673009 1372538410794037573694561 := by
  unfold tailWord_2673009
  simp only [CollatzResearch.WordTrace]
  refine ⟨97492647573152381437406081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64995098382101587624937387 97492647573152381437406081)
  ·
    refine ⟨73119485679864286078054561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97492647573152381437406081 73119485679864286078054561)
    ·
      refine ⟨54839614259898214558540921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73119485679864286078054561 54839614259898214558540921)
      ·
        refine ⟨41129710694923660918905691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54839614259898214558540921 41129710694923660918905691)
        ·
          refine ⟨61694566042385491378358537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41129710694923660918905691 61694566042385491378358537)
          ·
            refine ⟨46270924531789118533768903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61694566042385491378358537 46270924531789118533768903)
            ·
              refine ⟨69406386797683677800653355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46270924531789118533768903 69406386797683677800653355)
              ·
                refine ⟨104109580196525516700980033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69406386797683677800653355 104109580196525516700980033)
                ·
                  refine ⟨78082185147394137525735025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104109580196525516700980033 78082185147394137525735025)
                  ·
                    refine ⟨58561638860545603144301269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78082185147394137525735025 58561638860545603144301269)
                    ·
                      refine ⟨1372538410794037573694561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58561638860545603144301269 1372538410794037573694561)
                      ·
                        rfl

theorem cell23_2673009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2673009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673009 prefixEnd_2673009 := by exact prefixLift 2673009
  have htrace : WordTrace (prefixWord ++ tailWord_2673009) baseStart_2673009 baseEnd_2673009 := by
    simpa [prefixWord, tailWord_2673009, baseEnd_2673009] using wordTrace_append hprefix tailTrace_2673009
  have hstable : (prefixWord ++ tailWord_2673009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673009).length < 2 ^ (prefixWord ++ tailWord_2673009).sum := by decide
  have hdescent : baseEnd_2673009 < baseStart_2673009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673010 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_2673010 : Nat := 118140960795 + 2673010 * 2 ^ 59
def prefixEnd_2673010 : Nat := 4983230072969 + 3 ^ 40 * 2673010 * 2
def baseEnd_2673010 : Nat := 1372538924274692069782057

theorem tailTrace_2673010 : CollatzResearch.WordTrace tailWord_2673010 prefixEnd_2673010 1372538924274692069782057 := by
  unfold tailWord_2673010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373171011537189652048121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64995122697432505738794989 24373171011537189652048121)
  ·
    refine ⟨18279878258652892239036091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24373171011537189652048121 18279878258652892239036091)
    ·
      refine ⟨27419817387979338358554137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279878258652892239036091 27419817387979338358554137)
      ·
        refine ⟨20564863040984503768915603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27419817387979338358554137 20564863040984503768915603)
        ·
          refine ⟨30847294561476755653373405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20564863040984503768915603 30847294561476755653373405)
          ·
            refine ⟨11567735460553783370015027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30847294561476755653373405 11567735460553783370015027)
            ·
              refine ⟨17351603190830675055022541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11567735460553783370015027 17351603190830675055022541)
              ·
                refine ⟨6506851196561503145633453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17351603190830675055022541 6506851196561503145633453)
                ·
                  refine ⟨2440069198710563679612545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506851196561503145633453 2440069198710563679612545)
                  ·
                    refine ⟨1830051899032922759709409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2440069198710563679612545 1830051899032922759709409)
                    ·
                      refine ⟨1372538924274692069782057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830051899032922759709409 1372538924274692069782057)
                      ·
                        rfl

theorem cell23_2673010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_2673010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673010 prefixEnd_2673010 := by exact prefixLift 2673010
  have htrace : WordTrace (prefixWord ++ tailWord_2673010) baseStart_2673010 baseEnd_2673010 := by
    simpa [prefixWord, tailWord_2673010, baseEnd_2673010] using wordTrace_append hprefix tailTrace_2673010
  have hstable : (prefixWord ++ tailWord_2673010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673010).length < 2 ^ (prefixWord ++ tailWord_2673010).sum := by decide
  have hdescent : baseEnd_2673010 < baseStart_2673010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673013 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2673013 : Nat := 118140960795 + 2673013 * 2 ^ 59
def prefixEnd_2673013 : Nat := 4983230072969 + 3 ^ 40 * 2673013 * 2
def baseEnd_2673013 : Nat := 1372540464716655558044543

theorem tailTrace_2673013 : CollatzResearch.WordTrace tailWord_2673013 prefixEnd_2673013 1372540464716655558044543 := by
  unfold tailWord_2673013
  simp only [CollatzResearch.WordTrace]
  refine ⟨97492793465137890120551693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64995195643425260080367795 97492793465137890120551693)
  ·
    refine ⟨36559797549426708795206885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97492793465137890120551693 36559797549426708795206885)
    ·
      refine ⟨6854962040517507899101291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36559797549426708795206885 6854962040517507899101291)
      ·
        refine ⟨10282443060776261848651937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854962040517507899101291 10282443060776261848651937)
        ·
          refine ⟨7711832295582196386488953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10282443060776261848651937 7711832295582196386488953)
          ·
            refine ⟨5783874221686647289866715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711832295582196386488953 5783874221686647289866715)
            ·
              refine ⟨8675811332529970934800073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783874221686647289866715 8675811332529970934800073)
              ·
                refine ⟨6506858499397478201100055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8675811332529970934800073 6506858499397478201100055)
                ·
                  refine ⟨9760287749096217301650083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506858499397478201100055 9760287749096217301650083)
                  ·
                    refine ⟨14640431623644325952475125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9760287749096217301650083 14640431623644325952475125)
                    ·
                      refine ⟨1372540464716655558044543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14640431623644325952475125 1372540464716655558044543)
                      ·
                        rfl

theorem cell23_2673013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2673013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673013 prefixEnd_2673013 := by exact prefixLift 2673013
  have htrace : WordTrace (prefixWord ++ tailWord_2673013) baseStart_2673013 baseEnd_2673013 := by
    simpa [prefixWord, tailWord_2673013, baseEnd_2673013] using wordTrace_append hprefix tailTrace_2673013
  have hstable : (prefixWord ++ tailWord_2673013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673013).length < 2 ^ (prefixWord ++ tailWord_2673013).sum := by decide
  have hdescent : baseEnd_2673013 < baseStart_2673013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673033 : List Nat := [1, 2, 1, 1, 6, 3, 2, 7]
def baseStart_2673033 : Nat := 118140960795 + 2673033 * 2 ^ 59
def prefixEnd_2673033 : Nat := 4983230072969 + 3 ^ 40 * 2673033 * 2
def baseEnd_2673033 : Nat := 50835212382583165918313

theorem tailTrace_2673033 : CollatzResearch.WordTrace tailWord_2673033 prefixEnd_2673033 50835212382583165918313 := by
  unfold tailWord_2673033
  simp only [CollatzResearch.WordTrace]
  refine ⟨97493522925065433536279753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64995681950043622357519835 97493522925065433536279753)
  ·
    refine ⟨73120142193799075152209815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97493522925065433536279753 73120142193799075152209815)
    ·
      refine ⟨109680213290698612728314723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73120142193799075152209815 109680213290698612728314723)
      ·
        refine ⟨164520319936047919092472085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109680213290698612728314723 164520319936047919092472085)
        ·
          refine ⟨7711889997002246207459629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164520319936047919092472085 7711889997002246207459629)
          ·
            refine ⟨2891958748875842327797361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7711889997002246207459629 2891958748875842327797361)
            ·
              refine ⟨2168969061656881745848021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891958748875842327797361 2168969061656881745848021)
              ·
                refine ⟨50835212382583165918313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2168969061656881745848021 50835212382583165918313)
                ·
                  rfl

theorem cell23_2673033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 7].length) (baseStart_2673033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673033 prefixEnd_2673033 := by exact prefixLift 2673033
  have htrace : WordTrace (prefixWord ++ tailWord_2673033) baseStart_2673033 baseEnd_2673033 := by
    simpa [prefixWord, tailWord_2673033, baseEnd_2673033] using wordTrace_append hprefix tailTrace_2673033
  have hstable : (prefixWord ++ tailWord_2673033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673033).length < 2 ^ (prefixWord ++ tailWord_2673033).sum := by decide
  have hdescent : baseEnd_2673033 < baseStart_2673033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673077 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2673077 : Nat := 118140960795 + 2673077 * 2 ^ 59
def prefixEnd_2673077 : Nat := 4983230072969 + 3 ^ 40 * 2673077 * 2
def baseEnd_2673077 : Nat := 1372573327478543307644249

theorem tailTrace_2673077 : CollatzResearch.WordTrace tailWord_2673077 prefixEnd_2673077 1372573327478543307644249 := by
  unfold tailWord_2673077
  simp only [CollatzResearch.WordTrace]
  refine ⟨97495127736906029050881485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64996751824604019367254323 97495127736906029050881485)
  ·
    refine ⟨36560672901339760894080557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97495127736906029050881485 36560672901339760894080557)
    ·
      refine ⟨13710252338002410335280209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36560672901339760894080557 13710252338002410335280209)
      ·
        refine ⟨10282689253501807751460157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13710252338002410335280209 10282689253501807751460157)
        ·
          refine ⟨3856008470063177906797559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10282689253501807751460157 3856008470063177906797559)
          ·
            refine ⟨5784012705094766860196339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856008470063177906797559 5784012705094766860196339)
            ·
              refine ⟨8676019057642150290294509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784012705094766860196339 8676019057642150290294509)
              ·
                refine ⟨3253507146615806358860441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676019057642150290294509 3253507146615806358860441)
                ·
                  refine ⟨2440130359961854769145331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253507146615806358860441 2440130359961854769145331)
                  ·
                    refine ⟨3660195539942782153717997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2440130359961854769145331 3660195539942782153717997)
                    ·
                      refine ⟨1372573327478543307644249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3660195539942782153717997 1372573327478543307644249)
                      ·
                        rfl

theorem cell23_2673077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2673077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673077 prefixEnd_2673077 := by exact prefixLift 2673077
  have htrace : WordTrace (prefixWord ++ tailWord_2673077) baseStart_2673077 baseEnd_2673077 := by
    simpa [prefixWord, tailWord_2673077, baseEnd_2673077] using wordTrace_append hprefix tailTrace_2673077
  have hstable : (prefixWord ++ tailWord_2673077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673077).length < 2 ^ (prefixWord ++ tailWord_2673077).sum := by decide
  have hdescent : baseEnd_2673077 < baseStart_2673077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673136 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_2673136 : Nat := 118140960795 + 2673136 * 2 ^ 59
def prefixEnd_2673136 : Nat := 4983230072969 + 3 ^ 40 * 2673136 * 2
def baseEnd_2673136 : Nat := 457534540945719525602159

theorem tailTrace_2673136 : CollatzResearch.WordTrace tailWord_2673136 prefixEnd_2673136 457534540945719525602159 := by
  unfold tailWord_2673136
  simp only [CollatzResearch.WordTrace]
  refine ⟨48748639821846141063639631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64998186429128188084852841 48748639821846141063639631)
  ·
    refine ⟨73122959732769211595459447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48748639821846141063639631 73122959732769211595459447)
    ·
      refine ⟨109684439599153817393189171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73122959732769211595459447 109684439599153817393189171)
      ·
        refine ⟨164526659398730726089783757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109684439599153817393189171 164526659398730726089783757)
        ·
          refine ⟨61697497274524022283668909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164526659398730726089783757 61697497274524022283668909)
          ·
            refine ⟨23136561477946508356375841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61697497274524022283668909 23136561477946508356375841)
            ·
              refine ⟨17352421108459881267281881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23136561477946508356375841 17352421108459881267281881)
              ·
                refine ⟨13014315831344910950461411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17352421108459881267281881 13014315831344910950461411)
                ·
                  refine ⟨19521473747017366425692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13014315831344910950461411 19521473747017366425692117)
                  ·
                    refine ⟨457534540945719525602159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19521473747017366425692117 457534540945719525602159)
                    ·
                      rfl

theorem cell23_2673136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_2673136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673136 prefixEnd_2673136 := by exact prefixLift 2673136
  have htrace : WordTrace (prefixWord ++ tailWord_2673136) baseStart_2673136 baseEnd_2673136 := by
    simpa [prefixWord, tailWord_2673136, baseEnd_2673136] using wordTrace_append hprefix tailTrace_2673136
  have hstable : (prefixWord ++ tailWord_2673136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673136).length < 2 ^ (prefixWord ++ tailWord_2673136).sum := by decide
  have hdescent : baseEnd_2673136 < baseStart_2673136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673146 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2673146 : Nat := 118140960795 + 2673146 * 2 ^ 59
def prefixEnd_2673146 : Nat := 4983230072969 + 3 ^ 40 * 2673146 * 2
def baseEnd_2673146 : Nat := 1372608757643703537681431

theorem tailTrace_2673146 : CollatzResearch.WordTrace tailWord_2673146 prefixEnd_2673146 1372608757643703537681431 := by
  unfold tailWord_2673146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374411093414013458785823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64998429582437369223428861 24374411093414013458785823)
  ·
    refine ⟨36561616640121020188178735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24374411093414013458785823 36561616640121020188178735)
    ·
      refine ⟨54842424960181530282268103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36561616640121020188178735 54842424960181530282268103)
      ·
        refine ⟨82263637440272295423402155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54842424960181530282268103 82263637440272295423402155)
        ·
          refine ⟨123395456160408443135103233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82263637440272295423402155 123395456160408443135103233)
          ·
            refine ⟨92546592120306332351327425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123395456160408443135103233 92546592120306332351327425)
            ·
              refine ⟨69409944090229749263495569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92546592120306332351327425 69409944090229749263495569)
              ·
                refine ⟨52057458067672311947621677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69409944090229749263495569 52057458067672311947621677)
                ·
                  refine ⟨19521546775377116980358129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52057458067672311947621677 19521546775377116980358129)
                  ·
                    refine ⟨14641160081532837735268597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19521546775377116980358129 14641160081532837735268597)
                    ·
                      refine ⟨1372608757643703537681431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14641160081532837735268597 1372608757643703537681431)
                      ·
                        rfl

theorem cell23_2673146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2673146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673146 prefixEnd_2673146 := by exact prefixLift 2673146
  have htrace : WordTrace (prefixWord ++ tailWord_2673146) baseStart_2673146 baseEnd_2673146 := by
    simpa [prefixWord, tailWord_2673146, baseEnd_2673146] using wordTrace_append hprefix tailTrace_2673146
  have hstable : (prefixWord ++ tailWord_2673146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673146).length < 2 ^ (prefixWord ++ tailWord_2673146).sum := by decide
  have hdescent : baseEnd_2673146 < baseStart_2673146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673153 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2673153 : Nat := 118140960795 + 2673153 * 2 ^ 59
def prefixEnd_2673153 : Nat := 4983230072969 + 3 ^ 40 * 2673153 * 2
def baseEnd_2673153 : Nat := 457537450669428336764633

theorem tailTrace_2673153 : CollatzResearch.WordTrace tailWord_2673153 prefixEnd_2673153 457537450669428336764633 := by
  unfold tailWord_2673153
  simp only [CollatzResearch.WordTrace]
  refine ⟨97497899684630694030648113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64998599789753796020432075 97497899684630694030648113)
  ·
    refine ⟨73123424763473020522986085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97497899684630694030648113 73123424763473020522986085)
    ·
      refine ⟨13710642143151191348059891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73123424763473020522986085 13710642143151191348059891)
      ·
        refine ⟨20565963214726787022089837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13710642143151191348059891 20565963214726787022089837)
        ·
          refine ⟨7712236205522545133283689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20565963214726787022089837 7712236205522545133283689)
          ·
            refine ⟨5784177154141908849962767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7712236205522545133283689 5784177154141908849962767)
            ·
              refine ⟨8676265731212863274944151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784177154141908849962767 8676265731212863274944151)
              ·
                refine ⟨13014398596819294912416227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8676265731212863274944151 13014398596819294912416227)
                ·
                  refine ⟨19521597895228942368624341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13014398596819294912416227 19521597895228942368624341)
                  ·
                    refine ⟨457537450669428336764633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19521597895228942368624341 457537450669428336764633)
                    ·
                      rfl

theorem cell23_2673153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2673153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673153 prefixEnd_2673153 := by exact prefixLift 2673153
  have htrace : WordTrace (prefixWord ++ tailWord_2673153) baseStart_2673153 baseEnd_2673153 := by
    simpa [prefixWord, tailWord_2673153, baseEnd_2673153] using wordTrace_append hprefix tailTrace_2673153
  have hstable : (prefixWord ++ tailWord_2673153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673153).length < 2 ^ (prefixWord ++ tailWord_2673153).sum := by decide
  have hdescent : baseEnd_2673153 < baseStart_2673153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673173 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2673173 : Nat := 118140960795 + 2673173 * 2 ^ 59
def prefixEnd_2673173 : Nat := 4983230072969 + 3 ^ 40 * 2673173 * 2
def baseEnd_2673173 : Nat := 1372622621621374932043807

theorem tailTrace_2673173 : CollatzResearch.WordTrace tailWord_2673173 prefixEnd_2673173 1372622621621374932043807 := by
  unfold tailWord_2673173
  simp only [CollatzResearch.WordTrace]
  refine ⟨97498629144558237446376173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64999086096372158297584115 97498629144558237446376173)
  ·
    refine ⟨36561985929209339042391065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97498629144558237446376173 36561985929209339042391065)
    ·
      refine ⟨27421489446907004281793299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36561985929209339042391065 27421489446907004281793299)
      ·
        refine ⟨41132234170360506422689949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27421489446907004281793299 41132234170360506422689949)
        ·
          refine ⟨15424587813885189908508731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41132234170360506422689949 15424587813885189908508731)
          ·
            refine ⟨23136881720827784862763097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15424587813885189908508731 23136881720827784862763097)
            ·
              refine ⟨17352661290620838647072323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23136881720827784862763097 17352661290620838647072323)
              ·
                refine ⟨26028991935931257970608485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17352661290620838647072323 26028991935931257970608485)
                ·
                  refine ⟨4880435987987110869489091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26028991935931257970608485 4880435987987110869489091)
                  ·
                    refine ⟨7320653981980666304233637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4880435987987110869489091 7320653981980666304233637)
                    ·
                      refine ⟨1372622621621374932043807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7320653981980666304233637 1372622621621374932043807)
                      ·
                        rfl

theorem cell23_2673173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2673173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673173 prefixEnd_2673173 := by exact prefixLift 2673173
  have htrace : WordTrace (prefixWord ++ tailWord_2673173) baseStart_2673173 baseEnd_2673173 := by
    simpa [prefixWord, tailWord_2673173, baseEnd_2673173] using wordTrace_append hprefix tailTrace_2673173
  have hstable : (prefixWord ++ tailWord_2673173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673173).length < 2 ^ (prefixWord ++ tailWord_2673173).sum := by decide
  have hdescent : baseEnd_2673173 < baseStart_2673173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673213 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 8]
def baseStart_2673213 : Nat := 118140960795 + 2673213 * 2 ^ 59
def prefixEnd_2673213 : Nat := 4983230072969 + 3 ^ 40 * 2673213 * 2
def baseEnd_2673213 : Nat := 152515906760839419504847

theorem tailTrace_2673213 : CollatzResearch.WordTrace tailWord_2673213 prefixEnd_2673213 152515906760839419504847 := by
  unfold tailWord_2673213
  simp only [CollatzResearch.WordTrace]
  refine ⟨97500088064413324277832293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65000058709608882851888195 97500088064413324277832293)
  ·
    refine ⟨18281266512077498302093555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97500088064413324277832293 18281266512077498302093555)
    ·
      refine ⟨27421899768116247453140333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18281266512077498302093555 27421899768116247453140333)
      ·
        refine ⟨10283212413043592794927625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27421899768116247453140333 10283212413043592794927625)
        ·
          refine ⟨7712409309782694596195719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10283212413043592794927625 7712409309782694596195719)
          ·
            refine ⟨11568613964674041894293579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7712409309782694596195719 11568613964674041894293579)
            ·
              refine ⟨17352920947011062841440369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11568613964674041894293579 17352920947011062841440369)
              ·
                refine ⟨13014690710258297131080277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17352920947011062841440369 13014690710258297131080277)
                ·
                  refine ⟨152515906760839419504847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13014690710258297131080277 152515906760839419504847)
                  ·
                    rfl

theorem cell23_2673213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_2673213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673213 prefixEnd_2673213 := by exact prefixLift 2673213
  have htrace : WordTrace (prefixWord ++ tailWord_2673213) baseStart_2673213 baseEnd_2673213 := by
    simpa [prefixWord, tailWord_2673213, baseEnd_2673213] using wordTrace_append hprefix tailTrace_2673213
  have hstable : (prefixWord ++ tailWord_2673213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673213).length < 2 ^ (prefixWord ++ tailWord_2673213).sum := by decide
  have hdescent : baseEnd_2673213 < baseStart_2673213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673234 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2673234 : Nat := 118140960795 + 2673234 * 2 ^ 59
def prefixEnd_2673234 : Nat := 4983230072969 + 3 ^ 40 * 2673234 * 2
def baseEnd_2673234 : Nat := 457551314647099731127009

theorem tailTrace_2673234 : CollatzResearch.WordTrace tailWord_2673234 prefixEnd_2673234 457551314647099731127009 := by
  unfold tailWord_2673234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24375213499334311216086689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65000569331558163242897837 24375213499334311216086689)
  ·
    refine ⟨18281410124500733412065017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24375213499334311216086689 18281410124500733412065017)
    ·
      refine ⟨13711057593375550059048763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18281410124500733412065017 13711057593375550059048763)
      ·
        refine ⟨20566586390063325088573145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13711057593375550059048763 20566586390063325088573145)
        ·
          refine ⟨15424939792547493816429859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20566586390063325088573145 15424939792547493816429859)
          ·
            refine ⟨23137409688821240724644789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15424939792547493816429859 23137409688821240724644789)
            ·
              refine ⟨2169132158326991317935449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23137409688821240724644789 2169132158326991317935449)
              ·
                refine ⟨1626849118745243488451587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169132158326991317935449 1626849118745243488451587)
                ·
                  refine ⟨2440273678117865232677381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626849118745243488451587 2440273678117865232677381)
                  ·
                    refine ⟨457551314647099731127009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440273678117865232677381 457551314647099731127009)
                    ·
                      rfl

theorem cell23_2673234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2673234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673234 prefixEnd_2673234 := by exact prefixLift 2673234
  have htrace : WordTrace (prefixWord ++ tailWord_2673234) baseStart_2673234 baseEnd_2673234 := by
    simpa [prefixWord, tailWord_2673234, baseEnd_2673234] using wordTrace_append hprefix tailTrace_2673234
  have hstable : (prefixWord ++ tailWord_2673234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673234).length < 2 ^ (prefixWord ++ tailWord_2673234).sum := by decide
  have hdescent : baseEnd_2673234 < baseStart_2673234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673260 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_2673260 : Nat := 118140960795 + 2673260 * 2 ^ 59
def prefixEnd_2673260 : Nat := 4983230072969 + 3 ^ 40 * 2673260 * 2
def baseEnd_2673260 : Nat := 457555764812772030551969

theorem tailTrace_2673260 : CollatzResearch.WordTrace tailWord_2673260 prefixEnd_2673260 457555764812772030551969 := by
  unfold tailWord_2673260
  simp only [CollatzResearch.WordTrace]
  refine ⟨48750901147621525652396617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65001201530162034203195489 48750901147621525652396617)
  ·
    refine ⟨36563175860716144239297463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48750901147621525652396617 36563175860716144239297463)
    ·
      refine ⟨54844763791074216358946195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36563175860716144239297463 54844763791074216358946195)
      ·
        refine ⟨82267145686611324538419293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54844763791074216358946195 82267145686611324538419293)
        ·
          refine ⟨30850179632479246701907235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82267145686611324538419293 30850179632479246701907235)
          ·
            refine ⟨46275269448718870052860853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30850179632479246701907235 46275269448718870052860853)
            ·
              refine ⟨4338306510817394067455705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46275269448718870052860853 4338306510817394067455705)
              ·
                refine ⟨3253729883113045550591779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338306510817394067455705 3253729883113045550591779)
                ·
                  refine ⟨4880594824669568325887669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253729883113045550591779 4880594824669568325887669)
                  ·
                    refine ⟨457555764812772030551969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4880594824669568325887669 457555764812772030551969)
                    ·
                      rfl

theorem cell23_2673260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_2673260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673260 prefixEnd_2673260 := by exact prefixLift 2673260
  have htrace : WordTrace (prefixWord ++ tailWord_2673260) baseStart_2673260 baseEnd_2673260 := by
    simpa [prefixWord, tailWord_2673260, baseEnd_2673260] using wordTrace_append hprefix tailTrace_2673260
  have hstable : (prefixWord ++ tailWord_2673260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673260).length < 2 ^ (prefixWord ++ tailWord_2673260).sum := by decide
  have hdescent : baseEnd_2673260 < baseStart_2673260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673273 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_2673273 : Nat := 118140960795 + 2673273 * 2 ^ 59
def prefixEnd_2673273 : Nat := 4983230072969 + 3 ^ 40 * 2673273 * 2
def baseEnd_2673273 : Nat := 457557989895608180264449

theorem tailTrace_2673273 : CollatzResearch.WordTrace tailWord_2673273 prefixEnd_2673273 457557989895608180264449 := by
  unfold tailWord_2673273
  simp only [CollatzResearch.WordTrace]
  refine ⟨97502276444195954525016473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65001517629463969683344315 97502276444195954525016473)
  ·
    refine ⟨73126707333146965893762355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97502276444195954525016473 73126707333146965893762355)
    ·
      refine ⟨109690060999720448840643533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73126707333146965893762355 109690060999720448840643533)
      ·
        refine ⟨41133772874895168315241325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109690060999720448840643533 41133772874895168315241325)
        ·
          refine ⟨15425164828085688118215497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41133772874895168315241325 15425164828085688118215497)
          ·
            refine ⟨11568873621064266088661623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15425164828085688118215497 11568873621064266088661623)
            ·
              refine ⟨17353310431596399132992435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11568873621064266088661623 17353310431596399132992435)
              ·
                refine ⟨26029965647394598699488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17353310431596399132992435 26029965647394598699488653)
                ·
                  refine ⟨9761237117772974512308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26029965647394598699488653 9761237117772974512308245)
                  ·
                    refine ⟨457557989895608180264449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9761237117772974512308245 457557989895608180264449)
                    ·
                      rfl

theorem cell23_2673273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_2673273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673273 prefixEnd_2673273 := by exact prefixLift 2673273
  have htrace : WordTrace (prefixWord ++ tailWord_2673273) baseStart_2673273 baseEnd_2673273 := by
    simpa [prefixWord, tailWord_2673273, baseEnd_2673273] using wordTrace_append hprefix tailTrace_2673273
  have hstable : (prefixWord ++ tailWord_2673273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673273).length < 2 ^ (prefixWord ++ tailWord_2673273).sum := by decide
  have hdescent : baseEnd_2673273 < baseStart_2673273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673331 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 1, 2, 2]
def baseStart_2673331 : Nat := 118140960795 + 2673331 * 2 ^ 59
def prefixEnd_2673331 : Nat := 4983230072969 + 3 ^ 40 * 2673331 * 2
def baseEnd_2673331 : Nat := 1372703751564785313868081

theorem tailTrace_2673331 : CollatzResearch.WordTrace tailWord_2673331 prefixEnd_2673331 1372703751564785313868081 := by
  unfold tailWord_2673331
  simp only [CollatzResearch.WordTrace]
  refine ⟨97504391877985830430627847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65002927918657220287085231 97504391877985830430627847)
  ·
    refine ⟨146256587816978745645941771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97504391877985830430627847 146256587816978745645941771)
    ·
      refine ⟨219384881725468118468912657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146256587816978745645941771 219384881725468118468912657)
      ·
        refine ⟨164538661294101088851684493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219384881725468118468912657 164538661294101088851684493)
        ·
          refine ⟨61701997985287908319381685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164538661294101088851684493 61701997985287908319381685)
          ·
            refine ⟨5784562311120741404942033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61701997985287908319381685 5784562311120741404942033)
            ·
              refine ⟨4338421733340556053706525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5784562311120741404942033 4338421733340556053706525)
              ·
                refine ⟨1626908150002708520139947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4338421733340556053706525 1626908150002708520139947)
                ·
                  refine ⟨2440362225004062780209921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626908150002708520139947 2440362225004062780209921)
                  ·
                    refine ⟨1830271668753047085157441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2440362225004062780209921 1830271668753047085157441)
                    ·
                      refine ⟨1372703751564785313868081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830271668753047085157441 1372703751564785313868081)
                      ·
                        rfl

theorem cell23_2673331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 2, 2].length) (baseStart_2673331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673331 prefixEnd_2673331 := by exact prefixLift 2673331
  have htrace : WordTrace (prefixWord ++ tailWord_2673331) baseStart_2673331 baseEnd_2673331 := by
    simpa [prefixWord, tailWord_2673331, baseEnd_2673331] using wordTrace_append hprefix tailTrace_2673331
  have hstable : (prefixWord ++ tailWord_2673331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673331).length < 2 ^ (prefixWord ++ tailWord_2673331).sum := by decide
  have hdescent : baseEnd_2673331 < baseStart_2673331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673390 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2673390 : Nat := 118140960795 + 2673390 * 2 ^ 59
def prefixEnd_2673390 : Nat := 4983230072969 + 3 ^ 40 * 2673390 * 2
def baseEnd_2673390 : Nat := 1372734046923400583030309

theorem tailTrace_2673390 : CollatzResearch.WordTrace tailWord_2673390 prefixEnd_2673390 1372734046923400583030309 := by
  unfold tailWord_2673390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188317973096510438378203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65004362523181389004683749 12188317973096510438378203)
  ·
    refine ⟨18282476959644765657567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12188317973096510438378203 18282476959644765657567305)
    ·
      refine ⟨13711857719733574243175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18282476959644765657567305 13711857719733574243175479)
      ·
        refine ⟨20567786579600361364763219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13711857719733574243175479 20567786579600361364763219)
        ·
          refine ⟨30851679869400542047144829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20567786579600361364763219 30851679869400542047144829)
          ·
            refine ⟨11569379951025203267679311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30851679869400542047144829 11569379951025203267679311)
            ·
              refine ⟨17354069926537804901518967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11569379951025203267679311 17354069926537804901518967)
              ·
                refine ⟨26031104889806707352278451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17354069926537804901518967 26031104889806707352278451)
                ·
                  refine ⟨39046657334710061028417677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26031104889806707352278451 39046657334710061028417677)
                  ·
                    refine ⟨14642496500516272885656629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39046657334710061028417677 14642496500516272885656629)
                    ·
                      refine ⟨1372734046923400583030309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14642496500516272885656629 1372734046923400583030309)
                      ·
                        rfl

theorem cell23_2673390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2673390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673390 prefixEnd_2673390 := by exact prefixLift 2673390
  have htrace : WordTrace (prefixWord ++ tailWord_2673390) baseStart_2673390 baseEnd_2673390 := by
    simpa [prefixWord, tailWord_2673390, baseEnd_2673390] using wordTrace_append hprefix tailTrace_2673390
  have hstable : (prefixWord ++ tailWord_2673390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673390).length < 2 ^ (prefixWord ++ tailWord_2673390).sum := by decide
  have hdescent : baseEnd_2673390 < baseStart_2673390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673404 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_2673404 : Nat := 118140960795 + 2673404 * 2 ^ 59
def prefixEnd_2673404 : Nat := 4983230072969 + 3 ^ 40 * 2673404 * 2
def baseEnd_2673404 : Nat := 1372741235652563528255245

theorem tailTrace_2673404 : CollatzResearch.WordTrace tailWord_2673404 prefixEnd_2673404 1372741235652563528255245 := by
  unfold tailWord_2673404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48753527203360681949017633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65004702937814242598690177 48753527203360681949017633)
  ·
    refine ⟨36565145402520511461763225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48753527203360681949017633 36565145402520511461763225)
    ·
      refine ⟨27423859051890383596322419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36565145402520511461763225 27423859051890383596322419)
      ·
        refine ⟨41135788577835575394483629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27423859051890383596322419 41135788577835575394483629)
        ·
          refine ⟨15425920716688340772931361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41135788577835575394483629 15425920716688340772931361)
          ·
            refine ⟨11569440537516255579698521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15425920716688340772931361 11569440537516255579698521)
            ·
              refine ⟨8677080403137191684773891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569440537516255579698521 8677080403137191684773891)
              ·
                refine ⟨13015620604705787527160837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677080403137191684773891 13015620604705787527160837)
                ·
                  refine ⟨2440428863382335161342657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13015620604705787527160837 2440428863382335161342657)
                  ·
                    refine ⟨1830321647536751371006993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2440428863382335161342657 1830321647536751371006993)
                    ·
                      refine ⟨1372741235652563528255245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830321647536751371006993 1372741235652563528255245)
                      ·
                        rfl

theorem cell23_2673404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_2673404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673404 prefixEnd_2673404 := by exact prefixLift 2673404
  have htrace : WordTrace (prefixWord ++ tailWord_2673404) baseStart_2673404 baseEnd_2673404 := by
    simpa [prefixWord, tailWord_2673404, baseEnd_2673404] using wordTrace_append hprefix tailTrace_2673404
  have hstable : (prefixWord ++ tailWord_2673404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673404).length < 2 ^ (prefixWord ++ tailWord_2673404).sum := by decide
  have hdescent : baseEnd_2673404 < baseStart_2673404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673420 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2673420 : Nat := 118140960795 + 2673420 * 2 ^ 59
def prefixEnd_2673420 : Nat := 4983230072969 + 3 ^ 40 * 2673420 * 2
def baseEnd_2673420 : Nat := 1372749451343035465655171

theorem tailTrace_2673420 : CollatzResearch.WordTrace tailWord_2673420 prefixEnd_2673420 1372749451343035465655171 := by
  unfold tailWord_2673420
  simp only [CollatzResearch.WordTrace]
  refine ⟨48753818987331699315308857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65005091983108932420411809 48753818987331699315308857)
  ·
    refine ⟨36565364240498774486481643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48753818987331699315308857 36565364240498774486481643)
    ·
      refine ⟨54848046360748161729722465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36565364240498774486481643 54848046360748161729722465)
      ·
        refine ⟨41136034770561121297291849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54848046360748161729722465 41136034770561121297291849)
        ·
          refine ⟨30852026077920840972968887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41136034770561121297291849 30852026077920840972968887)
          ·
            refine ⟨46278039116881261459453331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30852026077920840972968887 46278039116881261459453331)
            ·
              refine ⟨69417058675321892189179997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46278039116881261459453331 69417058675321892189179997)
              ·
                refine ⟨26031397003245709570942499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69417058675321892189179997 26031397003245709570942499)
                ·
                  refine ⟨39047095504868564356413749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26031397003245709570942499 39047095504868564356413749)
                  ·
                    refine ⟨3660665203581427908413789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39047095504868564356413749 3660665203581427908413789)
                    ·
                      refine ⟨1372749451343035465655171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3660665203581427908413789 1372749451343035465655171)
                      ·
                        rfl

theorem cell23_2673420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2673420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673420 prefixEnd_2673420 := by exact prefixLift 2673420
  have htrace : WordTrace (prefixWord ++ tailWord_2673420) baseStart_2673420 baseEnd_2673420 := by
    simpa [prefixWord, tailWord_2673420, baseEnd_2673420] using wordTrace_append hprefix tailTrace_2673420
  have hstable : (prefixWord ++ tailWord_2673420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673420).length < 2 ^ (prefixWord ++ tailWord_2673420).sum := by decide
  have hdescent : baseEnd_2673420 < baseStart_2673420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673461 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 5]
def baseStart_2673461 : Nat := 118140960795 + 2673461 * 2 ^ 59
def prefixEnd_2673461 : Nat := 4983230072969 + 3 ^ 40 * 2673461 * 2
def baseEnd_2673461 : Nat := 152530056005541089471387

theorem tailTrace_2673461 : CollatzResearch.WordTrace tailWord_2673461 prefixEnd_2673461 152530056005541089471387 := by
  unfold tailWord_2673461
  simp only [CollatzResearch.WordTrace]
  refine ⟨97509133367514862632860237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65006088911676575088573491 97509133367514862632860237)
  ·
    refine ⟨36565925012818073487322589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97509133367514862632860237 36565925012818073487322589)
    ·
      refine ⟨13712221879806777557745971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36565925012818073487322589 13712221879806777557745971)
      ·
        refine ⟨20568332819710166336618957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13712221879806777557745971 20568332819710166336618957)
        ·
          refine ⟨7713124807391312376232109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20568332819710166336618957 7713124807391312376232109)
          ·
            refine ⟨2892421802771742141087041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7713124807391312376232109 2892421802771742141087041)
            ·
              refine ⟨2169316352078806605815281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892421802771742141087041 2169316352078806605815281)
              ·
                refine ⟨1626987264059104954361461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169316352078806605815281 1626987264059104954361461)
                ·
                  refine ⟨152530056005541089471387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1626987264059104954361461 152530056005541089471387)
                  ·
                    rfl

theorem cell23_2673461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_2673461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673461 prefixEnd_2673461 := by exact prefixLift 2673461
  have htrace : WordTrace (prefixWord ++ tailWord_2673461) baseStart_2673461 baseEnd_2673461 := by
    simpa [prefixWord, tailWord_2673461, baseEnd_2673461] using wordTrace_append hprefix tailTrace_2673461
  have hstable : (prefixWord ++ tailWord_2673461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673461).length < 2 ^ (prefixWord ++ tailWord_2673461).sum := by decide
  have hdescent : baseEnd_2673461 < baseStart_2673461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673497 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2673497 : Nat := 118140960795 + 2673497 * 2 ^ 59
def prefixEnd_2673497 : Nat := 4983230072969 + 3 ^ 40 * 2673497 * 2
def baseEnd_2673497 : Nat := 1372788989353431664392317

theorem tailTrace_2673497 : CollatzResearch.WordTrace tailWord_2673497 prefixEnd_2673497 1372788989353431664392317 := by
  unfold tailWord_2673497
  simp only [CollatzResearch.WordTrace]
  refine ⟨97510446395384440781170745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65006964263589627187447163 97510446395384440781170745)
  ·
    refine ⟨73132834796538330585878059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97510446395384440781170745 73132834796538330585878059)
    ·
      refine ⟨109699252194807495878817089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73132834796538330585878059 109699252194807495878817089)
      ·
        refine ⟨82274439146105621909112817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109699252194807495878817089 82274439146105621909112817)
        ·
          refine ⟨61705829359579216431834613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82274439146105621909112817 61705829359579216431834613)
          ·
            refine ⟨5784921502460551540484495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61705829359579216431834613 5784921502460551540484495)
            ·
              refine ⟨8677382253690827310726743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784921502460551540484495 8677382253690827310726743)
              ·
                refine ⟨13016073380536240966090115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677382253690827310726743 13016073380536240966090115)
                ·
                  refine ⟨19524110070804361449135173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13016073380536240966090115 19524110070804361449135173)
                  ·
                    refine ⟨3660770638275817771712845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19524110070804361449135173 3660770638275817771712845)
                    ·
                      refine ⟨1372788989353431664392317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3660770638275817771712845 1372788989353431664392317)
                      ·
                        rfl

theorem cell23_2673497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2673497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673497 prefixEnd_2673497 := by exact prefixLift 2673497
  have htrace : WordTrace (prefixWord ++ tailWord_2673497) baseStart_2673497 baseEnd_2673497 := by
    simpa [prefixWord, tailWord_2673497, baseEnd_2673497] using wordTrace_append hprefix tailTrace_2673497
  have hstable : (prefixWord ++ tailWord_2673497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673497).length < 2 ^ (prefixWord ++ tailWord_2673497).sum := by decide
  have hdescent : baseEnd_2673497 < baseStart_2673497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673520 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_2673520 : Nat := 118140960795 + 2673520 * 2 ^ 59
def prefixEnd_2673520 : Nat := 4983230072969 + 3 ^ 40 * 2673520 * 2
def baseEnd_2673520 : Nat := 1372800799408485074404711

theorem tailTrace_2673520 : CollatzResearch.WordTrace tailWord_2673520 prefixEnd_2673520 1372800799408485074404711 := by
  unfold tailWord_2673520
  simp only [CollatzResearch.WordTrace]
  refine ⟨48755642637150557854629007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65007523516200743806172009 48755642637150557854629007)
  ·
    refine ⟨73133463955725836781943511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48755642637150557854629007 73133463955725836781943511)
    ·
      refine ⟨109700195933588755172915267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73133463955725836781943511 109700195933588755172915267)
      ·
        refine ⟨164550293900383132759372901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109700195933588755172915267 164550293900383132759372901)
        ·
          refine ⟨30853180106321837392382419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164550293900383132759372901 30853180106321837392382419)
          ·
            refine ⟨46279770159482756088573629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30853180106321837392382419 46279770159482756088573629)
            ·
              refine ⟨17354913809806033533215111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46279770159482756088573629 17354913809806033533215111)
              ·
                refine ⟨26032370714709050299822667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17354913809806033533215111 26032370714709050299822667)
                ·
                  refine ⟨39048556072063575449734001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26032370714709050299822667 39048556072063575449734001)
                  ·
                    refine ⟨29286417054047681587300501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39048556072063575449734001 29286417054047681587300501)
                    ·
                      refine ⟨1372800799408485074404711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29286417054047681587300501 1372800799408485074404711)
                      ·
                        rfl

theorem cell23_2673520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_2673520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673520 prefixEnd_2673520 := by exact prefixLift 2673520
  have htrace : WordTrace (prefixWord ++ tailWord_2673520) baseStart_2673520 baseEnd_2673520 := by
    simpa [prefixWord, tailWord_2673520, baseEnd_2673520] using wordTrace_append hprefix tailTrace_2673520
  have hstable : (prefixWord ++ tailWord_2673520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673520).length < 2 ^ (prefixWord ++ tailWord_2673520).sum := by decide
  have hdescent : baseEnd_2673520 < baseStart_2673520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673547 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 1, 5]
def baseStart_2673547 : Nat := 118140960795 + 2673547 * 2 ^ 59
def prefixEnd_2673547 : Nat := 4983230072969 + 3 ^ 40 * 2673547 * 2
def baseEnd_2673547 : Nat := 457604887795385489589029

theorem tailTrace_2673547 : CollatzResearch.WordTrace tailWord_2673547 prefixEnd_2673547 457604887795385489589029 := by
  unfold tailWord_2673547
  simp only [CollatzResearch.WordTrace]
  refine ⟨97512270045203299320490895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65008180030135532880327263 97512270045203299320490895)
  ·
    refine ⟨146268405067804948980736343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97512270045203299320490895 146268405067804948980736343)
    ·
      refine ⟨219402607601707423471104515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146268405067804948980736343 219402607601707423471104515)
      ·
        refine ⟨329103911402561135206656773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219402607601707423471104515 329103911402561135206656773)
        ·
          refine ⟨61706983387980212851248145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329103911402561135206656773 61706983387980212851248145)
          ·
            refine ⟨46280237540985159638436109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61706983387980212851248145 46280237540985159638436109)
            ·
              refine ⟨17355089077869434864413541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46280237540985159638436109 17355089077869434864413541)
              ·
                refine ⟨3254079202100519037077539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17355089077869434864413541 3254079202100519037077539)
                ·
                  refine ⟨4881118803150778555616309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254079202100519037077539 4881118803150778555616309)
                  ·
                    refine ⟨457604887795385489589029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4881118803150778555616309 457604887795385489589029)
                    ·
                      rfl

theorem cell23_2673547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 5].length) (baseStart_2673547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673547 prefixEnd_2673547 := by exact prefixLift 2673547
  have htrace : WordTrace (prefixWord ++ tailWord_2673547) baseStart_2673547 baseEnd_2673547 := by
    simpa [prefixWord, tailWord_2673547, baseEnd_2673547] using wordTrace_append hprefix tailTrace_2673547
  have hstable : (prefixWord ++ tailWord_2673547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673547).length < 2 ^ (prefixWord ++ tailWord_2673547).sum := by decide
  have hdescent : baseEnd_2673547 < baseStart_2673547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673577 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_2673577 : Nat := 118140960795 + 2673577 * 2 ^ 59
def prefixEnd_2673577 : Nat := 4983230072969 + 3 ^ 40 * 2673577 * 2
def baseEnd_2673577 : Nat := 457610022601930450463983

theorem tailTrace_2673577 : CollatzResearch.WordTrace tailWord_2673577 prefixEnd_2673577 457610022601930450463983 := by
  unfold tailWord_2673577
  simp only [CollatzResearch.WordTrace]
  refine ⟨97513364235094614444082985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65008909490063076296055323 97513364235094614444082985)
  ·
    refine ⟨73135023176320960833062239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97513364235094614444082985 73135023176320960833062239)
    ·
      refine ⟨109702534764481441249593359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73135023176320960833062239 109702534764481441249593359)
      ·
        refine ⟨164553802146722161874390039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109702534764481441249593359 164553802146722161874390039)
        ·
          refine ⟨246830703220083242811585059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164553802146722161874390039 246830703220083242811585059)
          ·
            refine ⟨370246054830124864217377589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246830703220083242811585059 370246054830124864217377589)
            ·
              refine ⟨34710567640324206020379149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370246054830124864217377589 34710567640324206020379149)
              ·
                refine ⟨13016462865121577257642181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34710567640324206020379149 13016462865121577257642181)
                ·
                  refine ⟨2440586787210295735807909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13016462865121577257642181 2440586787210295735807909)
                  ·
                    refine ⟨457610022601930450463983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440586787210295735807909 457610022601930450463983)
                    ·
                      rfl

theorem cell23_2673577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_2673577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673577 prefixEnd_2673577 := by exact prefixLift 2673577
  have htrace : WordTrace (prefixWord ++ tailWord_2673577) baseStart_2673577 baseEnd_2673577 := by
    simpa [prefixWord, tailWord_2673577, baseEnd_2673577] using wordTrace_append hprefix tailTrace_2673577
  have hstable : (prefixWord ++ tailWord_2673577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673577).length < 2 ^ (prefixWord ++ tailWord_2673577).sum := by decide
  have hdescent : baseEnd_2673577 < baseStart_2673577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673594 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_2673594 : Nat := 118140960795 + 2673594 * 2 ^ 59
def prefixEnd_2673594 : Nat := 4983230072969 + 3 ^ 40 * 2673594 * 2
def baseEnd_2673594 : Nat := 457612932325639261626457

theorem tailTrace_2673594 : CollatzResearch.WordTrace tailWord_2673594 prefixEnd_2673594 457612932325639261626457 := by
  unfold tailWord_2673594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378496069008256586862959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65009322850688684231634557 24378496069008256586862959)
  ·
    refine ⟨36567744103512384880294439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24378496069008256586862959 36567744103512384880294439)
    ·
      refine ⟨54851616155268577320441659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36567744103512384880294439 54851616155268577320441659)
      ·
        refine ⟨82277424232902865980662489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54851616155268577320441659 82277424232902865980662489)
        ·
          refine ⟨61708068174677149485496867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82277424232902865980662489 61708068174677149485496867)
          ·
            refine ⟨92562102262015724228245301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61708068174677149485496867 92562102262015724228245301)
            ·
              refine ⟨8677697087063974146397997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92562102262015724228245301 8677697087063974146397997)
              ·
                refine ⟨3254136407648990304899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8677697087063974146397997 3254136407648990304899249)
                ·
                  refine ⟨2440602305736742728674437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254136407648990304899249 2440602305736742728674437)
                  ·
                    refine ⟨457612932325639261626457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2440602305736742728674437 457612932325639261626457)
                    ·
                      rfl

theorem cell23_2673594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_2673594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673594 prefixEnd_2673594 := by exact prefixLift 2673594
  have htrace : WordTrace (prefixWord ++ tailWord_2673594) baseStart_2673594 baseEnd_2673594 := by
    simpa [prefixWord, tailWord_2673594, baseEnd_2673594] using wordTrace_append hprefix tailTrace_2673594
  have hstable : (prefixWord ++ tailWord_2673594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673594).length < 2 ^ (prefixWord ++ tailWord_2673594).sum := by decide
  have hdescent : baseEnd_2673594 < baseStart_2673594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673614 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2673614 : Nat := 118140960795 + 2673614 * 2 ^ 59
def prefixEnd_2673614 : Nat := 4983230072969 + 3 ^ 40 * 2673614 * 2
def baseEnd_2673614 : Nat := 1372849066590007706629279

theorem tailTrace_2673614 : CollatzResearch.WordTrace tailWord_2673614 prefixEnd_2673614 1372849066590007706629279 := by
  unfold tailWord_2673614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12189339216995071220397487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65009809157307046508786597 12189339216995071220397487)
  ·
    refine ⟨18284008825492606830596231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12189339216995071220397487 18284008825492606830596231)
    ·
      refine ⟨27426013238238910245894347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18284008825492606830596231 27426013238238910245894347)
      ·
        refine ⟨41139019857358365368841521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27426013238238910245894347 41139019857358365368841521)
        ·
          refine ⟨30854264893018774026631141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41139019857358365368841521 30854264893018774026631141)
          ·
            refine ⟨5785174667441020129993339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30854264893018774026631141 5785174667441020129993339)
            ·
              refine ⟨8677762001161530194990009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785174667441020129993339 8677762001161530194990009)
              ·
                refine ⟨6508321500871147646242507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8677762001161530194990009 6508321500871147646242507)
                ·
                  refine ⟨9762482251306721469363761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508321500871147646242507 9762482251306721469363761)
                  ·
                    refine ⟨7321861688480041102022821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9762482251306721469363761 7321861688480041102022821)
                    ·
                      refine ⟨1372849066590007706629279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7321861688480041102022821 1372849066590007706629279)
                      ·
                        rfl

theorem cell23_2673614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2673614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673614 prefixEnd_2673614 := by exact prefixLift 2673614
  have htrace : WordTrace (prefixWord ++ tailWord_2673614) baseStart_2673614 baseEnd_2673614 := by
    simpa [prefixWord, tailWord_2673614, baseEnd_2673614] using wordTrace_append hprefix tailTrace_2673614
  have hstable : (prefixWord ++ tailWord_2673614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673614).length < 2 ^ (prefixWord ++ tailWord_2673614).sum := by decide
  have hdescent : baseEnd_2673614 < baseStart_2673614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673618 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2673618 : Nat := 118140960795 + 2673618 * 2 ^ 59
def prefixEnd_2673618 : Nat := 4983230072969 + 3 ^ 40 * 2673618 * 2
def baseEnd_2673618 : Nat := 1372851120512625690979261

theorem tailTrace_2673618 : CollatzResearch.WordTrace tailWord_2673618 prefixEnd_2673618 1372851120512625690979261 := by
  unfold tailWord_2673618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378714906986519611581377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65009906418630718964217005 24378714906986519611581377)
  ·
    refine ⟨18284036180239889708686033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24378714906986519611581377 18284036180239889708686033)
    ·
      refine ⟨13713027135179917281514525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18284036180239889708686033 13713027135179917281514525)
      ·
        refine ⟨5142385175692468980567947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13713027135179917281514525 5142385175692468980567947)
        ·
          refine ⟨7713577763538703470851921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142385175692468980567947 7713577763538703470851921)
          ·
            refine ⟨5785183322654027603138941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7713577763538703470851921 5785183322654027603138941)
            ·
              refine ⟨2169443745995260351177103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5785183322654027603138941 2169443745995260351177103)
              ·
                refine ⟨3254165618992890526765655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169443745995260351177103 3254165618992890526765655)
                ·
                  refine ⟨4881248428489335790148483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254165618992890526765655 4881248428489335790148483)
                  ·
                    refine ⟨7321872642734003685222725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4881248428489335790148483 7321872642734003685222725)
                    ·
                      refine ⟨1372851120512625690979261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7321872642734003685222725 1372851120512625690979261)
                      ·
                        rfl

theorem cell23_2673618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2673618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673618 prefixEnd_2673618 := by exact prefixLift 2673618
  have htrace : WordTrace (prefixWord ++ tailWord_2673618) baseStart_2673618 baseEnd_2673618 := by
    simpa [prefixWord, tailWord_2673618, baseEnd_2673618] using wordTrace_append hprefix tailTrace_2673618
  have hstable : (prefixWord ++ tailWord_2673618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673618).length < 2 ^ (prefixWord ++ tailWord_2673618).sum := by decide
  have hdescent : baseEnd_2673618 < baseStart_2673618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673621 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2673621 : Nat := 118140960795 + 2673621 * 2 ^ 59
def prefixEnd_2673621 : Nat := 4983230072969 + 3 ^ 40 * 2673621 * 2
def baseEnd_2673621 : Nat := 1372852660954589179241747

theorem tailTrace_2673621 : CollatzResearch.WordTrace tailWord_2673621 prefixEnd_2673621 1372852660954589179241747 := by
  unfold tailWord_2673621
  simp only [CollatzResearch.WordTrace]
  refine ⟨97514969046935209958684717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65009979364623473305789811 97514969046935209958684717)
  ·
    refine ⟨36568113392600703734506769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97514969046935209958684717 36568113392600703734506769)
    ·
      refine ⟨27426085044450527800880077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36568113392600703734506769 27426085044450527800880077)
      ·
        refine ⟨10284781891668947925330029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27426085044450527800880077 10284781891668947925330029)
        ·
          refine ⟨3856793209375855471998761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10284781891668947925330029 3856793209375855471998761)
          ·
            refine ⟨2892594907031891603999071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3856793209375855471998761 2892594907031891603999071)
            ·
              refine ⟨4338892360547837405998607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892594907031891603999071 4338892360547837405998607)
              ·
                refine ⟨6508338540821756108997911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338892360547837405998607 6508338540821756108997911)
                ·
                  refine ⟨9762507811232634163496867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508338540821756108997911 9762507811232634163496867)
                  ·
                    refine ⟨14643761716848951245245301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9762507811232634163496867 14643761716848951245245301)
                    ·
                      refine ⟨1372852660954589179241747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14643761716848951245245301 1372852660954589179241747)
                      ·
                        rfl

theorem cell23_2673621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2673621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673621 prefixEnd_2673621 := by exact prefixLift 2673621
  have htrace : WordTrace (prefixWord ++ tailWord_2673621) baseStart_2673621 baseEnd_2673621 := by
    simpa [prefixWord, tailWord_2673621, baseEnd_2673621] using wordTrace_append hprefix tailTrace_2673621
  have hstable : (prefixWord ++ tailWord_2673621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673621).length < 2 ^ (prefixWord ++ tailWord_2673621).sum := by decide
  have hdescent : baseEnd_2673621 < baseStart_2673621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673657 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2673657 : Nat := 118140960795 + 2673657 * 2 ^ 59
def prefixEnd_2673657 : Nat := 4983230072969 + 3 ^ 40 * 2673657 * 2
def baseEnd_2673657 : Nat := 1372871146258151038391581

theorem tailTrace_2673657 : CollatzResearch.WordTrace tailWord_2673657 prefixEnd_2673657 1372871146258151038391581 := by
  unfold tailWord_2673657
  simp only [CollatzResearch.WordTrace]
  refine ⟨97516282074804788106995225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65010854716536525404663483 97516282074804788106995225)
  ·
    refine ⟨73137211556103591080246419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97516282074804788106995225 73137211556103591080246419)
    ·
      refine ⟨109705817334155386620369629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73137211556103591080246419 109705817334155386620369629)
      ·
        refine ⟨41139681500308269982638611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109705817334155386620369629 41139681500308269982638611)
        ·
          refine ⟨61709522250462404973957917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41139681500308269982638611 61709522250462404973957917)
          ·
            refine ⟨23141070843923401865234219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61709522250462404973957917 23141070843923401865234219)
            ·
              refine ⟨34711606265885102797851329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23141070843923401865234219 34711606265885102797851329)
              ·
                refine ⟨26033704699413827098388497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34711606265885102797851329 26033704699413827098388497)
                ·
                  refine ⟨19525278524560370323791373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26033704699413827098388497 19525278524560370323791373)
                  ·
                    refine ⟨7321979446710138871421765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19525278524560370323791373 7321979446710138871421765)
                    ·
                      refine ⟨1372871146258151038391581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7321979446710138871421765 1372871146258151038391581)
                      ·
                        rfl

theorem cell23_2673657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2673657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673657 prefixEnd_2673657 := by exact prefixLift 2673657
  have htrace : WordTrace (prefixWord ++ tailWord_2673657) baseStart_2673657 baseEnd_2673657 := by
    simpa [prefixWord, tailWord_2673657, baseEnd_2673657] using wordTrace_append hprefix tailTrace_2673657
  have hstable : (prefixWord ++ tailWord_2673657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673657).length < 2 ^ (prefixWord ++ tailWord_2673657).sum := by decide
  have hdescent : baseEnd_2673657 < baseStart_2673657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673661 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_2673661 : Nat := 118140960795 + 2673661 * 2 ^ 59
def prefixEnd_2673661 : Nat := 4983230072969 + 3 ^ 40 * 2673661 * 2
def baseEnd_2673661 : Nat := 1372873200180769022741563

theorem tailTrace_2673661 : CollatzResearch.WordTrace tailWord_2673661 prefixEnd_2673661 1372873200180769022741563 := by
  unfold tailWord_2673661
  simp only [CollatzResearch.WordTrace]
  refine ⟨97516427966790296790140837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65010951977860197860093891 97516427966790296790140837)
  ·
    refine ⟨18284330243773180648151407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97516427966790296790140837 18284330243773180648151407)
    ·
      refine ⟨27426495365659770972227111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18284330243773180648151407 27426495365659770972227111)
      ·
        refine ⟨41139743048489656458340667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27426495365659770972227111 41139743048489656458340667)
        ·
          refine ⟨61709614572734484687511001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41139743048489656458340667 61709614572734484687511001)
          ·
            refine ⟨46282210929550863515633251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61709614572734484687511001 46282210929550863515633251)
            ·
              refine ⟨69423316394326295273449877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46282210929550863515633251 69423316394326295273449877)
              ·
                refine ⟨3254217955984045090942963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69423316394326295273449877 3254217955984045090942963)
                ·
                  refine ⟨4881326933976067636414445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254217955984045090942963 4881326933976067636414445)
                  ·
                    refine ⟨1830497600241025363655417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4881326933976067636414445 1830497600241025363655417)
                    ·
                      refine ⟨1372873200180769022741563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830497600241025363655417 1372873200180769022741563)
                      ·
                        rfl

theorem cell23_2673661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_2673661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673661 prefixEnd_2673661 := by exact prefixLift 2673661
  have htrace : WordTrace (prefixWord ++ tailWord_2673661) baseStart_2673661 baseEnd_2673661 := by
    simpa [prefixWord, tailWord_2673661, baseEnd_2673661] using wordTrace_append hprefix tailTrace_2673661
  have hstable : (prefixWord ++ tailWord_2673661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673661).length < 2 ^ (prefixWord ++ tailWord_2673661).sum := by decide
  have hdescent : baseEnd_2673661 < baseStart_2673661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673678 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2673678 : Nat := 118140960795 + 2673678 * 2 ^ 59
def prefixEnd_2673678 : Nat := 4983230072969 + 3 ^ 40 * 2673678 * 2
def baseEnd_2673678 : Nat := 1372881929351895456228985

theorem tailTrace_2673678 : CollatzResearch.WordTrace tailWord_2673678 prefixEnd_2673678 1372881929351895456228985 := by
  unfold tailWord_2673678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12189631000966088586688711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65011365338485805795673125 12189631000966088586688711)
  ·
    refine ⟨18284446501449132880033067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12189631000966088586688711 18284446501449132880033067)
    ·
      refine ⟨27426669752173699320049601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18284446501449132880033067 27426669752173699320049601)
      ·
        refine ⟨20570002314130274490037201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27426669752173699320049601 20570002314130274490037201)
        ·
          refine ⟨15427501735597705867527901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20570002314130274490037201 15427501735597705867527901)
          ·
            refine ⟨5785313150849139700322963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15427501735597705867527901 5785313150849139700322963)
            ·
              refine ⟨8677969726273709550484445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785313150849139700322963 8677969726273709550484445)
              ·
                refine ⟨3254238647352641081431667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8677969726273709550484445 3254238647352641081431667)
                ·
                  refine ⟨4881357971028961622147501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254238647352641081431667 4881357971028961622147501)
                  ·
                    refine ⟨1830509239135860608305313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4881357971028961622147501 1830509239135860608305313)
                    ·
                      refine ⟨1372881929351895456228985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1830509239135860608305313 1372881929351895456228985)
                      ·
                        rfl

theorem cell23_2673678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2673678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673678 prefixEnd_2673678 := by exact prefixLift 2673678
  have htrace : WordTrace (prefixWord ++ tailWord_2673678) baseStart_2673678 baseEnd_2673678 := by
    simpa [prefixWord, tailWord_2673678, baseEnd_2673678] using wordTrace_append hprefix tailTrace_2673678
  have hstable : (prefixWord ++ tailWord_2673678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673678).length < 2 ^ (prefixWord ++ tailWord_2673678).sum := by decide
  have hdescent : baseEnd_2673678 < baseStart_2673678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673764 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2673764 : Nat := 118140960795 + 2673764 * 2 ^ 59
def prefixEnd_2673764 : Nat := 4983230072969 + 3 ^ 40 * 2673764 * 2
def baseEnd_2673764 : Nat := 1372926088688182119753589

theorem tailTrace_2673764 : CollatzResearch.WordTrace tailWord_2673764 prefixEnd_2673764 1372926088688182119753589 := by
  unfold tailWord_2673764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48760092342708572690570173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65013456456944763587426897 48760092342708572690570173)
  ·
    refine ⟨18285034628515714758963815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48760092342708572690570173 18285034628515714758963815)
    ·
      refine ⟨27427551942773572138445723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18285034628515714758963815 27427551942773572138445723)
      ·
        refine ⟨41141327914160358207668585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27427551942773572138445723 41141327914160358207668585)
        ·
          refine ⟨30855995935620268655751439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41141327914160358207668585 30855995935620268655751439)
          ·
            refine ⟨46283993903430402983627159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30855995935620268655751439 46283993903430402983627159)
            ·
              refine ⟨69425990855145604475440739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46283993903430402983627159 69425990855145604475440739)
              ·
                refine ⟨104138986282718406713161109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69425990855145604475440739 104138986282718406713161109)
                ·
                  refine ⟨4881514982002425314679427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104138986282718406713161109 4881514982002425314679427)
                  ·
                    refine ⟨7322272473003637972019141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4881514982002425314679427 7322272473003637972019141)
                    ·
                      refine ⟨1372926088688182119753589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7322272473003637972019141 1372926088688182119753589)
                      ·
                        rfl

theorem cell23_2673764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2673764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673764 prefixEnd_2673764 := by exact prefixLift 2673764
  have htrace : WordTrace (prefixWord ++ tailWord_2673764) baseStart_2673764 baseEnd_2673764 := by
    simpa [prefixWord, tailWord_2673764, baseEnd_2673764] using wordTrace_append hprefix tailTrace_2673764
  have hstable : (prefixWord ++ tailWord_2673764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673764).length < 2 ^ (prefixWord ++ tailWord_2673764).sum := by decide
  have hdescent : baseEnd_2673764 < baseStart_2673764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673784 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_2673784 : Nat := 118140960795 + 2673784 * 2 ^ 59
def prefixEnd_2673784 : Nat := 4983230072969 + 3 ^ 40 * 2673784 * 2
def baseEnd_2673784 : Nat := 1372936358301272041503497

theorem tailTrace_2673784 : CollatzResearch.WordTrace tailWord_2673784 prefixEnd_2673784 1372936358301272041503497 := by
  unfold tailWord_2673784
  simp only [CollatzResearch.WordTrace]
  refine ⟨48760457072672344398434203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65013942763563125864578937 48760457072672344398434203)
  ·
    refine ⟨73140685609008516597651305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48760457072672344398434203 73140685609008516597651305)
    ·
      refine ⟨54855514206756387448238479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73140685609008516597651305 54855514206756387448238479)
      ·
        refine ⟨82283271310134581172357719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54855514206756387448238479 82283271310134581172357719)
        ·
          refine ⟨123424906965201871758536579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82283271310134581172357719 123424906965201871758536579)
          ·
            refine ⟨185137360447802807637804869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123424906965201871758536579 185137360447802807637804869)
            ·
              refine ⟨34713255083963026432088413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185137360447802807637804869 34713255083963026432088413)
              ·
                refine ⟨13017470656486134912033155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34713255083963026432088413 13017470656486134912033155)
                ·
                  refine ⟨19526205984729202368049733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017470656486134912033155 19526205984729202368049733)
                  ·
                    refine ⟨3661163622136725444009325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19526205984729202368049733 3661163622136725444009325)
                    ·
                      refine ⟨1372936358301272041503497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661163622136725444009325 1372936358301272041503497)
                      ·
                        rfl

theorem cell23_2673784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_2673784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673784 prefixEnd_2673784 := by exact prefixLift 2673784
  have htrace : WordTrace (prefixWord ++ tailWord_2673784) baseStart_2673784 baseEnd_2673784 := by
    simpa [prefixWord, tailWord_2673784, baseEnd_2673784] using wordTrace_append hprefix tailTrace_2673784
  have hstable : (prefixWord ++ tailWord_2673784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673784).length < 2 ^ (prefixWord ++ tailWord_2673784).sum := by decide
  have hdescent : baseEnd_2673784 < baseStart_2673784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673787 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 10]
def baseStart_2673787 : Nat := 118140960795 + 2673787 * 2 ^ 59
def prefixEnd_2673787 : Nat := 4983230072969 + 3 ^ 40 * 2673787 * 2
def baseEnd_2673787 : Nat := 152548655415915058862887

theorem tailTrace_2673787 : CollatzResearch.WordTrace tailWord_2673787 prefixEnd_2673787 152548655415915058862887 := by
  unfold tailWord_2673787
  simp only [CollatzResearch.WordTrace]
  refine ⟨97521023564333820309227615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65014015709555880206151743 97521023564333820309227615)
  ·
    refine ⟨146281535346500730463841423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97521023564333820309227615 146281535346500730463841423)
    ·
      refine ⟨219422303019751095695762135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146281535346500730463841423 219422303019751095695762135)
      ·
        refine ⟨329133454529626643543643203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219422303019751095695762135 329133454529626643543643203)
        ·
          refine ⟨493700181794439965315464805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329133454529626643543643203 493700181794439965315464805)
          ·
            refine ⟨92568784086457493496649651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493700181794439965315464805 92568784086457493496649651)
            ·
              refine ⟨138853176129686240244974477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92568784086457493496649651 138853176129686240244974477)
              ·
                refine ⟨52069941048632340091865429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138853176129686240244974477 52069941048632340091865429)
                ·
                  refine ⟨152548655415915058862887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52069941048632340091865429 152548655415915058862887)
                  ·
                    rfl

theorem cell23_2673787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_2673787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673787 prefixEnd_2673787 := by exact prefixLift 2673787
  have htrace : WordTrace (prefixWord ++ tailWord_2673787) baseStart_2673787 baseEnd_2673787 := by
    simpa [prefixWord, tailWord_2673787, baseEnd_2673787] using wordTrace_append hprefix tailTrace_2673787
  have hstable : (prefixWord ++ tailWord_2673787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673787).length < 2 ^ (prefixWord ++ tailWord_2673787).sum := by decide
  have hdescent : baseEnd_2673787 < baseStart_2673787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673801 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_2673801 : Nat := 118140960795 + 2673801 * 2 ^ 59
def prefixEnd_2673801 : Nat := 4983230072969 + 3 ^ 40 * 2673801 * 2
def baseEnd_2673801 : Nat := 1372945087472398474990919

theorem tailTrace_2673801 : CollatzResearch.WordTrace tailWord_2673801 prefixEnd_2673801 1372945087472398474990919 := by
  unfold tailWord_2673801
  simp only [CollatzResearch.WordTrace]
  refine ⟨97521534186283100700237257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65014356124188733800158171 97521534186283100700237257)
  ·
    refine ⟨73141150639712325525177943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97521534186283100700237257 73141150639712325525177943)
    ·
      refine ⟨109711725959568488287766915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73141150639712325525177943 109711725959568488287766915)
      ·
        refine ⟨164567588939352732431650373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109711725959568488287766915 164567588939352732431650373)
        ·
          refine ⟨30856422926128637330934445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164567588939352732431650373 30856422926128637330934445)
          ·
            refine ⟨11571158597298238999100417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30856422926128637330934445 11571158597298238999100417)
            ·
              refine ⟨8678368947973679249325313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11571158597298238999100417 8678368947973679249325313)
              ·
                refine ⟨6508776710980259436993985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8678368947973679249325313 6508776710980259436993985)
                ·
                  refine ⟨4881582533235194577745489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6508776710980259436993985 4881582533235194577745489)
                  ·
                    refine ⟨3661186899926395933309117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4881582533235194577745489 3661186899926395933309117)
                    ·
                      refine ⟨1372945087472398474990919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3661186899926395933309117 1372945087472398474990919)
                      ·
                        rfl

theorem cell23_2673801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_2673801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673801 prefixEnd_2673801 := by exact prefixLift 2673801
  have htrace : WordTrace (prefixWord ++ tailWord_2673801) baseStart_2673801 baseEnd_2673801 := by
    simpa [prefixWord, tailWord_2673801, baseEnd_2673801] using wordTrace_append hprefix tailTrace_2673801
  have hstable : (prefixWord ++ tailWord_2673801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673801).length < 2 ^ (prefixWord ++ tailWord_2673801).sum := by decide
  have hdescent : baseEnd_2673801 < baseStart_2673801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2673864 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_2673864 : Nat := 118140960795 + 2673864 * 2 ^ 59
def prefixEnd_2673864 : Nat := 4983230072969 + 3 ^ 40 * 2673864 * 2
def baseEnd_2673864 : Nat := 457659145584543909501043

theorem tailTrace_2673864 : CollatzResearch.WordTrace tailWord_2673864 prefixEnd_2673864 457659145584543909501043 := by
  unfold tailWord_2673864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48761915992527431229890323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65015887990036574973187097 48761915992527431229890323)
  ·
    refine ⟨73142873988791146844835485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48761915992527431229890323 73142873988791146844835485)
    ·
      refine ⟨27428577745796680066813307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73142873988791146844835485 27428577745796680066813307)
      ·
        refine ⟨41142866618695020100219961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27428577745796680066813307 41142866618695020100219961)
        ·
          refine ⟨30857149964021265075164971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41142866618695020100219961 30857149964021265075164971)
          ·
            refine ⟨46285724946031897612747457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30857149964021265075164971 46285724946031897612747457)
            ·
              refine ⟨34714293709523923209560593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46285724946031897612747457 34714293709523923209560593)
              ·
                refine ⟨26035720282142942407170445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34714293709523923209560593 26035720282142942407170445)
                ·
                  refine ⟨9763395105803603402688917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26035720282142942407170445 9763395105803603402688917)
                  ·
                    refine ⟨457659145584543909501043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9763395105803603402688917 457659145584543909501043)
                    ·
                      rfl

theorem cell23_2673864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_2673864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2673864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2673864 prefixEnd_2673864 := by exact prefixLift 2673864
  have htrace : WordTrace (prefixWord ++ tailWord_2673864) baseStart_2673864 baseEnd_2673864 := by
    simpa [prefixWord, tailWord_2673864, baseEnd_2673864] using wordTrace_append hprefix tailTrace_2673864
  have hstable : (prefixWord ++ tailWord_2673864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2673864).length < 2 ^ (prefixWord ++ tailWord_2673864).sum := by decide
  have hdescent : baseEnd_2673864 < baseStart_2673864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2673864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
