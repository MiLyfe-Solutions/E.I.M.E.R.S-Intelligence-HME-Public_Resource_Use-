import V185TrunkScan23Chunk1310

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7764449 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_7764449 : Nat := 118140960795 + 7764449 * 2 ^ 59
def prefixEnd_7764449 : Nat := 4983230072969 + 3 ^ 40 * 7764449 * 2
def baseEnd_7764449 : Nat := 3986894354321597291279455

theorem tailTrace_7764449 : CollatzResearch.WordTrace tailWord_7764449 prefixEnd_7764449 3986894354321597291279455 := by
  unfold tailWord_7764449
  simp only [CollatzResearch.WordTrace]
  refine ⟨283192720247734810161096401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188795146831823206774064267 283192720247734810161096401)
  ·
    refine ⟨212394540185801107620822301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283192720247734810161096401 212394540185801107620822301)
    ·
      refine ⟨79647952569675415357808363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212394540185801107620822301 79647952569675415357808363)
      ·
        refine ⟨119471928854513123036712545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79647952569675415357808363 119471928854513123036712545)
        ·
          refine ⟨89603946640884842277534409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119471928854513123036712545 89603946640884842277534409)
          ·
            refine ⟨67202959980663631708150807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89603946640884842277534409 67202959980663631708150807)
            ·
              refine ⟨100804439970995447562226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67202959980663631708150807 100804439970995447562226211)
              ·
                refine ⟨151206659956493171343339317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100804439970995447562226211 151206659956493171343339317)
                ·
                  refine ⟨14175624370921234813438061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151206659956493171343339317 14175624370921234813438061)
                  ·
                    refine ⟨5315859139095463055039273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14175624370921234813438061 5315859139095463055039273)
                    ·
                      refine ⟨3986894354321597291279455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315859139095463055039273 3986894354321597291279455)
                      ·
                        rfl

theorem cell23_7764449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_7764449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764449 prefixEnd_7764449 := by exact prefixLift 7764449
  have htrace : WordTrace (prefixWord ++ tailWord_7764449) baseStart_7764449 baseEnd_7764449 := by
    simpa [prefixWord, tailWord_7764449, baseEnd_7764449] using wordTrace_append hprefix tailTrace_7764449
  have hstable : (prefixWord ++ tailWord_7764449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764449).length < 2 ^ (prefixWord ++ tailWord_7764449).sum := by decide
  have hdescent : baseEnd_7764449 < baseStart_7764449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764456 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7764456 : Nat := 118140960795 + 7764456 * 2 ^ 59
def prefixEnd_7764456 : Nat := 4983230072969 + 3 ^ 40 * 7764456 * 2
def baseEnd_7764456 : Nat := 3986897948686178763891923

theorem tailTrace_7764456 : CollatzResearch.WordTrace tailWord_7764456 prefixEnd_7764456 3986897948686178763891923 := by
  unfold tailWord_7764456
  simp only [CollatzResearch.WordTrace]
  refine ⟨141596487779354725178300611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188795317039139633571067481 141596487779354725178300611)
  ·
    refine ⟨212394731669032087767450917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141596487779354725178300611 212394731669032087767450917)
    ·
      refine ⟨39824012187943516456397047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212394731669032087767450917 39824012187943516456397047)
      ·
        refine ⟨59736018281915274684595571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39824012187943516456397047 59736018281915274684595571)
        ·
          refine ⟨89604027422872912026893357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59736018281915274684595571 89604027422872912026893357)
          ·
            refine ⟨33601510283577342010085009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89604027422872912026893357 33601510283577342010085009)
            ·
              refine ⟨25201132712683006507563757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33601510283577342010085009 25201132712683006507563757)
              ·
                refine ⟨9450424767256127440336409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25201132712683006507563757 9450424767256127440336409)
                ·
                  refine ⟨7087818575442095580252307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9450424767256127440336409 7087818575442095580252307)
                  ·
                    refine ⟨10631727863163143370378461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087818575442095580252307 10631727863163143370378461)
                    ·
                      refine ⟨3986897948686178763891923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631727863163143370378461 3986897948686178763891923)
                      ·
                        rfl

theorem cell23_7764456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7764456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764456 prefixEnd_7764456 := by exact prefixLift 7764456
  have htrace : WordTrace (prefixWord ++ tailWord_7764456) baseStart_7764456 baseEnd_7764456 := by
    simpa [prefixWord, tailWord_7764456, baseEnd_7764456] using wordTrace_append hprefix tailTrace_7764456
  have hstable : (prefixWord ++ tailWord_7764456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764456).length < 2 ^ (prefixWord ++ tailWord_7764456).sum := by decide
  have hdescent : baseEnd_7764456 < baseStart_7764456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764479 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 4, 2]
def baseStart_7764479 : Nat := 118140960795 + 7764479 * 2 ^ 59
def prefixEnd_7764479 : Nat := 4983230072969 + 3 ^ 40 * 7764479 * 2
def baseEnd_7764479 : Nat := 3986909758741232173904317

theorem tailTrace_7764479 : CollatzResearch.WordTrace tailWord_7764479 prefixEnd_7764479 3986909758741232173904317 := by
  unfold tailWord_7764479
  simp only [CollatzResearch.WordTrace]
  refine ⟨283193814437626125284688491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188795876291750750189792327 283193814437626125284688491)
  ·
    refine ⟨424790721656439187927032737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283193814437626125284688491 424790721656439187927032737)
    ·
      refine ⟨318593041242329390945274553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424790721656439187927032737 318593041242329390945274553)
      ·
        refine ⟨238944780931747043208955915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318593041242329390945274553 238944780931747043208955915)
        ·
          refine ⟨358417171397620564813433873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238944780931747043208955915 358417171397620564813433873)
          ·
            refine ⟨268812878548215423610075405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358417171397620564813433873 268812878548215423610075405)
            ·
              refine ⟨100804829455580783853778277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268812878548215423610075405 100804829455580783853778277)
              ·
                refine ⟨18900905522921396972583427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100804829455580783853778277 18900905522921396972583427)
                ·
                  refine ⟨28351358284382095458875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18900905522921396972583427 28351358284382095458875141)
                  ·
                    refine ⟨5315879678321642898539089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28351358284382095458875141 5315879678321642898539089)
                    ·
                      refine ⟨3986909758741232173904317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5315879678321642898539089 3986909758741232173904317)
                      ·
                        rfl

theorem cell23_7764479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_7764479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764479 prefixEnd_7764479 := by exact prefixLift 7764479
  have htrace : WordTrace (prefixWord ++ tailWord_7764479) baseStart_7764479 baseEnd_7764479 := by
    simpa [prefixWord, tailWord_7764479, baseEnd_7764479] using wordTrace_append hprefix tailTrace_7764479
  have hstable : (prefixWord ++ tailWord_7764479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764479).length < 2 ^ (prefixWord ++ tailWord_7764479).sum := by decide
  have hdescent : baseEnd_7764479 < baseStart_7764479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764509 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7764509 : Nat := 118140960795 + 7764509 * 2 ^ 59
def prefixEnd_7764509 : Nat := 4983230072969 + 3 ^ 40 * 7764509 * 2
def baseEnd_7764509 : Nat := 3986925163160867056529179

theorem tailTrace_7764509 : CollatzResearch.WordTrace tailWord_7764509 prefixEnd_7764509 3986925163160867056529179 := by
  unfold tailWord_7764509
  simp only [CollatzResearch.WordTrace]
  refine ⟨283194908627517440408280581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188796605751678293605520387 283194908627517440408280581)
  ·
    refine ⟨53099045367659520076552609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283194908627517440408280581 53099045367659520076552609)
    ·
      refine ⟨39824284025744640057414457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53099045367659520076552609 39824284025744640057414457)
      ·
        refine ⟨29868213019308480043060843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39824284025744640057414457 29868213019308480043060843)
        ·
          refine ⟨44802319528962720064591265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29868213019308480043060843 44802319528962720064591265)
          ·
            refine ⟨33601739646722040048443449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44802319528962720064591265 33601739646722040048443449)
            ·
              refine ⟨25201304735041530036332587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33601739646722040048443449 25201304735041530036332587)
              ·
                refine ⟨37801957102562295054498881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25201304735041530036332587 37801957102562295054498881)
                ·
                  refine ⟨28351467826921721290874161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37801957102562295054498881 28351467826921721290874161)
                  ·
                    refine ⟨21263600870191290968155621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28351467826921721290874161 21263600870191290968155621)
                    ·
                      refine ⟨3986925163160867056529179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21263600870191290968155621 3986925163160867056529179)
                      ·
                        rfl

theorem cell23_7764509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7764509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764509 prefixEnd_7764509 := by exact prefixLift 7764509
  have htrace : WordTrace (prefixWord ++ tailWord_7764509) baseStart_7764509 baseEnd_7764509 := by
    simpa [prefixWord, tailWord_7764509, baseEnd_7764509] using wordTrace_append hprefix tailTrace_7764509
  have hstable : (prefixWord ++ tailWord_7764509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764509).length < 2 ^ (prefixWord ++ tailWord_7764509).sum := by decide
  have hdescent : baseEnd_7764509 < baseStart_7764509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764549 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_7764549 : Nat := 118140960795 + 7764549 * 2 ^ 59
def prefixEnd_7764549 : Nat := 4983230072969 + 3 ^ 40 * 7764549 * 2
def baseEnd_7764549 : Nat := 1328981900795682300009665

theorem tailTrace_7764549 : CollatzResearch.WordTrace tailWord_7764549 prefixEnd_7764549 1328981900795682300009665 := by
  unfold tailWord_7764549
  simp only [CollatzResearch.WordTrace]
  refine ⟨283196367547372527239736701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188797578364915018159824467 283196367547372527239736701)
  ·
    refine ⟨106198637830264697714901263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283196367547372527239736701 106198637830264697714901263)
    ·
      refine ⟨159297956745397046572351895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106198637830264697714901263 159297956745397046572351895)
      ·
        refine ⟨238946935118095569858527843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159297956745397046572351895 238946935118095569858527843)
        ·
          refine ⟨358420402677143354787791765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238946935118095569858527843 358420402677143354787791765)
          ·
            refine ⟨16800956375491094755677739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358420402677143354787791765 16800956375491094755677739)
            ·
              refine ⟨25201434563236642133516609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16800956375491094755677739 25201434563236642133516609)
              ·
                refine ⟨18901075922427481600137457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25201434563236642133516609 18901075922427481600137457)
                ·
                  refine ⟨14175806941820611200103093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18901075922427481600137457 14175806941820611200103093)
                  ·
                    refine ⟨1328981900795682300009665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14175806941820611200103093 1328981900795682300009665)
                    ·
                      rfl

theorem cell23_7764549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_7764549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764549 prefixEnd_7764549 := by exact prefixLift 7764549
  have htrace : WordTrace (prefixWord ++ tailWord_7764549) baseStart_7764549 baseEnd_7764549 := by
    simpa [prefixWord, tailWord_7764549, baseEnd_7764549] using wordTrace_append hprefix tailTrace_7764549
  have hstable : (prefixWord ++ tailWord_7764549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764549).length < 2 ^ (prefixWord ++ tailWord_7764549).sum := by decide
  have hdescent : baseEnd_7764549 < baseStart_7764549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764579 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 5, 4]
def baseStart_7764579 : Nat := 118140960795 + 7764579 * 2 ^ 59
def prefixEnd_7764579 : Nat := 4983230072969 + 3 ^ 40 * 7764579 * 2
def baseEnd_7764579 : Nat := 1328987035602227260884619

theorem tailTrace_7764579 : CollatzResearch.WordTrace tailWord_7764579 prefixEnd_7764579 1328987035602227260884619 := by
  unfold tailWord_7764579
  simp only [CollatzResearch.WordTrace]
  refine ⟨283197461737263842363328791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188798307824842561575552527 283197461737263842363328791)
  ·
    refine ⟨424796192605895763544993187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283197461737263842363328791 424796192605895763544993187)
    ·
      refine ⟨637194288908843645317489781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424796192605895763544993187 637194288908843645317489781)
      ·
        refine ⟨59736964585204091748514667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 637194288908843645317489781 59736964585204091748514667)
        ·
          refine ⟨89605446877806137622772001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59736964585204091748514667 89605446877806137622772001)
          ·
            refine ⟨67204085158354603217079001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89605446877806137622772001 67204085158354603217079001)
            ·
              refine ⟨50403063868765952412809251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67204085158354603217079001 50403063868765952412809251)
              ·
                refine ⟨75604595803148928619213877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50403063868765952412809251 75604595803148928619213877)
                ·
                  refine ⟨7087930856545212058051301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75604595803148928619213877 7087930856545212058051301)
                  ·
                    refine ⟨1328987035602227260884619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087930856545212058051301 1328987035602227260884619)
                    ·
                      rfl

theorem cell23_7764579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 4].length) (baseStart_7764579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764579 prefixEnd_7764579 := by exact prefixLift 7764579
  have htrace : WordTrace (prefixWord ++ tailWord_7764579) baseStart_7764579 baseEnd_7764579 := by
    simpa [prefixWord, tailWord_7764579, baseEnd_7764579] using wordTrace_append hprefix tailTrace_7764579
  have hstable : (prefixWord ++ tailWord_7764579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764579).length < 2 ^ (prefixWord ++ tailWord_7764579).sum := by decide
  have hdescent : baseEnd_7764579 < baseStart_7764579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764586 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7764586 : Nat := 118140960795 + 7764586 * 2 ^ 59
def prefixEnd_7764586 : Nat := 4983230072969 + 3 ^ 40 * 7764586 * 2
def baseEnd_7764586 : Nat := 3986964701171263255266325

theorem tailTrace_7764586 : CollatzResearch.WordTrace tailWord_7764586 prefixEnd_7764586 3986964701171263255266325 := by
  unfold tailWord_7764586
  simp only [CollatzResearch.WordTrace]
  refine ⟨70799429262059620639708403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188798478032158988372555741 70799429262059620639708403)
  ·
    refine ⟨106199143893089430959562605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70799429262059620639708403 106199143893089430959562605)
    ·
      refine ⟨39824678959908536609835977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106199143893089430959562605 39824678959908536609835977)
      ·
        refine ⟨29868509219931402457376983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39824678959908536609835977 29868509219931402457376983)
        ·
          refine ⟨44802763829897103686065475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29868509219931402457376983 44802763829897103686065475)
          ·
            refine ⟨67204145744845655529098213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44802763829897103686065475 67204145744845655529098213)
            ·
              refine ⟨12600777327158560411705915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67204145744845655529098213 12600777327158560411705915)
              ·
                refine ⟨18901165990737840617558873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600777327158560411705915 18901165990737840617558873)
                ·
                  refine ⟨14175874493053380463169155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18901165990737840617558873 14175874493053380463169155)
                  ·
                    refine ⟨21263811739580070694753733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14175874493053380463169155 21263811739580070694753733)
                    ·
                      refine ⟨3986964701171263255266325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21263811739580070694753733 3986964701171263255266325)
                      ·
                        rfl

theorem cell23_7764586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7764586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764586 prefixEnd_7764586 := by exact prefixLift 7764586
  have htrace : WordTrace (prefixWord ++ tailWord_7764586) baseStart_7764586 baseEnd_7764586 := by
    simpa [prefixWord, tailWord_7764586, baseEnd_7764586] using wordTrace_append hprefix tailTrace_7764586
  have hstable : (prefixWord ++ tailWord_7764586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764586).length < 2 ^ (prefixWord ++ tailWord_7764586).sum := by decide
  have hdescent : baseEnd_7764586 < baseStart_7764586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764613 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_7764613 : Nat := 118140960795 + 7764613 * 2 ^ 59
def prefixEnd_7764613 : Nat := 4983230072969 + 3 ^ 40 * 7764613 * 2
def baseEnd_7764613 : Nat := 1328992855049644883209567

theorem tailTrace_7764613 : CollatzResearch.WordTrace tailWord_7764613 prefixEnd_7764613 1328992855049644883209567 := by
  unfold tailWord_7764613
  simp only [CollatzResearch.WordTrace]
  refine ⟨283198701819140666170066493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188799134546093777446710995 283198701819140666170066493)
  ·
    refine ⟨106199513182177749813774935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283198701819140666170066493 106199513182177749813774935)
    ·
      refine ⟨159299269773266624720662403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106199513182177749813774935 159299269773266624720662403)
      ·
        refine ⟨238948904659899937080993605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159299269773266624720662403 238948904659899937080993605)
        ·
          refine ⟨44802919623731238202686301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238948904659899937080993605 44802919623731238202686301)
          ·
            refine ⟨16801094858899214326007363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44802919623731238202686301 16801094858899214326007363)
            ·
              refine ⟨25201642288348821489011045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16801094858899214326007363 25201642288348821489011045)
              ·
                refine ⟨4725307929065404029189571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25201642288348821489011045 4725307929065404029189571)
                ·
                  refine ⟨7087961893598106043784357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725307929065404029189571 7087961893598106043784357)
                  ·
                    refine ⟨1328992855049644883209567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087961893598106043784357 1328992855049644883209567)
                    ·
                      rfl

theorem cell23_7764613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_7764613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764613 prefixEnd_7764613 := by exact prefixLift 7764613
  have htrace : WordTrace (prefixWord ++ tailWord_7764613) baseStart_7764613 baseEnd_7764613 := by
    simpa [prefixWord, tailWord_7764613, baseEnd_7764613] using wordTrace_append hprefix tailTrace_7764613
  have hstable : (prefixWord ++ tailWord_7764613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764613).length < 2 ^ (prefixWord ++ tailWord_7764613).sum := by decide
  have hdescent : baseEnd_7764613 < baseStart_7764613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764626 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_7764626 : Nat := 118140960795 + 7764626 * 2 ^ 59
def prefixEnd_7764626 : Nat := 4983230072969 + 3 ^ 40 * 7764626 * 2
def baseEnd_7764626 : Nat := 442998360044160344307349

theorem tailTrace_7764626 : CollatzResearch.WordTrace tailWord_7764626 prefixEnd_7764626 442998360044160344307349 := by
  unfold tailWord_7764626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70799793992023392347572433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188799450645395712926859821 70799793992023392347572433)
  ·
    refine ⟨53099845494017544260679325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70799793992023392347572433 53099845494017544260679325)
    ·
      refine ⟨19912442060256579097754747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53099845494017544260679325 19912442060256579097754747)
      ·
        refine ⟨29868663090384868646632121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19912442060256579097754747 29868663090384868646632121)
        ·
          refine ⟨22401497317788651484974091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29868663090384868646632121 22401497317788651484974091)
          ·
            refine ⟨33602245976682977227461137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22401497317788651484974091 33602245976682977227461137)
            ·
              refine ⟨25201684482512232920595853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33602245976682977227461137 25201684482512232920595853)
              ·
                refine ⟨9450631680942087345223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25201684482512232920595853 9450631680942087345223445)
                ·
                  refine ⟨442998360044160344307349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9450631680942087345223445 442998360044160344307349)
                  ·
                    rfl

theorem cell23_7764626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_7764626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764626 prefixEnd_7764626 := by exact prefixLift 7764626
  have htrace : WordTrace (prefixWord ++ tailWord_7764626) baseStart_7764626 baseEnd_7764626 := by
    simpa [prefixWord, tailWord_7764626, baseEnd_7764626] using wordTrace_append hprefix tailTrace_7764626
  have hstable : (prefixWord ++ tailWord_7764626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764626).length < 2 ^ (prefixWord ++ tailWord_7764626).sum := by decide
  have hdescent : baseEnd_7764626 < baseStart_7764626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764640 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3]
def baseStart_7764640 : Nat := 118140960795 + 7764640 * 2 ^ 59
def prefixEnd_7764640 : Nat := 4983230072969 + 3 ^ 40 * 7764640 * 2
def baseEnd_7764640 : Nat := 3986992429126606043991077

theorem tailTrace_7764640 : CollatzResearch.WordTrace tailWord_7764640 prefixEnd_7764640 3986992429126606043991077 := by
  unfold tailWord_7764640
  simp only [CollatzResearch.WordTrace]
  refine ⟨141599843295021424890649687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188799791060028566520866249 141599843295021424890649687)
  ·
    refine ⟨212399764942532137335974531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141599843295021424890649687 212399764942532137335974531)
    ·
      refine ⟨318599647413798206003961797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212399764942532137335974531 318599647413798206003961797)
      ·
        refine ⟨59737433890087163625742837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318599647413798206003961797 59737433890087163625742837)
        ·
          refine ⟨5600384427195671589913391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59737433890087163625742837 5600384427195671589913391)
          ·
            refine ⟨8400576640793507384870087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600384427195671589913391 8400576640793507384870087)
            ·
              refine ⟨12600864961190261077305131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8400576640793507384870087 12600864961190261077305131)
              ·
                refine ⟨18901297441785391615957697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600864961190261077305131 18901297441785391615957697)
                ·
                  refine ⟨14175973081339043711968273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18901297441785391615957697 14175973081339043711968273)
                  ·
                    refine ⟨10631979811004282783976205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14175973081339043711968273 10631979811004282783976205)
                    ·
                      refine ⟨3986992429126606043991077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10631979811004282783976205 3986992429126606043991077)
                      ·
                        rfl

theorem cell23_7764640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_7764640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764640 prefixEnd_7764640 := by exact prefixLift 7764640
  have htrace : WordTrace (prefixWord ++ tailWord_7764640) baseStart_7764640 baseEnd_7764640 := by
    simpa [prefixWord, tailWord_7764640, baseEnd_7764640] using wordTrace_append hprefix tailTrace_7764640
  have hstable : (prefixWord ++ tailWord_7764640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764640).length < 2 ^ (prefixWord ++ tailWord_7764640).sum := by decide
  have hdescent : baseEnd_7764640 < baseStart_7764640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764647 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7764647 : Nat := 118140960795 + 7764647 * 2 ^ 59
def prefixEnd_7764647 : Nat := 4983230072969 + 3 ^ 40 * 7764647 * 2
def baseEnd_7764647 : Nat := 1328998674497062505534515

theorem tailTrace_7764647 : CollatzResearch.WordTrace tailWord_7764647 prefixEnd_7764647 1328998674497062505534515 := by
  unfold tailWord_7764647
  simp only [CollatzResearch.WordTrace]
  refine ⟨283199941901017489976804195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188799961267344993317869463 283199941901017489976804195)
  ·
    refine ⟨424799912851526234965206293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283199941901017489976804195 424799912851526234965206293)
    ·
      refine ⟨19912495914915292263994045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424799912851526234965206293 19912495914915292263994045)
      ·
        refine ⟨7467185968093234598997767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19912495914915292263994045 7467185968093234598997767)
        ·
          refine ⟨11200778952139851898496651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467185968093234598997767 11200778952139851898496651)
          ·
            refine ⟨16801168428209777847744977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200778952139851898496651 16801168428209777847744977)
            ·
              refine ⟨12600876321157333385808733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16801168428209777847744977 12600876321157333385808733)
              ·
                refine ⟨4725328620434000019678275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12600876321157333385808733 4725328620434000019678275)
                ·
                  refine ⟨7087992930651000029517413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725328620434000019678275 7087992930651000029517413)
                  ·
                    refine ⟨1328998674497062505534515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7087992930651000029517413 1328998674497062505534515)
                    ·
                      rfl

theorem cell23_7764647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7764647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764647 prefixEnd_7764647 := by exact prefixLift 7764647
  have htrace : WordTrace (prefixWord ++ tailWord_7764647) baseStart_7764647 baseEnd_7764647 := by
    simpa [prefixWord, tailWord_7764647, baseEnd_7764647] using wordTrace_append hprefix tailTrace_7764647
  have hstable : (prefixWord ++ tailWord_7764647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764647).length < 2 ^ (prefixWord ++ tailWord_7764647).sum := by decide
  have hdescent : baseEnd_7764647 < baseStart_7764647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764670 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_7764670 : Nat := 118140960795 + 7764670 * 2 ^ 59
def prefixEnd_7764670 : Nat := 4983230072969 + 3 ^ 40 * 7764670 * 2
def baseEnd_7764670 : Nat := 3987007833546240926615939

theorem tailTrace_7764670 : CollatzResearch.WordTrace tailWord_7764670 prefixEnd_7764670 3987007833546240926615939 := by
  unfold tailWord_7764670
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400097597491770613111433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188800520519956109936594309 35400097597491770613111433)
  ·
    refine ⟨26550073198118827959833575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35400097597491770613111433 26550073198118827959833575)
    ·
      refine ⟨39825109797178241939750363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26550073198118827959833575 39825109797178241939750363)
      ·
        refine ⟨59737664695767362909625545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39825109797178241939750363 59737664695767362909625545)
        ·
          refine ⟨44803248521825522182219159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59737664695767362909625545 44803248521825522182219159)
          ·
            refine ⟨67204872782738283273328739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44803248521825522182219159 67204872782738283273328739)
            ·
              refine ⟨100807309174107424909993109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67204872782738283273328739 100807309174107424909993109)
              ·
                refine ⟨4725342617536285542655927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100807309174107424909993109 4725342617536285542655927)
                ·
                  refine ⟨7088013926304428313983891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725342617536285542655927 7088013926304428313983891)
                  ·
                    refine ⟨10632020889456642470975837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7088013926304428313983891 10632020889456642470975837)
                    ·
                      refine ⟨3987007833546240926615939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632020889456642470975837 3987007833546240926615939)
                      ·
                        rfl

theorem cell23_7764670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_7764670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764670 prefixEnd_7764670 := by exact prefixLift 7764670
  have htrace : WordTrace (prefixWord ++ tailWord_7764670) baseStart_7764670 baseEnd_7764670 := by
    simpa [prefixWord, tailWord_7764670, baseEnd_7764670] using wordTrace_append hprefix tailTrace_7764670
  have hstable : (prefixWord ++ tailWord_7764670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764670).length < 2 ^ (prefixWord ++ tailWord_7764670).sum := by decide
  have hdescent : baseEnd_7764670 < baseStart_7764670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764679 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_7764679 : Nat := 118140960795 + 7764679 * 2 ^ 59
def prefixEnd_7764679 : Nat := 4983230072969 + 3 ^ 40 * 7764679 * 2
def baseEnd_7764679 : Nat := 3987012454872131391403397

theorem tailTrace_7764679 : CollatzResearch.WordTrace tailWord_7764679 prefixEnd_7764679 3987012454872131391403397 := by
  unfold tailWord_7764679
  simp only [CollatzResearch.WordTrace]
  refine ⟨283201109036901559441969091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188800739357934372961312727 283201109036901559441969091)
  ·
    refine ⟨424801663555352339162953637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283201109036901559441969091 424801663555352339162953637)
    ·
      refine ⟨79650311916628563593053807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424801663555352339162953637 79650311916628563593053807)
      ·
        refine ⟨119475467874942845389580711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79650311916628563593053807 119475467874942845389580711)
        ·
          refine ⟨179213201812414268084371067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119475467874942845389580711 179213201812414268084371067)
          ·
            refine ⟨268819802718621402126556601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179213201812414268084371067 268819802718621402126556601)
            ·
              refine ⟨201614852038966051594917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268819802718621402126556601 201614852038966051594917451)
              ·
                refine ⟨302422278058449077392376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201614852038966051594917451 302422278058449077392376177)
                ·
                  refine ⟨226816708543836808044282133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302422278058449077392376177 226816708543836808044282133)
                  ·
                    refine ⟨10632033212992350377075725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226816708543836808044282133 10632033212992350377075725)
                    ·
                      refine ⟨3987012454872131391403397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632033212992350377075725 3987012454872131391403397)
                      ·
                        rfl

theorem cell23_7764679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_7764679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764679 prefixEnd_7764679 := by exact prefixLift 7764679
  have htrace : WordTrace (prefixWord ++ tailWord_7764679) baseStart_7764679 baseEnd_7764679 := by
    simpa [prefixWord, tailWord_7764679, baseEnd_7764679] using wordTrace_append hprefix tailTrace_7764679
  have hstable : (prefixWord ++ tailWord_7764679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764679).length < 2 ^ (prefixWord ++ tailWord_7764679).sum := by decide
  have hdescent : baseEnd_7764679 < baseStart_7764679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764686 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_7764686 : Nat := 118140960795 + 7764686 * 2 ^ 59
def prefixEnd_7764686 : Nat := 4983230072969 + 3 ^ 40 * 7764686 * 2
def baseEnd_7764686 : Nat := 1329005349745570954671955

theorem tailTrace_7764686 : CollatzResearch.WordTrace tailWord_7764686 prefixEnd_7764686 1329005349745570954671955 := by
  unfold tailWord_7764686
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400170543484524954684239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188800909565250799758315941 35400170543484524954684239)
  ·
    refine ⟨53100255815226787432026359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35400170543484524954684239 53100255815226787432026359)
    ·
      refine ⟨79650383722840181148039539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53100255815226787432026359 79650383722840181148039539)
      ·
        refine ⟨119475575584260271722059309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79650383722840181148039539 119475575584260271722059309)
        ·
          refine ⟨44803340844097601895772241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119475575584260271722059309 44803340844097601895772241)
          ·
            refine ⟨33602505633073201421829181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44803340844097601895772241 33602505633073201421829181)
            ·
              refine ⟨12600939612402450533185943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33602505633073201421829181 12600939612402450533185943)
              ·
                refine ⟨18901409418603675799778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600939612402450533185943 18901409418603675799778915)
                ·
                  refine ⟨28352114127905513699668373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18901409418603675799778915 28352114127905513699668373)
                  ·
                    refine ⟨1329005349745570954671955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28352114127905513699668373 1329005349745570954671955)
                    ·
                      rfl

theorem cell23_7764686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_7764686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764686 prefixEnd_7764686 := by exact prefixLift 7764686
  have htrace : WordTrace (prefixWord ++ tailWord_7764686) baseStart_7764686 baseEnd_7764686 := by
    simpa [prefixWord, tailWord_7764686, baseEnd_7764686] using wordTrace_append hprefix tailTrace_7764686
  have hstable : (prefixWord ++ tailWord_7764686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764686).length < 2 ^ (prefixWord ++ tailWord_7764686).sum := by decide
  have hdescent : baseEnd_7764686 < baseStart_7764686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764689 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_7764689 : Nat := 118140960795 + 7764689 * 2 ^ 59
def prefixEnd_7764689 : Nat := 4983230072969 + 3 ^ 40 * 7764689 * 2
def baseEnd_7764689 : Nat := 3987017589678676352278351

theorem tailTrace_7764689 : CollatzResearch.WordTrace tailWord_7764689 prefixEnd_7764689 3987017589678676352278351 := by
  unfold tailWord_7764689
  simp only [CollatzResearch.WordTrace]
  refine ⟨283201473766865331149833121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188800982511243554099888747 283201473766865331149833121)
  ·
    refine ⟨212401105325148998362374841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283201473766865331149833121 212401105325148998362374841)
    ·
      refine ⟨159300828993861748771781131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212401105325148998362374841 159300828993861748771781131)
      ·
        refine ⟨238951243490792623157671697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159300828993861748771781131 238951243490792623157671697)
        ·
          refine ⟨179213432618094467368253773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238951243490792623157671697 179213432618094467368253773)
          ·
            refine ⟨67205037231785425263095165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179213432618094467368253773 67205037231785425263095165)
            ·
              refine ⟨25201888961919534473660687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67205037231785425263095165 25201888961919534473660687)
              ·
                refine ⟨37802833442879301710491031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25201888961919534473660687 37802833442879301710491031)
                ·
                  refine ⟨56704250164318952565736547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37802833442879301710491031 56704250164318952565736547)
                  ·
                    refine ⟨85056375246478428848604821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56704250164318952565736547 85056375246478428848604821)
                    ·
                      refine ⟨3987017589678676352278351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85056375246478428848604821 3987017589678676352278351)
                      ·
                        rfl

theorem cell23_7764689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_7764689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764689 prefixEnd_7764689 := by exact prefixLift 7764689
  have htrace : WordTrace (prefixWord ++ tailWord_7764689) baseStart_7764689 baseEnd_7764689 := by
    simpa [prefixWord, tailWord_7764689, baseEnd_7764689] using wordTrace_append hprefix tailTrace_7764689
  have hstable : (prefixWord ++ tailWord_7764689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764689).length < 2 ^ (prefixWord ++ tailWord_7764689).sum := by decide
  have hdescent : baseEnd_7764689 < baseStart_7764689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764776 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7764776 : Nat := 118140960795 + 7764776 * 2 ^ 59
def prefixEnd_7764776 : Nat := 4983230072969 + 3 ^ 40 * 7764776 * 2
def baseEnd_7764776 : Nat := 1329020754165205837296817

theorem tailTrace_7764776 : CollatzResearch.WordTrace tailWord_7764776 prefixEnd_7764776 1329020754165205837296817 := by
  unfold tailWord_7764776
  simp only [CollatzResearch.WordTrace]
  refine ⟨141602323458775072504125091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188803097945033430005500121 141602323458775072504125091)
  ·
    refine ⟨212403485188162608756187637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141602323458775072504125091 212403485188162608756187637)
    ·
      refine ⟨19912826736390244570892591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212403485188162608756187637 19912826736390244570892591)
      ·
        refine ⟨29869240104585366856338887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19912826736390244570892591 29869240104585366856338887)
        ·
          refine ⟨44803860156878050284508331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29869240104585366856338887 44803860156878050284508331)
          ·
            refine ⟨67205790235317075426762497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44803860156878050284508331 67205790235317075426762497)
            ·
              refine ⟨50404342676487806570071873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67205790235317075426762497 50404342676487806570071873)
              ·
                refine ⟨37803257007365854927553905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50404342676487806570071873 37803257007365854927553905)
                ·
                  refine ⟨28352442755524391195665429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37803257007365854927553905 28352442755524391195665429)
                  ·
                    refine ⟨1329020754165205837296817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28352442755524391195665429 1329020754165205837296817)
                    ·
                      rfl

theorem cell23_7764776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7764776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764776 prefixEnd_7764776 := by exact prefixLift 7764776
  have htrace : WordTrace (prefixWord ++ tailWord_7764776) baseStart_7764776 baseEnd_7764776 := by
    simpa [prefixWord, tailWord_7764776, baseEnd_7764776] using wordTrace_append hprefix tailTrace_7764776
  have hstable : (prefixWord ++ tailWord_7764776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764776).length < 2 ^ (prefixWord ++ tailWord_7764776).sum := by decide
  have hdescent : baseEnd_7764776 < baseStart_7764776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764778 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7764778 : Nat := 118140960795 + 7764778 * 2 ^ 59
def prefixEnd_7764778 : Nat := 4983230072969 + 3 ^ 40 * 7764778 * 2
def baseEnd_7764778 : Nat := 3987063289456926504065443

theorem tailTrace_7764778 : CollatzResearch.WordTrace tailWord_7764778 prefixEnd_7764778 3987063289456926504065443 := by
  unfold tailWord_7764778
  simp only [CollatzResearch.WordTrace]
  refine ⟨70801179965885724837455747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188803146575695266233215325 70801179965885724837455747)
  ·
    refine ⟨106201769948828587256183621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70801179965885724837455747 106201769948828587256183621)
    ·
      refine ⟨19912831865405360110534429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106201769948828587256183621 19912831865405360110534429)
      ·
        refine ⟨7467311949527010041450411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19912831865405360110534429 7467311949527010041450411)
        ·
          refine ⟨11200967924290515062175617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467311949527010041450411 11200967924290515062175617)
          ·
            refine ⟨8400725943217886296631713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11200967924290515062175617 8400725943217886296631713)
            ·
              refine ⟨6300544457413414722473785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400725943217886296631713 6300544457413414722473785)
              ·
                refine ⟨4725408343060061041855339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300544457413414722473785 4725408343060061041855339)
                ·
                  refine ⟨7088112514590091562783009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725408343060061041855339 7088112514590091562783009)
                  ·
                    refine ⟨5316084385942568672087257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7088112514590091562783009 5316084385942568672087257)
                    ·
                      refine ⟨3987063289456926504065443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316084385942568672087257 3987063289456926504065443)
                      ·
                        rfl

theorem cell23_7764778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7764778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764778 prefixEnd_7764778 := by exact prefixLift 7764778
  have htrace : WordTrace (prefixWord ++ tailWord_7764778) baseStart_7764778 baseEnd_7764778 := by
    simpa [prefixWord, tailWord_7764778, baseEnd_7764778] using wordTrace_append hprefix tailTrace_7764778
  have hstable : (prefixWord ++ tailWord_7764778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764778).length < 2 ^ (prefixWord ++ tailWord_7764778).sum := by decide
  have hdescent : baseEnd_7764778 < baseStart_7764778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764786 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_7764786 : Nat := 118140960795 + 7764786 * 2 ^ 59
def prefixEnd_7764786 : Nat := 4983230072969 + 3 ^ 40 * 7764786 * 2
def baseEnd_7764786 : Nat := 3987067397302162472765405

theorem tailTrace_7764786 : CollatzResearch.WordTrace tailWord_7764786 prefixEnd_7764786 3987067397302162472765405 := by
  unfold tailWord_7764786
  simp only [CollatzResearch.WordTrace]
  refine ⟨70801252911878479179028553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188803341098342611144076141 70801252911878479179028553)
  ·
    refine ⟨53100939683908859384271415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70801252911878479179028553 53100939683908859384271415)
    ·
      refine ⟨79651409525863289076407123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53100939683908859384271415 79651409525863289076407123)
      ·
        refine ⟨119477114288794933614610685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79651409525863289076407123 119477114288794933614610685)
        ·
          refine ⟨44803917858298100105479007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119477114288794933614610685 44803917858298100105479007)
          ·
            refine ⟨67205876787447150158218511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44803917858298100105479007 67205876787447150158218511)
            ·
              refine ⟨100808815181170725237327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67205876787447150158218511 100808815181170725237327767)
              ·
                refine ⟨151213222771756087855991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100808815181170725237327767 151213222771756087855991651)
                ·
                  refine ⟨226819834157634131783987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151213222771756087855991651 226819834157634131783987477)
                  ·
                    refine ⟨10632179726139099927374413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226819834157634131783987477 10632179726139099927374413)
                    ·
                      refine ⟨3987067397302162472765405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632179726139099927374413 3987067397302162472765405)
                      ·
                        rfl

theorem cell23_7764786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_7764786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764786 prefixEnd_7764786 := by exact prefixLift 7764786
  have htrace : WordTrace (prefixWord ++ tailWord_7764786) baseStart_7764786 baseEnd_7764786 := by
    simpa [prefixWord, tailWord_7764786, baseEnd_7764786] using wordTrace_append hprefix tailTrace_7764786
  have hstable : (prefixWord ++ tailWord_7764786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764786).length < 2 ^ (prefixWord ++ tailWord_7764786).sum := by decide
  have hdescent : baseEnd_7764786 < baseStart_7764786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764823 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 5]
def baseStart_7764823 : Nat := 118140960795 + 7764823 * 2 ^ 59
def prefixEnd_7764823 : Nat := 4983230072969 + 3 ^ 40 * 7764823 * 2
def baseEnd_7764823 : Nat := 443009599565153203111415

theorem tailTrace_7764823 : CollatzResearch.WordTrace tailWord_7764823 prefixEnd_7764823 443009599565153203111415 := by
  unfold tailWord_7764823
  simp only [CollatzResearch.WordTrace]
  refine ⟨283206361148379872035211123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188804240765586581356807415 283206361148379872035211123)
  ·
    refine ⟨424809541722569808052816685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283206361148379872035211123 424809541722569808052816685)
    ·
      refine ⟨159303578145963678019806257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424809541722569808052816685 159303578145963678019806257)
      ·
        refine ⟨119477683609472758514854693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159303578145963678019806257 119477683609472758514854693)
        ·
          refine ⟨22402065676776142221535255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119477683609472758514854693 22402065676776142221535255)
          ·
            refine ⟨33603098515164213332302883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22402065676776142221535255 33603098515164213332302883)
            ·
              refine ⟨50404647772746319998454325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33603098515164213332302883 50404647772746319998454325)
              ·
                refine ⟨4725435728694967499855093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50404647772746319998454325 4725435728694967499855093)
                ·
                  refine ⟨443009599565153203111415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4725435728694967499855093 443009599565153203111415)
                  ·
                    rfl

theorem cell23_7764823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 5].length) (baseStart_7764823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764823 prefixEnd_7764823 := by exact prefixLift 7764823
  have htrace : WordTrace (prefixWord ++ tailWord_7764823) baseStart_7764823 baseEnd_7764823 := by
    simpa [prefixWord, tailWord_7764823, baseEnd_7764823] using wordTrace_append hprefix tailTrace_7764823
  have hstable : (prefixWord ++ tailWord_7764823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764823).length < 2 ^ (prefixWord ++ tailWord_7764823).sum := by decide
  have hdescent : baseEnd_7764823 < baseStart_7764823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764856 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_7764856 : Nat := 118140960795 + 7764856 * 2 ^ 59
def prefixEnd_7764856 : Nat := 4983230072969 + 3 ^ 40 * 7764856 * 2
def baseEnd_7764856 : Nat := 3987103340947977198890083

theorem tailTrace_7764856 : CollatzResearch.WordTrace tailWord_7764856 prefixEnd_7764856 3987103340947977198890083 := by
  unfold tailWord_7764856
  simp only [CollatzResearch.WordTrace]
  refine ⟨141603782378630159335581211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188805043171506879114108281 141603782378630159335581211)
  ·
    refine ⟨212405673567945239003371817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141603782378630159335581211 212405673567945239003371817)
    ·
      refine ⟨159304255175958929252528863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212405673567945239003371817 159304255175958929252528863)
      ·
        refine ⟨238956382763938393878793295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159304255175958929252528863 238956382763938393878793295)
        ·
          refine ⟨358434574145907590818189943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238956382763938393878793295 358434574145907590818189943)
          ·
            refine ⟨537651861218861386227284915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358434574145907590818189943 537651861218861386227284915)
            ·
              refine ⟨806477791828292079340927373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537651861218861386227284915 806477791828292079340927373)
              ·
                refine ⟨302429171935609529752847765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 806477791828292079340927373 302429171935609529752847765)
                ·
                  refine ⟨14176367434481696707164739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302429171935609529752847765 14176367434481696707164739)
                  ·
                    refine ⟨21264551151722545060747109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14176367434481696707164739 21264551151722545060747109)
                    ·
                      refine ⟨3987103340947977198890083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21264551151722545060747109 3987103340947977198890083)
                      ·
                        rfl

theorem cell23_7764856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_7764856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764856 prefixEnd_7764856 := by exact prefixLift 7764856
  have htrace : WordTrace (prefixWord ++ tailWord_7764856) baseStart_7764856 baseEnd_7764856 := by
    simpa [prefixWord, tailWord_7764856, baseEnd_7764856] using wordTrace_append hprefix tailTrace_7764856
  have hstable : (prefixWord ++ tailWord_7764856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764856).length < 2 ^ (prefixWord ++ tailWord_7764856).sum := by decide
  have hdescent : baseEnd_7764856 < baseStart_7764856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764890 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7764890 : Nat := 118140960795 + 7764890 * 2 ^ 59
def prefixEnd_7764890 : Nat := 4983230072969 + 3 ^ 40 * 7764890 * 2
def baseEnd_7764890 : Nat := 3987120799290230065864927

theorem tailTrace_7764890 : CollatzResearch.WordTrace tailWord_7764890 prefixEnd_7764890 3987120799290230065864927 := by
  unfold tailWord_7764890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70802201209784285619475031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188805869892758094985266749 70802201209784285619475031)
  ·
    refine ⟨106203301814676428429212547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70802201209784285619475031 106203301814676428429212547)
    ·
      refine ⟨159304952722014642643818821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106203301814676428429212547 159304952722014642643818821)
      ·
        refine ⟨29869678635377745495716029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159304952722014642643818821 29869678635377745495716029)
        ·
          refine ⟨11201129488266654560893511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29869678635377745495716029 11201129488266654560893511)
          ·
            refine ⟨16801694232399981841340267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201129488266654560893511 16801694232399981841340267)
            ·
              refine ⟨25202541348599972762010401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16801694232399981841340267 25202541348599972762010401)
              ·
                refine ⟨18901906011449979571507801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25202541348599972762010401 18901906011449979571507801)
                ·
                  refine ⟨14176429508587484678630851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18901906011449979571507801 14176429508587484678630851)
                  ·
                    refine ⟨21264644262881227017946277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14176429508587484678630851 21264644262881227017946277)
                    ·
                      refine ⟨3987120799290230065864927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21264644262881227017946277 3987120799290230065864927)
                      ·
                        rfl

theorem cell23_7764890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7764890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764890 prefixEnd_7764890 := by exact prefixLift 7764890
  have htrace : WordTrace (prefixWord ++ tailWord_7764890) baseStart_7764890 baseEnd_7764890 := by
    simpa [prefixWord, tailWord_7764890, baseEnd_7764890] using wordTrace_append hprefix tailTrace_7764890
  have hstable : (prefixWord ++ tailWord_7764890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764890).length < 2 ^ (prefixWord ++ tailWord_7764890).sum := by decide
  have hdescent : baseEnd_7764890 < baseStart_7764890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764896 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 8]
def baseStart_7764896 : Nat := 118140960795 + 7764896 * 2 ^ 59
def prefixEnd_7764896 : Nat := 4983230072969 + 3 ^ 40 * 7764896 * 2
def baseEnd_7764896 : Nat := 443013764463795226932211

theorem tailTrace_7764896 : CollatzResearch.WordTrace tailWord_7764896 prefixEnd_7764896 443013764463795226932211 := by
  unfold tailWord_7764896
  simp only [CollatzResearch.WordTrace]
  refine ⟨141604511838557702751309271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188806015784743603668412361 141604511838557702751309271)
  ·
    refine ⟨212406767757836554126963907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141604511838557702751309271 212406767757836554126963907)
    ·
      refine ⟨318610151636754831190445861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212406767757836554126963907 318610151636754831190445861)
      ·
        refine ⟨59739403431891530848208599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318610151636754831190445861 59739403431891530848208599)
        ·
          refine ⟨89609105147837296272312899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59739403431891530848208599 89609105147837296272312899)
          ·
            refine ⟨134413657721755944408469349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89609105147837296272312899 134413657721755944408469349)
            ·
              refine ⟨25202560822829239576588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134413657721755944408469349 25202560822829239576588003)
              ·
                refine ⟨37803841234243859364882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25202560822829239576588003 37803841234243859364882005)
                ·
                  refine ⟨443013764463795226932211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37803841234243859364882005 443013764463795226932211)
                  ·
                    rfl

theorem cell23_7764896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_7764896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764896 prefixEnd_7764896 := by exact prefixLift 7764896
  have htrace : WordTrace (prefixWord ++ tailWord_7764896) baseStart_7764896 baseEnd_7764896 := by
    simpa [prefixWord, tailWord_7764896, baseEnd_7764896] using wordTrace_append hprefix tailTrace_7764896
  have hstable : (prefixWord ++ tailWord_7764896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764896).length < 2 ^ (prefixWord ++ tailWord_7764896).sum := by decide
  have hdescent : baseEnd_7764896 < baseStart_7764896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764933 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_7764933 : Nat := 118140960795 + 7764933 * 2 ^ 59
def prefixEnd_7764933 : Nat := 4983230072969 + 3 ^ 40 * 7764933 * 2
def baseEnd_7764933 : Nat := 3987142878958373397627229

theorem tailTrace_7764933 : CollatzResearch.WordTrace tailWord_7764933 prefixEnd_7764933 3987142878958373397627229 := by
  unfold tailWord_7764933
  simp only [CollatzResearch.WordTrace]
  refine ⟨283210373177981360821715453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188806915451987573881143635 283210373177981360821715453)
  ·
    refine ⟨106203889941743010308143295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283210373177981360821715453 106203889941743010308143295)
    ·
      refine ⟨159305834912614515462214943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106203889941743010308143295 159305834912614515462214943)
      ·
        refine ⟨238958752368921773193322415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159305834912614515462214943 238958752368921773193322415)
        ·
          refine ⟨358438128553382659789983623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238958752368921773193322415 358438128553382659789983623)
          ·
            refine ⟨537657192830073989684975435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358438128553382659789983623 537657192830073989684975435)
            ·
              refine ⟨806485789245110984527463153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537657192830073989684975435 806485789245110984527463153)
              ·
                refine ⟨604864341933833238395597365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806485789245110984527463153 604864341933833238395597365)
                ·
                  refine ⟨56706032056296866099587253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604864341933833238395597365 56706032056296866099587253)
                  ·
                    refine ⟨5316190505277831196836305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56706032056296866099587253 5316190505277831196836305)
                    ·
                      refine ⟨3987142878958373397627229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316190505277831196836305 3987142878958373397627229)
                      ·
                        rfl

theorem cell23_7764933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_7764933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764933 prefixEnd_7764933 := by exact prefixLift 7764933
  have htrace : WordTrace (prefixWord ++ tailWord_7764933) baseStart_7764933 baseEnd_7764933 := by
    simpa [prefixWord, tailWord_7764933, baseEnd_7764933] using wordTrace_append hprefix tailTrace_7764933
  have hstable : (prefixWord ++ tailWord_7764933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764933).length < 2 ^ (prefixWord ++ tailWord_7764933).sum := by decide
  have hdescent : baseEnd_7764933 < baseStart_7764933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764963 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7764963 : Nat := 118140960795 + 7764963 * 2 ^ 59
def prefixEnd_7764963 : Nat := 4983230072969 + 3 ^ 40 * 7764963 * 2
def baseEnd_7764963 : Nat := 3987158283378008280252091

theorem tailTrace_7764963 : CollatzResearch.WordTrace tailWord_7764963 prefixEnd_7764963 3987158283378008280252091 := by
  unfold tailWord_7764963
  simp only [CollatzResearch.WordTrace]
  refine ⟨283211467367872675945307543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188807644911915117296871695 283211467367872675945307543)
  ·
    refine ⟨424817201051809013917961315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283211467367872675945307543 424817201051809013917961315)
    ·
      refine ⟨637225801577713520876941973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424817201051809013917961315 637225801577713520876941973)
      ·
        refine ⟨29869959448955321291106655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 637225801577713520876941973 29869959448955321291106655)
        ·
          refine ⟨44804939173432981936659983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29869959448955321291106655 44804939173432981936659983)
          ·
            refine ⟨67207408760149472904989975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44804939173432981936659983 67207408760149472904989975)
            ·
              refine ⟨100811113140224209357484963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67207408760149472904989975 100811113140224209357484963)
              ·
                refine ⟨151216669710336314036227445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100811113140224209357484963 151216669710336314036227445)
                ·
                  refine ⟨14176562785344029440896323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151216669710336314036227445 14176562785344029440896323)
                  ·
                    refine ⟨21264844178016044161344485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14176562785344029440896323 21264844178016044161344485)
                    ·
                      refine ⟨3987158283378008280252091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21264844178016044161344485 3987158283378008280252091)
                      ·
                        rfl

theorem cell23_7764963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7764963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764963 prefixEnd_7764963 := by exact prefixLift 7764963
  have htrace : WordTrace (prefixWord ++ tailWord_7764963) baseStart_7764963 baseEnd_7764963 := by
    simpa [prefixWord, tailWord_7764963, baseEnd_7764963] using wordTrace_append hprefix tailTrace_7764963
  have hstable : (prefixWord ++ tailWord_7764963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764963).length < 2 ^ (prefixWord ++ tailWord_7764963).sum := by decide
  have hdescent : baseEnd_7764963 < baseStart_7764963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764986 : List Nat := [3, 1, 1, 1, 1, 2, 1, 13]
def baseStart_7764986 : Nat := 118140960795 + 7764986 * 2 ^ 59
def prefixEnd_7764986 : Nat := 4983230072969 + 3 ^ 40 * 7764986 * 2
def baseEnd_7764986 : Nat := 147672966423446729269055

theorem tailTrace_7764986 : CollatzResearch.WordTrace tailWord_7764986 prefixEnd_7764986 147672966423446729269055 := by
  unfold tailWord_7764986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803076561697337718348703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188808204164526233915596541 70803076561697337718348703)
  ·
    refine ⟨106204614842546006577523055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70803076561697337718348703 106204614842546006577523055)
    ·
      refine ⟨159306922263819009866284583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106204614842546006577523055 159306922263819009866284583)
      ·
        refine ⟨238960383395728514799426875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159306922263819009866284583 238960383395728514799426875)
        ·
          refine ⟨358440575093592772199140313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238960383395728514799426875 358440575093592772199140313)
          ·
            refine ⟨268830431320194579149355235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358440575093592772199140313 268830431320194579149355235)
            ·
              refine ⟨403245646980291868724032853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268830431320194579149355235 403245646980291868724032853)
              ·
                refine ⟨147672966423446729269055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 403245646980291868724032853 147672966423446729269055)
                ·
                  rfl

theorem cell23_7764986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_7764986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764986 prefixEnd_7764986 := by exact prefixLift 7764986
  have htrace : WordTrace (prefixWord ++ tailWord_7764986) baseStart_7764986 baseEnd_7764986 := by
    simpa [prefixWord, tailWord_7764986, baseEnd_7764986] using wordTrace_append hprefix tailTrace_7764986
  have hstable : (prefixWord ++ tailWord_7764986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764986).length < 2 ^ (prefixWord ++ tailWord_7764986).sum := by decide
  have hdescent : baseEnd_7764986 < baseStart_7764986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7764994 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7764994 : Nat := 118140960795 + 7764994 * 2 ^ 59
def prefixEnd_7764994 : Nat := 4983230072969 + 3 ^ 40 * 7764994 * 2
def baseEnd_7764994 : Nat := 1329058067092765886321483

theorem tailTrace_7764994 : CollatzResearch.WordTrace tailWord_7764994 prefixEnd_7764994 1329058067092765886321483 := by
  unfold tailWord_7764994
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803149507690092059921509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188808398687173578826457357 70803149507690092059921509)
  ·
    refine ⟨13275590532691892261235283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70803149507690092059921509 13275590532691892261235283)
    ·
      refine ⟨19913385799037838391852925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13275590532691892261235283 19913385799037838391852925)
      ·
        refine ⟨7467519674639189396944847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19913385799037838391852925 7467519674639189396944847)
        ·
          refine ⟨11201279511958784095417271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467519674639189396944847 11201279511958784095417271)
          ·
            refine ⟨16801919267938176143125907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201279511958784095417271 16801919267938176143125907)
            ·
              refine ⟨25202878901907264214688861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16801919267938176143125907 25202878901907264214688861)
              ·
                refine ⟨9451079588215224080508323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25202878901907264214688861 9451079588215224080508323)
                ·
                  refine ⟨14176619382322836120762485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451079588215224080508323 14176619382322836120762485)
                  ·
                    refine ⟨1329058067092765886321483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14176619382322836120762485 1329058067092765886321483)
                    ·
                      rfl

theorem cell23_7764994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7764994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7764994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7764994 prefixEnd_7764994 := by exact prefixLift 7764994
  have htrace : WordTrace (prefixWord ++ tailWord_7764994) baseStart_7764994 baseEnd_7764994 := by
    simpa [prefixWord, tailWord_7764994, baseEnd_7764994] using wordTrace_append hprefix tailTrace_7764994
  have hstable : (prefixWord ++ tailWord_7764994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7764994).length < 2 ^ (prefixWord ++ tailWord_7764994).sum := by decide
  have hdescent : baseEnd_7764994 < baseStart_7764994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7764994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765024 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_7765024 : Nat := 118140960795 + 7765024 * 2 ^ 59
def prefixEnd_7765024 : Nat := 4983230072969 + 3 ^ 40 * 7765024 * 2
def baseEnd_7765024 : Nat := 1329063201899310847196437

theorem tailTrace_7765024 : CollatzResearch.WordTrace tailWord_7765024 prefixEnd_7765024 1329063201899310847196437 := by
  unfold tailWord_7765024
  simp only [CollatzResearch.WordTrace]
  refine ⟨141606846110325841681639063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188809128147101122242185417 141606846110325841681639063)
  ·
    refine ⟨212410269165488762522458595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141606846110325841681639063 212410269165488762522458595)
    ·
      refine ⟨318615403748233143783687893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212410269165488762522458595 318615403748233143783687893)
      ·
        refine ⟨7467548525349214307430185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 318615403748233143783687893 7467548525349214307430185)
        ·
          refine ⟨5600661394011910730572639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7467548525349214307430185 5600661394011910730572639)
          ·
            refine ⟨8400992091017866095858959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600661394011910730572639 8400992091017866095858959)
            ·
              refine ⟨12601488136526799143788439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8400992091017866095858959 12601488136526799143788439)
              ·
                refine ⟨18902232204790198715682659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12601488136526799143788439 18902232204790198715682659)
                ·
                  refine ⟨28353348307185298073523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18902232204790198715682659 28353348307185298073523989)
                  ·
                    refine ⟨1329063201899310847196437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28353348307185298073523989 1329063201899310847196437)
                    ·
                      rfl

theorem cell23_7765024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_7765024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765024 prefixEnd_7765024 := by exact prefixLift 7765024
  have htrace : WordTrace (prefixWord ++ tailWord_7765024) baseStart_7765024 baseEnd_7765024 := by
    simpa [prefixWord, tailWord_7765024, baseEnd_7765024] using wordTrace_append hprefix tailTrace_7765024
  have hstable : (prefixWord ++ tailWord_7765024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765024).length < 2 ^ (prefixWord ++ tailWord_7765024).sum := by decide
  have hdescent : baseEnd_7765024 < baseStart_7765024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765034 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7765034 : Nat := 118140960795 + 7765034 * 2 ^ 59
def prefixEnd_7765034 : Nat := 4983230072969 + 3 ^ 40 * 7765034 * 2
def baseEnd_7765034 : Nat := 3987194740504477502464265

theorem tailTrace_7765034 : CollatzResearch.WordTrace tailWord_7765034 prefixEnd_7765034 3987194740504477502464265 := by
  unfold tailWord_7765034
  simp only [CollatzResearch.WordTrace]
  refine ⟨70803514237653863767785539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188809371300410303380761437 70803514237653863767785539)
  ·
    refine ⟨106205271356480795651678309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70803514237653863767785539 106205271356480795651678309)
    ·
      refine ⟨19913488379340149184689683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106205271356480795651678309 19913488379340149184689683)
      ·
        refine ⟨29870232569010223777034525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19913488379340149184689683 29870232569010223777034525)
        ·
          refine ⟨11201337213378833916387947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29870232569010223777034525 11201337213378833916387947)
          ·
            refine ⟨16802005820068250874581921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201337213378833916387947 16802005820068250874581921)
            ·
              refine ⟨12601504365051188155936441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16802005820068250874581921 12601504365051188155936441)
              ·
                refine ⟨9451128273788391116952331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12601504365051188155936441 9451128273788391116952331)
                ·
                  refine ⟨14176692410682586675428497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451128273788391116952331 14176692410682586675428497)
                  ·
                    refine ⟨10632519308011940006571373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14176692410682586675428497 10632519308011940006571373)
                    ·
                      refine ⟨3987194740504477502464265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632519308011940006571373 3987194740504477502464265)
                      ·
                        rfl

theorem cell23_7765034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7765034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765034 prefixEnd_7765034 := by exact prefixLift 7765034
  have htrace : WordTrace (prefixWord ++ tailWord_7765034) baseStart_7765034 baseEnd_7765034 := by
    simpa [prefixWord, tailWord_7765034, baseEnd_7765034] using wordTrace_append hprefix tailTrace_7765034
  have hstable : (prefixWord ++ tailWord_7765034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765034).length < 2 ^ (prefixWord ++ tailWord_7765034).sum := by decide
  have hdescent : baseEnd_7765034 < baseStart_7765034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765093 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 9]
def baseStart_7765093 : Nat := 118140960795 + 7765093 * 2 ^ 59
def prefixEnd_7765093 : Nat := 4983230072969 + 3 ^ 40 * 7765093 * 2
def baseEnd_7765093 : Nat := 443025003984788085736277

theorem tailTrace_7765093 : CollatzResearch.WordTrace tailWord_7765093 prefixEnd_7765093 443025003984788085736277 := by
  unfold tailWord_7765093
  simp only [CollatzResearch.WordTrace]
  refine ⟨283216208857401708147539933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188810805904934472098359955 283216208857401708147539933)
  ·
    refine ⟨106206078321525640555327475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283216208857401708147539933 106206078321525640555327475)
    ·
      refine ⟨159309117482288460832991213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106206078321525640555327475 159309117482288460832991213)
      ·
        refine ⟨59740919055858172812371705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159309117482288460832991213 59740919055858172812371705)
        ·
          refine ⟨44805689291893629609278779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59740919055858172812371705 44805689291893629609278779)
          ·
            refine ⟨67208533937840444413918169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44805689291893629609278779 67208533937840444413918169)
            ·
              refine ⟨50406400453380333310438627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67208533937840444413918169 50406400453380333310438627)
              ·
                refine ⟨75609600680070499965657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50406400453380333310438627 75609600680070499965657941)
                ·
                  refine ⟨443025003984788085736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75609600680070499965657941 443025003984788085736277)
                  ·
                    rfl

theorem cell23_7765093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_7765093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765093 prefixEnd_7765093 := by exact prefixLift 7765093
  have htrace : WordTrace (prefixWord ++ tailWord_7765093) baseStart_7765093 baseEnd_7765093 := by
    simpa [prefixWord, tailWord_7765093, baseEnd_7765093] using wordTrace_append hprefix tailTrace_7765093
  have hstable : (prefixWord ++ tailWord_7765093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765093).length < 2 ^ (prefixWord ++ tailWord_7765093).sum := by decide
  have hdescent : baseEnd_7765093 < baseStart_7765093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765121 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7765121 : Nat := 118140960795 + 7765121 * 2 ^ 59
def prefixEnd_7765121 : Nat := 4983230072969 + 3 ^ 40 * 7765121 * 2
def baseEnd_7765121 : Nat := 3987239413321418662076365

theorem tailTrace_7765121 : CollatzResearch.WordTrace tailWord_7765121 prefixEnd_7765121 3987239413321418662076365 := by
  unfold tailWord_7765121
  simp only [CollatzResearch.WordTrace]
  refine ⟨283217230101300268929559217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188811486734200179286372811 283217230101300268929559217)
  ·
    refine ⟨212412922575975201697169413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283217230101300268929559217 212412922575975201697169413)
    ·
      refine ⟨39827422982995350318219265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212412922575975201697169413 39827422982995350318219265)
      ·
        refine ⟨29870567237246512738664449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39827422982995350318219265 29870567237246512738664449)
        ·
          refine ⟨22402925427934884553998337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29870567237246512738664449 22402925427934884553998337)
          ·
            refine ⟨16802194070951163415498753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22402925427934884553998337 16802194070951163415498753)
            ·
              refine ⟨12601645553213372561624065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16802194070951163415498753 12601645553213372561624065)
              ·
                refine ⟨9451234164910029421218049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12601645553213372561624065 9451234164910029421218049)
                ·
                  refine ⟨7088425623682522065913537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9451234164910029421218049 7088425623682522065913537)
                  ·
                    refine ⟨5316319217761891549435153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7088425623682522065913537 5316319217761891549435153)
                    ·
                      refine ⟨3987239413321418662076365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316319217761891549435153 3987239413321418662076365)
                      ·
                        rfl

theorem cell23_7765121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7765121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765121 prefixEnd_7765121 := by exact prefixLift 7765121
  have htrace : WordTrace (prefixWord ++ tailWord_7765121) baseStart_7765121 baseEnd_7765121 := by
    simpa [prefixWord, tailWord_7765121, baseEnd_7765121] using wordTrace_append hprefix tailTrace_7765121
  have hstable : (prefixWord ++ tailWord_7765121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765121).length < 2 ^ (prefixWord ++ tailWord_7765121).sum := by decide
  have hdescent : baseEnd_7765121 < baseStart_7765121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765157 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_7765157 : Nat := 118140960795 + 7765157 * 2 ^ 59
def prefixEnd_7765157 : Nat := 4983230072969 + 3 ^ 40 * 7765157 * 2
def baseEnd_7765157 : Nat := 1329085966208326840408733

theorem tailTrace_7765157 : CollatzResearch.WordTrace tailWord_7765157 prefixEnd_7765157 1329085966208326840408733 := by
  unfold tailWord_7765157
  simp only [CollatzResearch.WordTrace]
  refine ⟨283218543129169847077869725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188812362086113231385246483 283218543129169847077869725)
  ·
    refine ⟨106206953673438692654201147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283218543129169847077869725 106206953673438692654201147)
    ·
      refine ⟨159310430510158038981301721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106206953673438692654201147 159310430510158038981301721)
      ·
        refine ⟨119482822882618529235976291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159310430510158038981301721 119482822882618529235976291)
        ·
          refine ⟨179224234323927793853964437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119482822882618529235976291 179224234323927793853964437)
          ·
            refine ⟨8401135983934115336904583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179224234323927793853964437 8401135983934115336904583)
            ·
              refine ⟨12601703975901173005356875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401135983934115336904583 12601703975901173005356875)
              ·
                refine ⟨18902555963851759508035313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12601703975901173005356875 18902555963851759508035313)
                ·
                  refine ⟨14176916972888819631026485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18902555963851759508035313 14176916972888819631026485)
                  ·
                    refine ⟨1329085966208326840408733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14176916972888819631026485 1329085966208326840408733)
                    ·
                      rfl

theorem cell23_7765157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_7765157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765157 prefixEnd_7765157 := by exact prefixLift 7765157
  have htrace : WordTrace (prefixWord ++ tailWord_7765157) baseStart_7765157 baseEnd_7765157 := by
    simpa [prefixWord, tailWord_7765157, baseEnd_7765157] using wordTrace_append hprefix tailTrace_7765157
  have hstable : (prefixWord ++ tailWord_7765157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765157).length < 2 ^ (prefixWord ++ tailWord_7765157).sum := by decide
  have hdescent : baseEnd_7765157 < baseStart_7765157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765177 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7765177 : Nat := 118140960795 + 7765177 * 2 ^ 59
def prefixEnd_7765177 : Nat := 4983230072969 + 3 ^ 40 * 7765177 * 2
def baseEnd_7765177 : Nat := 3987268168238070442976107

theorem tailTrace_7765177 : CollatzResearch.WordTrace tailWord_7765177 prefixEnd_7765177 3987268168238070442976107 := by
  unfold tailWord_7765177
  simp only [CollatzResearch.WordTrace]
  refine ⟨283219272589097390493597785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188812848392731593662398523 283219272589097390493597785)
  ·
    refine ⟨212414454441823042870198339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283219272589097390493597785 212414454441823042870198339)
    ·
      refine ⟨318621681662734564305297509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212414454441823042870198339 318621681662734564305297509)
      ·
        refine ⟨59741565311762730807243283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318621681662734564305297509 59741565311762730807243283)
        ·
          refine ⟨89612347967644096210864925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59741565311762730807243283 89612347967644096210864925)
          ·
            refine ⟨33604630487866536079074347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89612347967644096210864925 33604630487866536079074347)
            ·
              refine ⟨50406945731799804118611521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33604630487866536079074347 50406945731799804118611521)
              ·
                refine ⟨37805209298849853088958641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50406945731799804118611521 37805209298849853088958641)
                ·
                  refine ⟨28353906974137389816718981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37805209298849853088958641 28353906974137389816718981)
                  ·
                    refine ⟨5316357557650760590634809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28353906974137389816718981 5316357557650760590634809)
                    ·
                      refine ⟨3987268168238070442976107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316357557650760590634809 3987268168238070442976107)
                      ·
                        rfl

theorem cell23_7765177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7765177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765177 prefixEnd_7765177 := by exact prefixLift 7765177
  have htrace : WordTrace (prefixWord ++ tailWord_7765177) baseStart_7765177 baseEnd_7765177 := by
    simpa [prefixWord, tailWord_7765177, baseEnd_7765177] using wordTrace_append hprefix tailTrace_7765177
  have hstable : (prefixWord ++ tailWord_7765177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765177).length < 2 ^ (prefixWord ++ tailWord_7765177).sum := by decide
  have hdescent : baseEnd_7765177 < baseStart_7765177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765193 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_7765193 : Nat := 118140960795 + 7765193 * 2 ^ 59
def prefixEnd_7765193 : Nat := 4983230072969 + 3 ^ 40 * 7765193 * 2
def baseEnd_7765193 : Nat := 3987276383928542380376033

theorem tailTrace_7765193 : CollatzResearch.WordTrace tailWord_7765193 prefixEnd_7765193 3987276383928542380376033 := by
  unfold tailWord_7765193
  simp only [CollatzResearch.WordTrace]
  refine ⟨283219856157039425226180233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188813237438026283484120155 283219856157039425226180233)
  ·
    refine ⟨212414892117779568919635175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283219856157039425226180233 212414892117779568919635175)
    ·
      refine ⟨318622338176669353379452763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212414892117779568919635175 318622338176669353379452763)
      ·
        refine ⟨477933507265004030069179145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318622338176669353379452763 477933507265004030069179145)
        ·
          refine ⟨358450130448753022551884359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477933507265004030069179145 358450130448753022551884359)
          ·
            refine ⟨537675195673129533827826539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358450130448753022551884359 537675195673129533827826539)
            ·
              refine ⟨806512793509694300741739809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537675195673129533827826539 806512793509694300741739809)
              ·
                refine ⟨604884595132270725556304857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806512793509694300741739809 604884595132270725556304857)
                ·
                  refine ⟨453663446349203044167228643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604884595132270725556304857 453663446349203044167228643)
                  ·
                    refine ⟨680495169523804566250842965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 453663446349203044167228643 680495169523804566250842965)
                    ·
                      refine ⟨3987276383928542380376033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 680495169523804566250842965 3987276383928542380376033)
                      ·
                        rfl

theorem cell23_7765193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_7765193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765193 prefixEnd_7765193 := by exact prefixLift 7765193
  have htrace : WordTrace (prefixWord ++ tailWord_7765193) baseStart_7765193 baseEnd_7765193 := by
    simpa [prefixWord, tailWord_7765193, baseEnd_7765193] using wordTrace_append hprefix tailTrace_7765193
  have hstable : (prefixWord ++ tailWord_7765193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765193).length < 2 ^ (prefixWord ++ tailWord_7765193).sum := by decide
  have hdescent : baseEnd_7765193 < baseStart_7765193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765210 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_7765210 : Nat := 118140960795 + 7765210 * 2 ^ 59
def prefixEnd_7765210 : Nat := 4983230072969 + 3 ^ 40 * 7765210 * 2
def baseEnd_7765210 : Nat := 3987285113099668813863455

theorem tailTrace_7765210 : CollatzResearch.WordTrace tailWord_7765210 prefixEnd_7765210 3987285113099668813863455 := by
  unfold tailWord_7765210
  simp only [CollatzResearch.WordTrace]
  refine ⟨70805119049494459282387271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188813650798651891419699389 70805119049494459282387271)
  ·
    refine ⟨106207678574241688923580907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70805119049494459282387271 106207678574241688923580907)
    ·
      refine ⟨159311517861362533385371361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106207678574241688923580907 159311517861362533385371361)
      ·
        refine ⟨119483638396021900039028521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159311517861362533385371361 119483638396021900039028521)
        ·
          refine ⟨89612728797016425029271391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119483638396021900039028521 89612728797016425029271391)
          ·
            refine ⟨134419093195524637543907087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89612728797016425029271391 134419093195524637543907087)
            ·
              refine ⟨201628639793286956315860631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134419093195524637543907087 201628639793286956315860631)
              ·
                refine ⟨302442959689930434473790947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201628639793286956315860631 302442959689930434473790947)
                ·
                  refine ⟨453664439534895651710686421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302442959689930434473790947 453664439534895651710686421)
                  ·
                    refine ⟨10632760301599116836969213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 453664439534895651710686421 10632760301599116836969213)
                    ·
                      refine ⟨3987285113099668813863455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632760301599116836969213 3987285113099668813863455)
                      ·
                        rfl

theorem cell23_7765210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_7765210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765210 prefixEnd_7765210 := by exact prefixLift 7765210
  have htrace : WordTrace (prefixWord ++ tailWord_7765210) baseStart_7765210 baseEnd_7765210 := by
    simpa [prefixWord, tailWord_7765210, baseEnd_7765210] using wordTrace_append hprefix tailTrace_7765210
  have hstable : (prefixWord ++ tailWord_7765210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765210).length < 2 ^ (prefixWord ++ tailWord_7765210).sum := by decide
  have hdescent : baseEnd_7765210 < baseStart_7765210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765277 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7765277 : Nat := 118140960795 + 7765277 * 2 ^ 59
def prefixEnd_7765277 : Nat := 4983230072969 + 3 ^ 40 * 7765277 * 2
def baseEnd_7765277 : Nat := 1329106505434506683908549

theorem tailTrace_7765277 : CollatzResearch.WordTrace tailWord_7765277 prefixEnd_7765277 1329106505434506683908549 := by
  unfold tailWord_7765277
  simp only [CollatzResearch.WordTrace]
  refine ⟨283222919888735107572238085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188815279925823405048158723 283222919888735107572238085)
  ·
    refine ⟨53104297479137832669794641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283222919888735107572238085 53104297479137832669794641)
    ·
      refine ⟨39828223109353374502345981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53104297479137832669794641 39828223109353374502345981)
      ·
        refine ⟨14935583666007515438379743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39828223109353374502345981 14935583666007515438379743)
        ·
          refine ⟨22403375499011273157569615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14935583666007515438379743 22403375499011273157569615)
          ·
            refine ⟨33605063248516909736354423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22403375499011273157569615 33605063248516909736354423)
            ·
              refine ⟨50407594872775364604531635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33605063248516909736354423 50407594872775364604531635)
              ·
                refine ⟨75611392309163046906797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50407594872775364604531635 75611392309163046906797453)
                ·
                  refine ⟨28354272115936142590049045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75611392309163046906797453 28354272115936142590049045)
                  ·
                    refine ⟨1329106505434506683908549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28354272115936142590049045 1329106505434506683908549)
                    ·
                      rfl

theorem cell23_7765277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7765277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765277 prefixEnd_7765277 := by exact prefixLift 7765277
  have htrace : WordTrace (prefixWord ++ tailWord_7765277) baseStart_7765277 baseEnd_7765277 := by
    simpa [prefixWord, tailWord_7765277, baseEnd_7765277] using wordTrace_append hprefix tailTrace_7765277
  have hstable : (prefixWord ++ tailWord_7765277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765277).length < 2 ^ (prefixWord ++ tailWord_7765277).sum := by decide
  have hdescent : baseEnd_7765277 < baseStart_7765277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765320 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_7765320 : Nat := 118140960795 + 7765320 * 2 ^ 59
def prefixEnd_7765320 : Nat := 4983230072969 + 3 ^ 40 * 7765320 * 2
def baseEnd_7765320 : Nat := 1329113865323887794495983

theorem tailTrace_7765320 : CollatzResearch.WordTrace tailWord_7765320 prefixEnd_7765320 1329113865323887794495983 := by
  unfold tailWord_7765320
  simp only [CollatzResearch.WordTrace]
  refine ⟨141612244113789662958026707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188816325485052883944035609 141612244113789662958026707)
  ·
    refine ⟨212418366170684494437040061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141612244113789662958026707 212418366170684494437040061)
    ·
      refine ⟨79656887314006685413890023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212418366170684494437040061 79656887314006685413890023)
      ·
        refine ⟨119485330971010028120835035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79656887314006685413890023 119485330971010028120835035)
        ·
          refine ⟨179227996456515042181252553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119485330971010028120835035 179227996456515042181252553)
          ·
            refine ⟨134420997342386281635939415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179227996456515042181252553 134420997342386281635939415)
            ·
              refine ⟨201631496013579422453909123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134420997342386281635939415 201631496013579422453909123)
              ·
                refine ⟨302447244020369133680863685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201631496013579422453909123 302447244020369133680863685)
                ·
                  refine ⟨56708858253819212565161941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302447244020369133680863685 56708858253819212565161941)
                  ·
                    refine ⟨1329113865323887794495983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56708858253819212565161941 1329113865323887794495983)
                    ·
                      rfl

theorem cell23_7765320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_7765320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765320 prefixEnd_7765320 := by exact prefixLift 7765320
  have htrace : WordTrace (prefixWord ++ tailWord_7765320) baseStart_7765320 baseEnd_7765320 := by
    simpa [prefixWord, tailWord_7765320, baseEnd_7765320] using wordTrace_append hprefix tailTrace_7765320
  have hstable : (prefixWord ++ tailWord_7765320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765320).length < 2 ^ (prefixWord ++ tailWord_7765320).sum := by decide
  have hdescent : baseEnd_7765320 < baseStart_7765320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765341 : List Nat := [1, 4, 5, 1, 1, 1, 10]
def baseStart_7765341 : Nat := 118140960795 + 7765341 * 2 ^ 59
def prefixEnd_7765341 : Nat := 4983230072969 + 3 ^ 40 * 7765341 * 2
def baseEnd_7765341 : Nat := 49226572581054417300313

theorem tailTrace_7765341 : CollatzResearch.WordTrace tailWord_7765341 prefixEnd_7765341 49226572581054417300313 := by
  unfold tailWord_7765341
  simp only [CollatzResearch.WordTrace]
  refine ⟨283225254160503246502567877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188816836107002164335045251 283225254160503246502567877)
  ·
    refine ⟨53104735155094358719231477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283225254160503246502567877 53104735155094358719231477)
    ·
      refine ⟨4978568920790096129927951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53104735155094358719231477 4978568920790096129927951)
      ·
        refine ⟨7467853381185144194891927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978568920790096129927951 7467853381185144194891927)
        ·
          refine ⟨11201780071777716292337891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467853381185144194891927 11201780071777716292337891)
          ·
            refine ⟨16802670107666574438506837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201780071777716292337891 16802670107666574438506837)
            ·
              refine ⟨49226572581054417300313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16802670107666574438506837 49226572581054417300313)
              ·
                rfl

theorem cell23_7765341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 10].length) (baseStart_7765341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765341 prefixEnd_7765341 := by exact prefixLift 7765341
  have htrace : WordTrace (prefixWord ++ tailWord_7765341) baseStart_7765341 baseEnd_7765341 := by
    simpa [prefixWord, tailWord_7765341, baseEnd_7765341] using wordTrace_append hprefix tailTrace_7765341
  have hstable : (prefixWord ++ tailWord_7765341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765341).length < 2 ^ (prefixWord ++ tailWord_7765341).sum := by decide
  have hdescent : baseEnd_7765341 < baseStart_7765341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765351 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_7765351 : Nat := 118140960795 + 7765351 * 2 ^ 59
def prefixEnd_7765351 : Nat := 4983230072969 + 3 ^ 40 * 7765351 * 2
def baseEnd_7765351 : Nat := 3987357513871952762200307

theorem tailTrace_7765351 : CollatzResearch.WordTrace tailWord_7765351 prefixEnd_7765351 3987357513871952762200307 := by
  unfold tailWord_7765351
  simp only [CollatzResearch.WordTrace]
  refine ⟨283225618890467018210431907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188817079260311345473621271 283225618890467018210431907)
  ·
    refine ⟨424838428335700527315647861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283225618890467018210431907 424838428335700527315647861)
    ·
      refine ⟨39828602656471924435841987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424838428335700527315647861 39828602656471924435841987)
      ·
        refine ⟨59742903984707886653762981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39828602656471924435841987 59742903984707886653762981)
        ·
          refine ⟨11201794497132728747580559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59742903984707886653762981 11201794497132728747580559)
          ·
            refine ⟨16802691745699093121370839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201794497132728747580559 16802691745699093121370839)
            ·
              refine ⟨25204037618548639682056259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16802691745699093121370839 25204037618548639682056259)
              ·
                refine ⟨37806056427822959523084389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25204037618548639682056259 37806056427822959523084389)
                ·
                  refine ⟨7088635580216804910578323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37806056427822959523084389 7088635580216804910578323)
                  ·
                    refine ⟨10632953370325207365867485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7088635580216804910578323 10632953370325207365867485)
                    ·
                      refine ⟨3987357513871952762200307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10632953370325207365867485 3987357513871952762200307)
                      ·
                        rfl

theorem cell23_7765351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_7765351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765351 prefixEnd_7765351 := by exact prefixLift 7765351
  have htrace : WordTrace (prefixWord ++ tailWord_7765351) baseStart_7765351 baseEnd_7765351 := by
    simpa [prefixWord, tailWord_7765351, baseEnd_7765351] using wordTrace_append hprefix tailTrace_7765351
  have hstable : (prefixWord ++ tailWord_7765351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765351).length < 2 ^ (prefixWord ++ tailWord_7765351).sum := by decide
  have hdescent : baseEnd_7765351 < baseStart_7765351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765437 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7765437 : Nat := 118140960795 + 7765437 * 2 ^ 59
def prefixEnd_7765437 : Nat := 4983230072969 + 3 ^ 40 * 7765437 * 2
def baseEnd_7765437 : Nat := 3987401673208239425724911

theorem tailTrace_7765437 : CollatzResearch.WordTrace tailWord_7765437 prefixEnd_7765437 3987401673208239425724911 := by
  unfold tailWord_7765437
  simp only [CollatzResearch.WordTrace]
  refine ⟨283228755568155454898062565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188819170378770303265375043 283228755568155454898062565)
  ·
    refine ⟨53105391669029147793386731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283228755568155454898062565 53105391669029147793386731)
    ·
      refine ⟨79658087503543721690080097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53105391669029147793386731 79658087503543721690080097)
      ·
        refine ⟨59743565627657791267560073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79658087503543721690080097 59743565627657791267560073)
        ·
          refine ⟨44807674220743343450670055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59743565627657791267560073 44807674220743343450670055)
          ·
            refine ⟨67211511331115015176005083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44807674220743343450670055 67211511331115015176005083)
            ·
              refine ⟨100817266996672522764007625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67211511331115015176005083 100817266996672522764007625)
              ·
                refine ⟨75612950247504392073005719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100817266996672522764007625 75612950247504392073005719)
                ·
                  refine ⟨113419425371256588109508579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75612950247504392073005719 113419425371256588109508579)
                  ·
                    refine ⟨170129138056884882164262869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113419425371256588109508579 170129138056884882164262869)
                    ·
                      refine ⟨3987401673208239425724911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170129138056884882164262869 3987401673208239425724911)
                      ·
                        rfl

theorem cell23_7765437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7765437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765437 prefixEnd_7765437 := by exact prefixLift 7765437
  have htrace : WordTrace (prefixWord ++ tailWord_7765437) baseStart_7765437 baseEnd_7765437 := by
    simpa [prefixWord, tailWord_7765437, baseEnd_7765437] using wordTrace_append hprefix tailTrace_7765437
  have hstable : (prefixWord ++ tailWord_7765437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765437).length < 2 ^ (prefixWord ++ tailWord_7765437).sum := by decide
  have hdescent : baseEnd_7765437 < baseStart_7765437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765464 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_7765464 : Nat := 118140960795 + 7765464 * 2 ^ 59
def prefixEnd_7765464 : Nat := 4983230072969 + 3 ^ 40 * 7765464 * 2
def baseEnd_7765464 : Nat := 3987415537185910820087287

theorem tailTrace_7765464 : CollatzResearch.WordTrace tailWord_7765464 prefixEnd_7765464 3987415537185910820087287 := by
  unfold tailWord_7765464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141614870169528819254647723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188819826892705092339530297 141614870169528819254647723)
  ·
    refine ⟨212422305254293228881971585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141614870169528819254647723 212422305254293228881971585)
    ·
      refine ⟨159316728940719921661478689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212422305254293228881971585 159316728940719921661478689)
      ·
        refine ⟨119487546705539941246109017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159316728940719921661478689 119487546705539941246109017)
        ·
          refine ⟨89615660029154955934581763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119487546705539941246109017 89615660029154955934581763)
          ·
            refine ⟨134423490043732433901872645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89615660029154955934581763 134423490043732433901872645)
            ·
              refine ⟨25204404383199831356601121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134423490043732433901872645 25204404383199831356601121)
              ·
                refine ⟨18903303287399873517450841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25204404383199831356601121 18903303287399873517450841)
                ·
                  refine ⟨14177477465549905138088131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18903303287399873517450841 14177477465549905138088131)
                  ·
                    refine ⟨21266216198324857707132197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14177477465549905138088131 21266216198324857707132197)
                    ·
                      refine ⟨3987415537185910820087287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21266216198324857707132197 3987415537185910820087287)
                      ·
                        rfl

theorem cell23_7765464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_7765464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765464 prefixEnd_7765464 := by exact prefixLift 7765464
  have htrace : WordTrace (prefixWord ++ tailWord_7765464) baseStart_7765464 baseEnd_7765464 := by
    simpa [prefixWord, tailWord_7765464, baseEnd_7765464] using wordTrace_append hprefix tailTrace_7765464
  have hstable : (prefixWord ++ tailWord_7765464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765464).length < 2 ^ (prefixWord ++ tailWord_7765464).sum := by decide
  have hdescent : baseEnd_7765464 < baseStart_7765464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765501 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_7765501 : Nat := 118140960795 + 7765501 * 2 ^ 59
def prefixEnd_7765501 : Nat := 4983230072969 + 3 ^ 40 * 7765501 * 2
def baseEnd_7765501 : Nat := 3987434535970127175324617

theorem tailTrace_7765501 : CollatzResearch.WordTrace tailWord_7765501 prefixEnd_7765501 3987434535970127175324617 := by
  unfold tailWord_7765501
  simp only [CollatzResearch.WordTrace]
  refine ⟨283231089839923593828392357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188820726559949062552261571 283231089839923593828392357)
  ·
    refine ⟨53105829344985673842823567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283231089839923593828392357 53105829344985673842823567)
    ·
      refine ⟨79658744017478510764235351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53105829344985673842823567 79658744017478510764235351)
      ·
        refine ⟨119488116026217766146353027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79658744017478510764235351 119488116026217766146353027)
        ·
          refine ⟨179232174039326649219529541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119488116026217766146353027 179232174039326649219529541)
          ·
            refine ⟨33606032632373746728661789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179232174039326649219529541 33606032632373746728661789)
            ·
              refine ⟨12602262237140155023248171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33606032632373746728661789 12602262237140155023248171)
              ·
                refine ⟨18903393355710232534872257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12602262237140155023248171 18903393355710232534872257)
                ·
                  refine ⟨14177545016782674401154193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18903393355710232534872257 14177545016782674401154193)
                  ·
                    refine ⟨10633158762587005800865645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14177545016782674401154193 10633158762587005800865645)
                    ·
                      refine ⟨3987434535970127175324617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10633158762587005800865645 3987434535970127175324617)
                      ·
                        rfl

theorem cell23_7765501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_7765501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765501 prefixEnd_7765501 := by exact prefixLift 7765501
  have htrace : WordTrace (prefixWord ++ tailWord_7765501) baseStart_7765501 baseEnd_7765501 := by
    simpa [prefixWord, tailWord_7765501, baseEnd_7765501] using wordTrace_append hprefix tailTrace_7765501
  have hstable : (prefixWord ++ tailWord_7765501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765501).length < 2 ^ (prefixWord ++ tailWord_7765501).sum := by decide
  have hdescent : baseEnd_7765501 < baseStart_7765501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765608 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7765608 : Nat := 118140960795 + 7765608 * 2 ^ 59
def prefixEnd_7765608 : Nat := 4983230072969 + 3 ^ 40 * 7765608 * 2
def baseEnd_7765608 : Nat := 3987489478400158256686625

theorem tailTrace_7765608 : CollatzResearch.WordTrace tailWord_7765608 prefixEnd_7765608 3987489478400158256686625 := by
  unfold tailWord_7765608
  simp only [CollatzResearch.WordTrace]
  refine ⟨141617496225267975551268739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188823328300357300735024985 141617496225267975551268739)
  ·
    refine ⟨212426244337901963326903109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141617496225267975551268739 212426244337901963326903109)
    ·
      refine ⟨39829920813356618123794333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212426244337901963326903109 39829920813356618123794333)
      ·
        refine ⟨14936220305008731796422875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39829920813356618123794333 14936220305008731796422875)
        ·
          refine ⟨22404330457513097694634313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936220305008731796422875 22404330457513097694634313)
          ·
            refine ⟨16803247843134823270975735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22404330457513097694634313 16803247843134823270975735)
            ·
              refine ⟨25204871764702234906463603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803247843134823270975735 25204871764702234906463603)
              ·
                refine ⟨37807307647053352359695405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25204871764702234906463603 37807307647053352359695405)
                ·
                  refine ⟨14177740367645007134885777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37807307647053352359695405 14177740367645007134885777)
                  ·
                    refine ⟨10633305275733755351164333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14177740367645007134885777 10633305275733755351164333)
                    ·
                      refine ⟨3987489478400158256686625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10633305275733755351164333 3987489478400158256686625)
                      ·
                        rfl

theorem cell23_7765608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7765608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765608 prefixEnd_7765608 := by exact prefixLift 7765608
  have htrace : WordTrace (prefixWord ++ tailWord_7765608) baseStart_7765608 baseEnd_7765608 := by
    simpa [prefixWord, tailWord_7765608, baseEnd_7765608] using wordTrace_append hprefix tailTrace_7765608
  have hstable : (prefixWord ++ tailWord_7765608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765608).length < 2 ^ (prefixWord ++ tailWord_7765608).sum := by decide
  have hdescent : baseEnd_7765608 < baseStart_7765608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765639 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_7765639 : Nat := 118140960795 + 7765639 * 2 ^ 59
def prefixEnd_7765639 : Nat := 4983230072969 + 3 ^ 40 * 7765639 * 2
def baseEnd_7765639 : Nat := 3987505396300447635398983

theorem tailTrace_7765639 : CollatzResearch.WordTrace tailWord_7765639 prefixEnd_7765639 3987505396300447635398983 := by
  unfold tailWord_7765639
  simp only [CollatzResearch.WordTrace]
  refine ⟨283236123113423643396915971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188824082075615762264610647 283236123113423643396915971)
  ·
    refine ⟨424854184670135465095373957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283236123113423643396915971 424854184670135465095373957)
    ·
      refine ⟨79660159625650399705382617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424854184670135465095373957 79660159625650399705382617)
      ·
        refine ⟨59745119719237799779036963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79660159625650399705382617 59745119719237799779036963)
        ·
          refine ⟨89617679578856699668555445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59745119719237799779036963 89617679578856699668555445)
          ·
            refine ⟨8401657460517815593927073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89617679578856699668555445 8401657460517815593927073)
            ·
              refine ⟨6301243095388361695445305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8401657460517815593927073 6301243095388361695445305)
              ·
                refine ⟨4725932321541271271583979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6301243095388361695445305 4725932321541271271583979)
                ·
                  refine ⟨7088898482311906907375969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725932321541271271583979 7088898482311906907375969)
                  ·
                    refine ⟨5316673861733930180531977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7088898482311906907375969 5316673861733930180531977)
                    ·
                      refine ⟨3987505396300447635398983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316673861733930180531977 3987505396300447635398983)
                      ·
                        rfl

theorem cell23_7765639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_7765639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765639 prefixEnd_7765639 := by exact prefixLift 7765639
  have htrace : WordTrace (prefixWord ++ tailWord_7765639) baseStart_7765639 baseEnd_7765639 := by
    simpa [prefixWord, tailWord_7765639, baseEnd_7765639] using wordTrace_append hprefix tailTrace_7765639
  have hstable : (prefixWord ++ tailWord_7765639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765639).length < 2 ^ (prefixWord ++ tailWord_7765639).sum := by decide
  have hdescent : baseEnd_7765639 < baseStart_7765639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765644 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_7765644 : Nat := 118140960795 + 7765644 * 2 ^ 59
def prefixEnd_7765644 : Nat := 4983230072969 + 3 ^ 40 * 7765644 * 2
def baseEnd_7765644 : Nat := 3987507963703720115836459

theorem tailTrace_7765644 : CollatzResearch.WordTrace tailWord_7765644 prefixEnd_7765644 3987507963703720115836459 := by
  unfold tailWord_7765644
  simp only [CollatzResearch.WordTrace]
  refine ⟨141618152739202764625423993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188824203652270352833898657 141618152739202764625423993)
  ·
    refine ⟨106213614554402073469067995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141618152739202764625423993 106213614554402073469067995)
    ·
      refine ⟨159320421831603110203601993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106213614554402073469067995 159320421831603110203601993)
      ·
        refine ⟨119490316373702332652701495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159320421831603110203601993 119490316373702332652701495)
        ·
          refine ⟨179235474560553498979052243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119490316373702332652701495 179235474560553498979052243)
          ·
            refine ⟨268853211840830248468578365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179235474560553498979052243 268853211840830248468578365)
            ·
              refine ⟨100819954440311343175716887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268853211840830248468578365 100819954440311343175716887)
              ·
                refine ⟨151229931660467014763575331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100819954440311343175716887 151229931660467014763575331)
                ·
                  refine ⟨226844897490700522145362997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151229931660467014763575331 226844897490700522145362997)
                  ·
                    refine ⟨21266709139753173951127781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226844897490700522145362997 21266709139753173951127781)
                    ·
                      refine ⟨3987507963703720115836459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21266709139753173951127781 3987507963703720115836459)
                      ·
                        rfl

theorem cell23_7765644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_7765644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765644 prefixEnd_7765644 := by exact prefixLift 7765644
  have htrace : WordTrace (prefixWord ++ tailWord_7765644) baseStart_7765644 baseEnd_7765644 := by
    simpa [prefixWord, tailWord_7765644, baseEnd_7765644] using wordTrace_append hprefix tailTrace_7765644
  have hstable : (prefixWord ++ tailWord_7765644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765644).length < 2 ^ (prefixWord ++ tailWord_7765644).sum := by decide
  have hdescent : baseEnd_7765644 < baseStart_7765644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765751 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_7765751 : Nat := 118140960795 + 7765751 * 2 ^ 59
def prefixEnd_7765751 : Nat := 4983230072969 + 3 ^ 40 * 7765751 * 2
def baseEnd_7765751 : Nat := 3987562906133751197198467

theorem tailTrace_7765751 : CollatzResearch.WordTrace tailWord_7765751 prefixEnd_7765751 3987562906133751197198467 := by
  unfold tailWord_7765751
  simp only [CollatzResearch.WordTrace]
  refine ⟨283240208089017886524993107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188826805392678591016662071 283240208089017886524993107)
  ·
    refine ⟨424860312133526829787489661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283240208089017886524993107 424860312133526829787489661)
    ·
      refine ⟨159322617050072561170308623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424860312133526829787489661 159322617050072561170308623)
      ·
        refine ⟨238983925575108841755462935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159322617050072561170308623 238983925575108841755462935)
        ·
          refine ⟨358475888362663262633194403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238983925575108841755462935 358475888362663262633194403)
          ·
            refine ⟨537713832543994893949791605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358475888362663262633194403 537713832543994893949791605)
            ·
              refine ⟨50410671800999521307792963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 537713832543994893949791605 50410671800999521307792963)
              ·
                refine ⟨75616007701499281961689445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50410671800999521307792963 75616007701499281961689445)
                ·
                  refine ⟨14178001444031115367816771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75616007701499281961689445 14178001444031115367816771)
                  ·
                    refine ⟨21267002166046673051725157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14178001444031115367816771 21267002166046673051725157)
                    ·
                      refine ⟨3987562906133751197198467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21267002166046673051725157 3987562906133751197198467)
                      ·
                        rfl

theorem cell23_7765751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_7765751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765751 prefixEnd_7765751 := by exact prefixLift 7765751
  have htrace : WordTrace (prefixWord ++ tailWord_7765751) baseStart_7765751 baseEnd_7765751 := by
    simpa [prefixWord, tailWord_7765751, baseEnd_7765751] using wordTrace_append hprefix tailTrace_7765751
  have hstable : (prefixWord ++ tailWord_7765751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765751).length < 2 ^ (prefixWord ++ tailWord_7765751).sum := by decide
  have hdescent : baseEnd_7765751 < baseStart_7765751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765768 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_7765768 : Nat := 118140960795 + 7765768 * 2 ^ 59
def prefixEnd_7765768 : Nat := 4983230072969 + 3 ^ 40 * 7765768 * 2
def baseEnd_7765768 : Nat := 3987571635304877630685889

theorem tailTrace_7765768 : CollatzResearch.WordTrace tailWord_7765768 prefixEnd_7765768 3987571635304877630685889 := by
  unfold tailWord_7765768
  simp only [CollatzResearch.WordTrace]
  refine ⟨141620414064978149214180979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188827218753304198952241305 141620414064978149214180979)
  ·
    refine ⟨212430621097467223821271469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141620414064978149214180979 212430621097467223821271469)
    ·
      refine ⟨79661482911550208932976801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212430621097467223821271469 79661482911550208932976801)
      ·
        refine ⟨59746112183662656699732601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79661482911550208932976801 59746112183662656699732601)
        ·
          refine ⟨44809584137746992524799451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59746112183662656699732601 44809584137746992524799451)
          ·
            refine ⟨67214376206620488787199177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44809584137746992524799451 67214376206620488787199177)
            ·
              refine ⟨50410782154965366590399383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67214376206620488787199177 50410782154965366590399383)
              ·
                refine ⟨75616173232448049885599075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50410782154965366590399383 75616173232448049885599075)
                ·
                  refine ⟨113424259848672074828398613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75616173232448049885599075 113424259848672074828398613)
                  ·
                    refine ⟨5316762180406503507581185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113424259848672074828398613 5316762180406503507581185)
                    ·
                      refine ⟨3987571635304877630685889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316762180406503507581185 3987571635304877630685889)
                      ·
                        rfl

theorem cell23_7765768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_7765768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765768 prefixEnd_7765768 := by exact prefixLift 7765768
  have htrace : WordTrace (prefixWord ++ tailWord_7765768) baseStart_7765768 baseEnd_7765768 := by
    simpa [prefixWord, tailWord_7765768, baseEnd_7765768] using wordTrace_append hprefix tailTrace_7765768
  have hstable : (prefixWord ++ tailWord_7765768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765768).length < 2 ^ (prefixWord ++ tailWord_7765768).sum := by decide
  have hdescent : baseEnd_7765768 < baseStart_7765768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765771 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3]
def baseStart_7765771 : Nat := 118140960795 + 7765771 * 2 ^ 59
def prefixEnd_7765771 : Nat := 4983230072969 + 3 ^ 40 * 7765771 * 2
def baseEnd_7765771 : Nat := 3987573175746841118948375

theorem tailTrace_7765771 : CollatzResearch.WordTrace tailWord_7765771 prefixEnd_7765771 3987573175746841118948375 := by
  unfold tailWord_7765771
  simp only [CollatzResearch.WordTrace]
  refine ⟨283240937548945429940721167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188827291699296953293814111 283240937548945429940721167)
  ·
    refine ⟨424861406323418144911081751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283240937548945429940721167 424861406323418144911081751)
    ·
      refine ⟨637292109485127217366622627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424861406323418144911081751 637292109485127217366622627)
      ·
        refine ⟨955938164227690826049933941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637292109485127217366622627 955938164227690826049933941)
        ·
          refine ⟨89619202896346014942181307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 955938164227690826049933941 89619202896346014942181307)
          ·
            refine ⟨134428804344519022413271961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89619202896346014942181307 134428804344519022413271961)
            ·
              refine ⟨100821603258389266809953971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134428804344519022413271961 100821603258389266809953971)
              ·
                refine ⟨151232404887583900214930957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100821603258389266809953971 151232404887583900214930957)
                ·
                  refine ⟨56712151832843962580599109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151232404887583900214930957 56712151832843962580599109)
                  ·
                    refine ⟨10633528468658242983862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56712151832843962580599109 10633528468658242983862333)
                    ·
                      refine ⟨3987573175746841118948375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10633528468658242983862333 3987573175746841118948375)
                      ·
                        rfl

theorem cell23_7765771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].length) (baseStart_7765771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765771 prefixEnd_7765771 := by exact prefixLift 7765771
  have htrace : WordTrace (prefixWord ++ tailWord_7765771) baseStart_7765771 baseEnd_7765771 := by
    simpa [prefixWord, tailWord_7765771, baseEnd_7765771] using wordTrace_append hprefix tailTrace_7765771
  have hstable : (prefixWord ++ tailWord_7765771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765771).length < 2 ^ (prefixWord ++ tailWord_7765771).sum := by decide
  have hdescent : baseEnd_7765771 < baseStart_7765771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765845 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7765845 : Nat := 118140960795 + 7765845 * 2 ^ 59
def prefixEnd_7765845 : Nat := 4983230072969 + 3 ^ 40 * 7765845 * 2
def baseEnd_7765845 : Nat := 3987611173315273829423035

theorem tailTrace_7765845 : CollatzResearch.WordTrace tailWord_7765845 prefixEnd_7765845 3987611173315273829423035 := by
  unfold tailWord_7765845
  simp only [CollatzResearch.WordTrace]
  refine ⟨283243636550677340578914989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188829091033784893719276659 283243636550677340578914989)
  ·
    refine ⟨106216363706504002717093121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283243636550677340578914989 106216363706504002717093121)
    ·
      refine ⟨79662272779878002037819841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106216363706504002717093121 79662272779878002037819841)
      ·
        refine ⟨59746704584908501528364881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79662272779878002037819841 59746704584908501528364881)
        ·
          refine ⟨44810028438681376146273661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59746704584908501528364881 44810028438681376146273661)
          ·
            refine ⟨16803760664505516054852623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44810028438681376146273661 16803760664505516054852623)
            ·
              refine ⟨25205640996758274082278935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803760664505516054852623 25205640996758274082278935)
              ·
                refine ⟨37808461495137411123418403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25205640996758274082278935 37808461495137411123418403)
                ·
                  refine ⟨56712692242706116685127605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37808461495137411123418403 56712692242706116685127605)
                  ·
                    refine ⟨5316814897753698439230713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56712692242706116685127605 5316814897753698439230713)
                    ·
                      refine ⟨3987611173315273829423035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316814897753698439230713 3987611173315273829423035)
                      ·
                        rfl

theorem cell23_7765845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7765845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765845 prefixEnd_7765845 := by exact prefixLift 7765845
  have htrace : WordTrace (prefixWord ++ tailWord_7765845) baseStart_7765845 baseEnd_7765845 := by
    simpa [prefixWord, tailWord_7765845, baseEnd_7765845] using wordTrace_append hprefix tailTrace_7765845
  have hstable : (prefixWord ++ tailWord_7765845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765845).length < 2 ^ (prefixWord ++ tailWord_7765845).sum := by decide
  have hdescent : baseEnd_7765845 < baseStart_7765845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765855 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 1, 5]
def baseStart_7765855 : Nat := 118140960795 + 7765855 * 2 ^ 59
def prefixEnd_7765855 : Nat := 4983230072969 + 3 ^ 40 * 7765855 * 2
def baseEnd_7765855 : Nat := 1329205436040606263432663

theorem tailTrace_7765855 : CollatzResearch.WordTrace tailWord_7765855 prefixEnd_7765855 1329205436040606263432663 := by
  unfold tailWord_7765855
  simp only [CollatzResearch.WordTrace]
  refine ⟨283244001280641112286779019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188829334187094074857852679 283244001280641112286779019)
  ·
    refine ⟨424866001920961668430168529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283244001280641112286779019 424866001920961668430168529)
    ·
      refine ⟨318649501440721251322626397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424866001920961668430168529 318649501440721251322626397)
      ·
        refine ⟨119493563040270469245984899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318649501440721251322626397 119493563040270469245984899)
        ·
          refine ⟨179240344560405703868977349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119493563040270469245984899 179240344560405703868977349)
          ·
            refine ⟨33607564605076069475433253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179240344560405703868977349 33607564605076069475433253)
            ·
              refine ⟨6301418363451763026643735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33607564605076069475433253 6301418363451763026643735)
              ·
                refine ⟨9452127545177644539965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301418363451763026643735 9452127545177644539965603)
                ·
                  refine ⟨14178191317766466809948405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452127545177644539965603 14178191317766466809948405)
                  ·
                    refine ⟨1329205436040606263432663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14178191317766466809948405 1329205436040606263432663)
                    ·
                      rfl

theorem cell23_7765855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_7765855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765855 prefixEnd_7765855 := by exact prefixLift 7765855
  have htrace : WordTrace (prefixWord ++ tailWord_7765855) baseStart_7765855 baseEnd_7765855 := by
    simpa [prefixWord, tailWord_7765855, baseEnd_7765855] using wordTrace_append hprefix tailTrace_7765855
  have hstable : (prefixWord ++ tailWord_7765855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765855).length < 2 ^ (prefixWord ++ tailWord_7765855).sum := by decide
  have hdescent : baseEnd_7765855 < baseStart_7765855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765871 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_7765871 : Nat := 118140960795 + 7765871 * 2 ^ 59
def prefixEnd_7765871 : Nat := 4983230072969 + 3 ^ 40 * 7765871 * 2
def baseEnd_7765871 : Nat := 3987624523812290727697915

theorem tailTrace_7765871 : CollatzResearch.WordTrace tailWord_7765871 prefixEnd_7765871 3987624523812290727697915 := by
  unfold tailWord_7765871
  simp only [CollatzResearch.WordTrace]
  refine ⟨283244584848583147019361467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188829723232388764679574311 283244584848583147019361467)
  ·
    refine ⟨424866877272874720529042201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283244584848583147019361467 424866877272874720529042201)
    ·
      refine ⟨318650157954656040396781651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424866877272874720529042201 318650157954656040396781651)
      ·
        refine ⟨477975236931984060595172477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318650157954656040396781651 477975236931984060595172477)
        ·
          refine ⟨179240713849494022723189679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477975236931984060595172477 179240713849494022723189679)
          ·
            refine ⟨268861070774241034084784519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179240713849494022723189679 268861070774241034084784519)
            ·
              refine ⟨403291606161361551127176779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268861070774241034084784519 403291606161361551127176779)
              ·
                refine ⟨604937409242042326690765169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403291606161361551127176779 604937409242042326690765169)
                ·
                  refine ⟨453703056931531745018073877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604937409242042326690765169 453703056931531745018073877)
                  ·
                    refine ⟨21267330793665550547722213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 453703056931531745018073877 21267330793665550547722213)
                    ·
                      refine ⟨3987624523812290727697915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21267330793665550547722213 3987624523812290727697915)
                      ·
                        rfl

theorem cell23_7765871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_7765871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765871 prefixEnd_7765871 := by exact prefixLift 7765871
  have htrace : WordTrace (prefixWord ++ tailWord_7765871) baseStart_7765871 baseEnd_7765871 := by
    simpa [prefixWord, tailWord_7765871, baseEnd_7765871] using wordTrace_append hprefix tailTrace_7765871
  have hstable : (prefixWord ++ tailWord_7765871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765871).length < 2 ^ (prefixWord ++ tailWord_7765871).sum := by decide
  have hdescent : baseEnd_7765871 < baseStart_7765871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765881 : List Nat := [1, 2, 1, 3, 2, 2, 2, 10]
def baseStart_7765881 : Nat := 118140960795 + 7765881 * 2 ^ 59
def prefixEnd_7765881 : Nat := 4983230072969 + 3 ^ 40 * 7765881 * 2
def baseEnd_7765881 : Nat := 147689987356253173650847

theorem tailTrace_7765881 : CollatzResearch.WordTrace tailWord_7765881 prefixEnd_7765881 147689987356253173650847 := by
  unfold tailWord_7765881
  simp only [CollatzResearch.WordTrace]
  refine ⟨283244949578546918727225497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188829966385697945818150331 283244949578546918727225497)
  ·
    refine ⟨212433712183910189045419123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283244949578546918727225497 212433712183910189045419123)
    ·
      refine ⟨318650568275865283568128685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212433712183910189045419123 318650568275865283568128685)
      ·
        refine ⟨119493963103449481338048257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318650568275865283568128685 119493963103449481338048257)
        ·
          refine ⟨89620472327587111003536193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119493963103449481338048257 89620472327587111003536193)
          ·
            refine ⟨67215354245690333252652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89620472327587111003536193 67215354245690333252652145)
            ·
              refine ⟨50411515684267749939489109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67215354245690333252652145 50411515684267749939489109)
              ·
                refine ⟨147689987356253173650847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50411515684267749939489109 147689987356253173650847)
                ·
                  rfl

theorem cell23_7765881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 10].length) (baseStart_7765881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765881 prefixEnd_7765881 := by exact prefixLift 7765881
  have htrace : WordTrace (prefixWord ++ tailWord_7765881) baseStart_7765881 baseEnd_7765881 := by
    simpa [prefixWord, tailWord_7765881, baseEnd_7765881] using wordTrace_append hprefix tailTrace_7765881
  have hstable : (prefixWord ++ tailWord_7765881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765881).length < 2 ^ (prefixWord ++ tailWord_7765881).sum := by decide
  have hdescent : baseEnd_7765881 < baseStart_7765881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765892 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7765892 : Nat := 118140960795 + 7765892 * 2 ^ 59
def prefixEnd_7765892 : Nat := 4983230072969 + 3 ^ 40 * 7765892 * 2
def baseEnd_7765892 : Nat := 3987635306906035145535319

theorem tailTrace_7765892 : CollatzResearch.WordTrace tailWord_7765892 prefixEnd_7765892 3987635306906035145535319 := by
  unfold tailWord_7765892
  simp only [CollatzResearch.WordTrace]
  refine ⟨141622675390753533802937965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188830233854338045070583953 141622675390753533802937965)
  ·
    refine ⟨53108503271532575176101737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141622675390753533802937965 53108503271532575176101737)
    ·
      refine ⟨39831377453649431382076303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53108503271532575176101737 39831377453649431382076303)
      ·
        refine ⟨59747066180474147073114455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39831377453649431382076303 59747066180474147073114455)
        ·
          refine ⟨89620599270711220609671683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59747066180474147073114455 89620599270711220609671683)
          ·
            refine ⟨134430898906066830914507525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89620599270711220609671683 134430898906066830914507525)
            ·
              refine ⟨25205793544887530796470161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134430898906066830914507525 25205793544887530796470161)
              ·
                refine ⟨18904345158665648097352621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25205793544887530796470161 18904345158665648097352621)
                ·
                  refine ⟨7089129434499618036507233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18904345158665648097352621 7089129434499618036507233)
                  ·
                    refine ⟨5316847075874713527380425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089129434499618036507233 5316847075874713527380425)
                    ·
                      refine ⟨3987635306906035145535319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316847075874713527380425 3987635306906035145535319)
                      ·
                        rfl

theorem cell23_7765892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7765892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765892 prefixEnd_7765892 := by exact prefixLift 7765892
  have htrace : WordTrace (prefixWord ++ tailWord_7765892) baseStart_7765892 baseEnd_7765892 := by
    simpa [prefixWord, tailWord_7765892, baseEnd_7765892] using wordTrace_append hprefix tailTrace_7765892
  have hstable : (prefixWord ++ tailWord_7765892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765892).length < 2 ^ (prefixWord ++ tailWord_7765892).sum := by decide
  have hdescent : baseEnd_7765892 < baseStart_7765892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765912 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7765912 : Nat := 118140960795 + 7765912 * 2 ^ 59
def prefixEnd_7765912 : Nat := 4983230072969 + 3 ^ 40 * 7765912 * 2
def baseEnd_7765912 : Nat := 3987645576519125067285227

theorem tailTrace_7765912 : CollatzResearch.WordTrace tailWord_7765912 prefixEnd_7765912 3987645576519125067285227 := by
  unfold tailWord_7765912
  simp only [CollatzResearch.WordTrace]
  refine ⟨141623040120717305510801995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188830720160956407347735993 141623040120717305510801995)
  ·
    refine ⟨212434560181075958266202993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141623040120717305510801995 212434560181075958266202993)
    ·
      refine ⟨159325920135806968699652245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212434560181075958266202993 159325920135806968699652245)
      ·
        refine ⟨7468402506365951657796199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159325920135806968699652245 7468402506365951657796199)
        ·
          refine ⟨11202603759548927486694299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468402506365951657796199 11202603759548927486694299)
          ·
            refine ⟨16803905639323391230041449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11202603759548927486694299 16803905639323391230041449)
            ·
              refine ⟨12602929229492543422531087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16803905639323391230041449 12602929229492543422531087)
              ·
                refine ⟨18904393844238815133796631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12602929229492543422531087 18904393844238815133796631)
                ·
                  refine ⟨28356590766358222700694947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18904393844238815133796631 28356590766358222700694947)
                  ·
                    refine ⟨42534886149537334051042421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28356590766358222700694947 42534886149537334051042421)
                    ·
                      refine ⟨3987645576519125067285227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42534886149537334051042421 3987645576519125067285227)
                      ·
                        rfl

theorem cell23_7765912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7765912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765912 prefixEnd_7765912 := by exact prefixLift 7765912
  have htrace : WordTrace (prefixWord ++ tailWord_7765912) baseStart_7765912 baseEnd_7765912 := by
    simpa [prefixWord, tailWord_7765912, baseEnd_7765912] using wordTrace_append hprefix tailTrace_7765912
  have hstable : (prefixWord ++ tailWord_7765912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765912).length < 2 ^ (prefixWord ++ tailWord_7765912).sum := by decide
  have hdescent : baseEnd_7765912 < baseStart_7765912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765935 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 3, 3, 2]
def baseStart_7765935 : Nat := 118140960795 + 7765935 * 2 ^ 59
def prefixEnd_7765935 : Nat := 4983230072969 + 3 ^ 40 * 7765935 * 2
def baseEnd_7765935 : Nat := 3987657386574178477297621

theorem tailTrace_7765935 : CollatzResearch.WordTrace tailWord_7765935 prefixEnd_7765935 3987657386574178477297621 := by
  unfold tailWord_7765935
  simp only [CollatzResearch.WordTrace]
  refine ⟨283246919120351285949691259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188831279413567523966460839 283246919120351285949691259)
  ·
    refine ⟨424870378680526928924536889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283246919120351285949691259 424870378680526928924536889)
    ·
      refine ⟨318652784010395196693402667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424870378680526928924536889 318652784010395196693402667)
      ·
        refine ⟨477979176015592795040104001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318652784010395196693402667 477979176015592795040104001)
        ·
          refine ⟨358484382011694596280078001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477979176015592795040104001 358484382011694596280078001)
          ·
            refine ⟨268863286508770947210058501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358484382011694596280078001 268863286508770947210058501)
            ·
              refine ⟨50411866220394552601885969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268863286508770947210058501 50411866220394552601885969)
              ·
                refine ⟨37808899665295914451414477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50411866220394552601885969 37808899665295914451414477)
                ·
                  refine ⟨14178337374485967919280429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37808899665295914451414477 14178337374485967919280429)
                  ·
                    refine ⟨5316876515432237969730161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14178337374485967919280429 5316876515432237969730161)
                    ·
                      refine ⟨3987657386574178477297621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316876515432237969730161 3987657386574178477297621)
                      ·
                        rfl

theorem cell23_7765935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3, 2].length) (baseStart_7765935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765935 prefixEnd_7765935 := by exact prefixLift 7765935
  have htrace : WordTrace (prefixWord ++ tailWord_7765935) baseStart_7765935 baseEnd_7765935 := by
    simpa [prefixWord, tailWord_7765935, baseEnd_7765935] using wordTrace_append hprefix tailTrace_7765935
  have hstable : (prefixWord ++ tailWord_7765935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765935).length < 2 ^ (prefixWord ++ tailWord_7765935).sum := by decide
  have hdescent : baseEnd_7765935 < baseStart_7765935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765968 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_7765968 : Nat := 118140960795 + 7765968 * 2 ^ 59
def prefixEnd_7765968 : Nat := 4983230072969 + 3 ^ 40 * 7765968 * 2
def baseEnd_7765968 : Nat := 3987674331435776848184969

theorem tailTrace_7765968 : CollatzResearch.WordTrace tailWord_7765968 prefixEnd_7765968 3987674331435776848184969 := by
  unfold tailWord_7765968
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624061364615866292821279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188832081819487821723761705 141624061364615866292821279)
  ·
    refine ⟨212436092046923799439231919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141624061364615866292821279 212436092046923799439231919)
    ·
      refine ⟨318654138070385699158847879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212436092046923799439231919 318654138070385699158847879)
      ·
        refine ⟨477981207105578548738271819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318654138070385699158847879 477981207105578548738271819)
        ·
          refine ⟨716971810658367823107407729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477981207105578548738271819 716971810658367823107407729)
          ·
            refine ⟨537728857993775867330555797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716971810658367823107407729 537728857993775867330555797)
            ·
              refine ⟨25206040218458243781119803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 537728857993775867330555797 25206040218458243781119803)
              ·
                refine ⟨37809060327687365671679705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25206040218458243781119803 37809060327687365671679705)
                ·
                  refine ⟨28356795245765524253759779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37809060327687365671679705 28356795245765524253759779)
                  ·
                    refine ⟨42535192868648286380639669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28356795245765524253759779 42535192868648286380639669)
                    ·
                      refine ⟨3987674331435776848184969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42535192868648286380639669 3987674331435776848184969)
                      ·
                        rfl

theorem cell23_7765968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_7765968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765968 prefixEnd_7765968 := by exact prefixLift 7765968
  have htrace : WordTrace (prefixWord ++ tailWord_7765968) baseStart_7765968 baseEnd_7765968 := by
    simpa [prefixWord, tailWord_7765968, baseEnd_7765968] using wordTrace_append hprefix tailTrace_7765968
  have hstable : (prefixWord ++ tailWord_7765968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765968).length < 2 ^ (prefixWord ++ tailWord_7765968).sum := by decide
  have hdescent : baseEnd_7765968 < baseStart_7765968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7765988 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 7]
def baseStart_7765988 : Nat := 118140960795 + 7765988 * 2 ^ 59
def prefixEnd_7765988 : Nat := 4983230072969 + 3 ^ 40 * 7765988 * 2
def baseEnd_7765988 : Nat := 443076066783207418881653

theorem tailTrace_7765988 : CollatzResearch.WordTrace tailWord_7765988 prefixEnd_7765988 443076066783207418881653 := by
  unfold tailWord_7765988
  simp only [CollatzResearch.WordTrace]
  refine ⟨141624426094579638000685309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188832568126106184000913745 141624426094579638000685309)
  ·
    refine ⟨53109159785467364250256991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141624426094579638000685309 53109159785467364250256991)
    ·
      refine ⟨79663739678201046375385487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53109159785467364250256991 79663739678201046375385487)
      ·
        refine ⟨119495609517301569563078231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79663739678201046375385487 119495609517301569563078231)
        ·
          refine ⟨179243414275952354344617347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119495609517301569563078231 179243414275952354344617347)
          ·
            refine ⟨268865121413928531516926021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179243414275952354344617347 268865121413928531516926021)
            ·
              refine ⟨50412210265111599659423629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268865121413928531516926021 50412210265111599659423629)
              ·
                refine ⟨18904578849416849872283861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50412210265111599659423629 18904578849416849872283861)
                ·
                  refine ⟨443076066783207418881653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18904578849416849872283861 443076066783207418881653)
                  ·
                    rfl

theorem cell23_7765988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_7765988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7765988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7765988 prefixEnd_7765988 := by exact prefixLift 7765988
  have htrace : WordTrace (prefixWord ++ tailWord_7765988) baseStart_7765988 baseEnd_7765988 := by
    simpa [prefixWord, tailWord_7765988, baseEnd_7765988] using wordTrace_append hprefix tailTrace_7765988
  have hstable : (prefixWord ++ tailWord_7765988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7765988).length < 2 ^ (prefixWord ++ tailWord_7765988).sum := by decide
  have hdescent : baseEnd_7765988 < baseStart_7765988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7765988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766020 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7766020 : Nat := 118140960795 + 7766020 * 2 ^ 59
def prefixEnd_7766020 : Nat := 4983230072969 + 3 ^ 40 * 7766020 * 2
def baseEnd_7766020 : Nat := 3987701032429810644734731

theorem tailTrace_7766020 : CollatzResearch.WordTrace tailWord_7766020 prefixEnd_7766020 3987701032429810644734731 := by
  unfold tailWord_7766020
  simp only [CollatzResearch.WordTrace]
  refine ⟨141625009662521672733267757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188833346216695563644357009 141625009662521672733267757)
  ·
    refine ⟨53109378623445627274975409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141625009662521672733267757 53109378623445627274975409)
    ·
      refine ⟨39832033967584220456231557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53109378623445627274975409 39832033967584220456231557)
      ·
        refine ⟨7468506368922041335543417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39832033967584220456231557 7468506368922041335543417)
        ·
          refine ⟨5601379776691531001657563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7468506368922041335543417 5601379776691531001657563)
          ·
            refine ⟨8402069665037296502486345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601379776691531001657563 8402069665037296502486345)
            ·
              refine ⟨6301552248777972376864759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8402069665037296502486345 6301552248777972376864759)
              ·
                refine ⟨9452328373166958565297139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301552248777972376864759 9452328373166958565297139)
                ·
                  refine ⟨14178492559750437847945709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452328373166958565297139 14178492559750437847945709)
                  ·
                    refine ⟨5316934709906414192979641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14178492559750437847945709 5316934709906414192979641)
                    ·
                      refine ⟨3987701032429810644734731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5316934709906414192979641 3987701032429810644734731)
                      ·
                        rfl

theorem cell23_7766020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7766020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766020 prefixEnd_7766020 := by exact prefixLift 7766020
  have htrace : WordTrace (prefixWord ++ tailWord_7766020) baseStart_7766020 baseEnd_7766020 := by
    simpa [prefixWord, tailWord_7766020, baseEnd_7766020] using wordTrace_append hprefix tailTrace_7766020
  have hstable : (prefixWord ++ tailWord_7766020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766020).length < 2 ^ (prefixWord ++ tailWord_7766020).sum := by decide
  have hdescent : baseEnd_7766020 < baseStart_7766020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766112 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 6]
def baseStart_7766112 : Nat := 118140960795 + 7766112 * 2 ^ 59
def prefixEnd_7766112 : Nat := 4983230072969 + 3 ^ 40 * 7766112 * 2
def baseEnd_7766112 : Nat := 443083141405558253864923

theorem tailTrace_7766112 : CollatzResearch.WordTrace tailWord_7766112 prefixEnd_7766112 443083141405558253864923 := by
  unfold tailWord_7766112
  simp only [CollatzResearch.WordTrace]
  refine ⟨141626687420355022589442295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188835583227140030119256393 141626687420355022589442295)
  ·
    refine ⟨212440031130532533884163443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141626687420355022589442295 212440031130532533884163443)
    ·
      refine ⟨318660046695798800826245165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212440031130532533884163443 318660046695798800826245165)
      ·
        refine ⟨119497517510924550309841937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318660046695798800826245165 119497517510924550309841937)
        ·
          refine ⟨89623138133193412732381453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119497517510924550309841937 89623138133193412732381453)
          ·
            refine ⟨33608676799947529774643045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89623138133193412732381453 33608676799947529774643045)
            ·
              refine ⟨6301626899990161832745571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33608676799947529774643045 6301626899990161832745571)
              ·
                refine ⟨9452440349985242749118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301626899990161832745571 9452440349985242749118357)
                ·
                  refine ⟨443083141405558253864923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9452440349985242749118357 443083141405558253864923)
                  ·
                    rfl

theorem cell23_7766112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_7766112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766112 prefixEnd_7766112 := by exact prefixLift 7766112
  have htrace : WordTrace (prefixWord ++ tailWord_7766112) baseStart_7766112 baseEnd_7766112 := by
    simpa [prefixWord, tailWord_7766112, baseEnd_7766112] using wordTrace_append hprefix tailTrace_7766112
  have hstable : (prefixWord ++ tailWord_7766112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766112).length < 2 ^ (prefixWord ++ tailWord_7766112).sum := by decide
  have hdescent : baseEnd_7766112 < baseStart_7766112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766149 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_7766149 : Nat := 118140960795 + 7766149 * 2 ^ 59
def prefixEnd_7766149 : Nat := 4983230072969 + 3 ^ 40 * 7766149 * 2
def baseEnd_7766149 : Nat := 3987767271434240640021637

theorem tailTrace_7766149 : CollatzResearch.WordTrace tailWord_7766149 prefixEnd_7766149 3987767271434240640021637 := by
  unfold tailWord_7766149
  simp only [CollatzResearch.WordTrace]
  refine ⟨283254724341576000497981501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188836482894384000331987667 283254724341576000497981501)
  ·
    refine ⟨106220521628091000186743063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283254724341576000497981501 106220521628091000186743063)
    ·
      refine ⟨159330782442136500280114595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106220521628091000186743063 159330782442136500280114595)
      ·
        refine ⟨238996173663204750420171893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159330782442136500280114595 238996173663204750420171893)
        ·
          refine ⟨22405891280925445351891115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238996173663204750420171893 22405891280925445351891115)
          ·
            refine ⟨33608836921388168027836673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22405891280925445351891115 33608836921388168027836673)
            ·
              refine ⟨25206627691041126020877505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33608836921388168027836673 25206627691041126020877505)
              ·
                refine ⟨18904970768280844515658129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25206627691041126020877505 18904970768280844515658129)
                ·
                  refine ⟨14178728076210633386743597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18904970768280844515658129 14178728076210633386743597)
                  ·
                    refine ⟨5317023028578987520028849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14178728076210633386743597 5317023028578987520028849)
                    ·
                      refine ⟨3987767271434240640021637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317023028578987520028849 3987767271434240640021637)
                      ·
                        rfl

theorem cell23_7766149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_7766149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766149 prefixEnd_7766149 := by exact prefixLift 7766149
  have htrace : WordTrace (prefixWord ++ tailWord_7766149) baseStart_7766149 baseEnd_7766149 := by
    simpa [prefixWord, tailWord_7766149, baseEnd_7766149] using wordTrace_append hprefix tailTrace_7766149
  have hstable : (prefixWord ++ tailWord_7766149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766149).length < 2 ^ (prefixWord ++ tailWord_7766149).sum := by decide
  have hdescent : baseEnd_7766149 < baseStart_7766149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766162 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7766162 : Nat := 118140960795 + 7766162 * 2 ^ 59
def prefixEnd_7766162 : Nat := 4983230072969 + 3 ^ 40 * 7766162 * 2
def baseEnd_7766162 : Nat := 3987773946682749089159077

theorem tailTrace_7766162 : CollatzResearch.WordTrace tailWord_7766162 prefixEnd_7766162 3987773946682749089159077 := by
  unfold tailWord_7766162
  simp only [CollatzResearch.WordTrace]
  refine ⟨70813799622632225929551185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188836798993685935812136493 70813799622632225929551185)
  ·
    refine ⟨53110349716974169447163389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70813799622632225929551185 53110349716974169447163389)
    ·
      refine ⟨19916381143865313542686271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53110349716974169447163389 19916381143865313542686271)
      ·
        refine ⟨29874571715797970314029407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19916381143865313542686271 29874571715797970314029407)
        ·
          refine ⟨44811857573696955471044111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29874571715797970314029407 44811857573696955471044111)
          ·
            refine ⟨67217786360545433206566167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44811857573696955471044111 67217786360545433206566167)
            ·
              refine ⟨100826679540818149809849251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67217786360545433206566167 100826679540818149809849251)
              ·
                refine ⟨151240019311227224714773877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100826679540818149809849251 151240019311227224714773877)
                ·
                  refine ⟨14178751810427552317010051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151240019311227224714773877 14178751810427552317010051)
                  ·
                    refine ⟨21268127715641328475515077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14178751810427552317010051 21268127715641328475515077)
                    ·
                      refine ⟨3987773946682749089159077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21268127715641328475515077 3987773946682749089159077)
                      ·
                        rfl

theorem cell23_7766162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7766162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766162 prefixEnd_7766162 := by exact prefixLift 7766162
  have htrace : WordTrace (prefixWord ++ tailWord_7766162) baseStart_7766162 baseEnd_7766162 := by
    simpa [prefixWord, tailWord_7766162, baseEnd_7766162] using wordTrace_append hprefix tailTrace_7766162
  have hstable : (prefixWord ++ tailWord_7766162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766162).length < 2 ^ (prefixWord ++ tailWord_7766162).sum := by decide
  have hdescent : baseEnd_7766162 < baseStart_7766162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766165 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7766165 : Nat := 118140960795 + 7766165 * 2 ^ 59
def prefixEnd_7766165 : Nat := 4983230072969 + 3 ^ 40 * 7766165 * 2
def baseEnd_7766165 : Nat := 3987775487124712577421563

theorem tailTrace_7766165 : CollatzResearch.WordTrace tailWord_7766165 prefixEnd_7766165 3987775487124712577421563 := by
  unfold tailWord_7766165
  simp only [CollatzResearch.WordTrace]
  refine ⟨283255307909518035230563949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188836871939678690153709299 283255307909518035230563949)
  ·
    refine ⟨106220740466069263211461481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283255307909518035230563949 106220740466069263211461481)
    ·
      refine ⟨79665555349551947408596111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106220740466069263211461481 79665555349551947408596111)
      ·
        refine ⟨119498333024327921112894167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79665555349551947408596111 119498333024327921112894167)
        ·
          refine ⟨179247499536491881669341251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119498333024327921112894167 179247499536491881669341251)
          ·
            refine ⟨268871249304737822504011877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179247499536491881669341251 268871249304737822504011877)
            ·
              refine ⟨50413359244638341719502227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268871249304737822504011877 50413359244638341719502227)
              ·
                refine ⟨75620038866957512579253341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50413359244638341719502227 75620038866957512579253341)
                ·
                  refine ⟨28357514575109067217220003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75620038866957512579253341 28357514575109067217220003)
                  ·
                    refine ⟨42536271862663600825830005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28357514575109067217220003 42536271862663600825830005)
                    ·
                      refine ⟨3987775487124712577421563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42536271862663600825830005 3987775487124712577421563)
                      ·
                        rfl

theorem cell23_7766165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7766165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766165 prefixEnd_7766165 := by exact prefixLift 7766165
  have htrace : WordTrace (prefixWord ++ tailWord_7766165) baseStart_7766165 baseEnd_7766165 := by
    simpa [prefixWord, tailWord_7766165, baseEnd_7766165] using wordTrace_append hprefix tailTrace_7766165
  have hstable : (prefixWord ++ tailWord_7766165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766165).length < 2 ^ (prefixWord ++ tailWord_7766165).sum := by decide
  have hdescent : baseEnd_7766165 < baseStart_7766165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766172 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7766172 : Nat := 118140960795 + 7766172 * 2 ^ 59
def prefixEnd_7766172 : Nat := 4983230072969 + 3 ^ 40 * 7766172 * 2
def baseEnd_7766172 : Nat := 1329259693829764683344677

theorem tailTrace_7766172 : CollatzResearch.WordTrace tailWord_7766172 prefixEnd_7766172 1329259693829764683344677 := by
  unfold tailWord_7766172
  simp only [CollatzResearch.WordTrace]
  refine ⟨141627781610246337713034385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188837042146995116950712513 141627781610246337713034385)
  ·
    refine ⟨106220836207684753284775789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141627781610246337713034385 106220836207684753284775789)
    ·
      refine ⟨39832813577881782481790921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106220836207684753284775789 39832813577881782481790921)
      ·
        refine ⟨29874610183411336861343191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39832813577881782481790921 29874610183411336861343191)
        ·
          refine ⟨44811915275117005292014787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29874610183411336861343191 44811915275117005292014787)
          ·
            refine ⟨67217872912675507938022181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44811915275117005292014787 67217872912675507938022181)
            ·
              refine ⟨12603351171126657738379159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67217872912675507938022181 12603351171126657738379159)
              ·
                refine ⟨18905026756689986607568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603351171126657738379159 18905026756689986607568739)
                ·
                  refine ⟨28357540135034979911353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18905026756689986607568739 28357540135034979911353109)
                  ·
                    refine ⟨1329259693829764683344677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28357540135034979911353109 1329259693829764683344677)
                    ·
                      rfl

theorem cell23_7766172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7766172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766172 prefixEnd_7766172 := by exact prefixLift 7766172
  have htrace : WordTrace (prefixWord ++ tailWord_7766172) baseStart_7766172 baseEnd_7766172 := by
    simpa [prefixWord, tailWord_7766172, baseEnd_7766172] using wordTrace_append hprefix tailTrace_7766172
  have hstable : (prefixWord ++ tailWord_7766172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766172).length < 2 ^ (prefixWord ++ tailWord_7766172).sum := by decide
  have hdescent : baseEnd_7766172 < baseStart_7766172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766183 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7766183 : Nat := 118140960795 + 7766183 * 2 ^ 59
def prefixEnd_7766183 : Nat := 4983230072969 + 3 ^ 40 * 7766183 * 2
def baseEnd_7766183 : Nat := 3987784729776493506996481

theorem tailTrace_7766183 : CollatzResearch.WordTrace tailWord_7766183 prefixEnd_7766183 3987784729776493506996481 := by
  unfold tailWord_7766183
  simp only [CollatzResearch.WordTrace]
  refine ⟨283255964423452824304719203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188837309615635216203146135 283255964423452824304719203)
  ·
    refine ⟨424883946635179236457078805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283255964423452824304719203 424883946635179236457078805)
    ·
      refine ⟨19916434998524026708925569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424883946635179236457078805 19916434998524026708925569)
      ·
        refine ⟨14937326248893020031694177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19916434998524026708925569 14937326248893020031694177)
        ·
          refine ⟨11202994686669765023770633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14937326248893020031694177 11202994686669765023770633)
          ·
            refine ⟨8402246015002323767827975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202994686669765023770633 8402246015002323767827975)
            ·
              refine ⟨12603369022503485651741963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402246015002323767827975 12603369022503485651741963)
              ·
                refine ⟨18905053533755228477612945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603369022503485651741963 18905053533755228477612945)
                ·
                  refine ⟨14178790150316421358209709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18905053533755228477612945 14178790150316421358209709)
                  ·
                    refine ⟨5317046306368658009328641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14178790150316421358209709 5317046306368658009328641)
                    ·
                      refine ⟨3987784729776493506996481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317046306368658009328641 3987784729776493506996481)
                      ·
                        rfl

theorem cell23_7766183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7766183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766183 prefixEnd_7766183 := by exact prefixLift 7766183
  have htrace : WordTrace (prefixWord ++ tailWord_7766183) baseStart_7766183 baseEnd_7766183 := by
    simpa [prefixWord, tailWord_7766183, baseEnd_7766183] using wordTrace_append hprefix tailTrace_7766183
  have hstable : (prefixWord ++ tailWord_7766183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766183).length < 2 ^ (prefixWord ++ tailWord_7766183).sum := by decide
  have hdescent : baseEnd_7766183 < baseStart_7766183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766193 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_7766193 : Nat := 118140960795 + 7766193 * 2 ^ 59
def prefixEnd_7766193 : Nat := 4983230072969 + 3 ^ 40 * 7766193 * 2
def baseEnd_7766193 : Nat := 1329263288194346155957145

theorem tailTrace_7766193 : CollatzResearch.WordTrace tailWord_7766193 prefixEnd_7766193 1329263288194346155957145 := by
  unfold tailWord_7766193
  simp only [CollatzResearch.WordTrace]
  refine ⟨283256329153416596012583233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188837552768944397341722155 283256329153416596012583233)
  ·
    refine ⟨212442246865062447009437425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283256329153416596012583233 212442246865062447009437425)
    ·
      refine ⟨159331685148796835257078069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212442246865062447009437425 159331685148796835257078069)
      ·
        refine ⟨14937345482699703305351069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159331685148796835257078069 14937345482699703305351069)
        ·
          refine ⟨5601504556012388739506651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14937345482699703305351069 5601504556012388739506651)
          ·
            refine ⟨8402256834018583109259977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601504556012388739506651 8402256834018583109259977)
            ·
              refine ⟨6301692625513937331944983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8402256834018583109259977 6301692625513937331944983)
              ·
                refine ⟨9452538938270905997917475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301692625513937331944983 9452538938270905997917475)
                ·
                  refine ⟨14178808407406358996876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452538938270905997917475 14178808407406358996876213)
                  ·
                    refine ⟨1329263288194346155957145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14178808407406358996876213 1329263288194346155957145)
                    ·
                      rfl

theorem cell23_7766193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_7766193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766193 prefixEnd_7766193 := by exact prefixLift 7766193
  have htrace : WordTrace (prefixWord ++ tailWord_7766193) baseStart_7766193 baseEnd_7766193 := by
    simpa [prefixWord, tailWord_7766193, baseEnd_7766193] using wordTrace_append hprefix tailTrace_7766193
  have hstable : (prefixWord ++ tailWord_7766193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766193).length < 2 ^ (prefixWord ++ tailWord_7766193).sum := by decide
  have hdescent : baseEnd_7766193 < baseStart_7766193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766199 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_7766199 : Nat := 118140960795 + 7766199 * 2 ^ 59
def prefixEnd_7766199 : Nat := 4983230072969 + 3 ^ 40 * 7766199 * 2
def baseEnd_7766199 : Nat := 3987792945466965444396407

theorem tailTrace_7766199 : CollatzResearch.WordTrace tailWord_7766199 prefixEnd_7766199 3987792945466965444396407 := by
  unfold tailWord_7766199
  simp only [CollatzResearch.WordTrace]
  refine ⟨283256547991394859037301651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188837698660929906024867767 283256547991394859037301651)
  ·
    refine ⟨424884821987092288555952477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283256547991394859037301651 424884821987092288555952477)
    ·
      refine ⟨159331808245159608208482179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424884821987092288555952477 159331808245159608208482179)
      ·
        refine ⟨238997712367739412312723269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159331808245159608208482179 238997712367739412312723269)
        ·
          refine ⟨44812071068951139808635613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238997712367739412312723269 44812071068951139808635613)
          ·
            refine ⟨16804526650856677428238355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44812071068951139808635613 16804526650856677428238355)
            ·
              refine ⟨25206789976285016142357533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16804526650856677428238355 25206789976285016142357533)
              ·
                refine ⟨9452546241106881053384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25206789976285016142357533 9452546241106881053384075)
                ·
                  refine ⟨14178819361660321580076113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452546241106881053384075 14178819361660321580076113)
                  ·
                    refine ⟨10634114521245241185057085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14178819361660321580076113 10634114521245241185057085)
                    ·
                      refine ⟨3987792945466965444396407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634114521245241185057085 3987792945466965444396407)
                      ·
                        rfl

theorem cell23_7766199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_7766199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766199 prefixEnd_7766199 := by exact prefixLift 7766199
  have htrace : WordTrace (prefixWord ++ tailWord_7766199) baseStart_7766199 baseEnd_7766199 := by
    simpa [prefixWord, tailWord_7766199, baseEnd_7766199] using wordTrace_append hprefix tailTrace_7766199
  have hstable : (prefixWord ++ tailWord_7766199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766199).length < 2 ^ (prefixWord ++ tailWord_7766199).sum := by decide
  have hdescent : baseEnd_7766199 < baseStart_7766199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766205 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7766205 : Nat := 118140960795 + 7766205 * 2 ^ 59
def prefixEnd_7766205 : Nat := 4983230072969 + 3 ^ 40 * 7766205 * 2
def baseEnd_7766205 : Nat := 3987796026350892420921379

theorem tailTrace_7766205 : CollatzResearch.WordTrace tailWord_7766205 prefixEnd_7766205 3987796026350892420921379 := by
  unfold tailWord_7766205
  simp only [CollatzResearch.WordTrace]
  refine ⟨283256766829373122062020069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188837844552915414708013379 283256766829373122062020069)
  ·
    refine ⟨53110643780507460386628763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283256766829373122062020069 53110643780507460386628763)
    ·
      refine ⟨79665965670761190579943145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53110643780507460386628763 79665965670761190579943145)
      ·
        refine ⟨59749474253070892934957359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79665965670761190579943145 59749474253070892934957359)
        ·
          refine ⟨89624211379606339402436039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59749474253070892934957359 89624211379606339402436039)
          ·
            refine ⟨134436317069409509103654059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89624211379606339402436039 134436317069409509103654059)
            ·
              refine ⟨201654475604114263655481089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134436317069409509103654059 201654475604114263655481089)
              ·
                refine ⟨151240856703085697741610817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201654475604114263655481089 151240856703085697741610817)
                ·
                  refine ⟨113430642527314273306208113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151240856703085697741610817 113430642527314273306208113)
                  ·
                    refine ⟨85072981895485704979656085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113430642527314273306208113 85072981895485704979656085)
                    ·
                      refine ⟨3987796026350892420921379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85072981895485704979656085 3987796026350892420921379)
                      ·
                        rfl

theorem cell23_7766205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7766205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766205 prefixEnd_7766205 := by exact prefixLift 7766205
  have htrace : WordTrace (prefixWord ++ tailWord_7766205) baseStart_7766205 baseEnd_7766205 := by
    simpa [prefixWord, tailWord_7766205, baseEnd_7766205] using wordTrace_append hprefix tailTrace_7766205
  have hstable : (prefixWord ++ tailWord_7766205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766205).length < 2 ^ (prefixWord ++ tailWord_7766205).sum := by decide
  have hdescent : baseEnd_7766205 < baseStart_7766205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_7766235 : Nat := 118140960795 + 7766235 * 2 ^ 59
def prefixEnd_7766235 : Nat := 4983230072969 + 3 ^ 40 * 7766235 * 2
def baseEnd_7766235 : Nat := 3987811430770527303546241

theorem tailTrace_7766235 : CollatzResearch.WordTrace tailWord_7766235 prefixEnd_7766235 3987811430770527303546241 := by
  unfold tailWord_7766235
  simp only [CollatzResearch.WordTrace]
  refine ⟨283257861019264437185612159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188838574012842958123741439 283257861019264437185612159)
  ·
    refine ⟨424886791528896655778418239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283257861019264437185612159 424886791528896655778418239)
    ·
      refine ⟨637330187293344983667627359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424886791528896655778418239 637330187293344983667627359)
      ·
        refine ⟨955995280940017475501441039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637330187293344983667627359 955995280940017475501441039)
        ·
          refine ⟨1433992921410026213252161559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955995280940017475501441039 1433992921410026213252161559)
          ·
            refine ⟨2150989382115039319878242339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433992921410026213252161559 2150989382115039319878242339)
            ·
              refine ⟨3226484073172558979817363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150989382115039319878242339 3226484073172558979817363509)
              ·
                refine ⟨302482881859927404357877829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3226484073172558979817363509 302482881859927404357877829)
                ·
                  refine ⟨56715540348736388317102093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302482881859927404357877829 56715540348736388317102093)
                  ·
                    refine ⟨21268327630776145618913285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56715540348736388317102093 21268327630776145618913285)
                    ·
                      refine ⟨3987811430770527303546241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21268327630776145618913285 3987811430770527303546241)
                      ·
                        rfl

theorem cell23_7766235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_7766235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766235 prefixEnd_7766235 := by exact prefixLift 7766235
  have htrace : WordTrace (prefixWord ++ tailWord_7766235) baseStart_7766235 baseEnd_7766235 := by
    simpa [prefixWord, tailWord_7766235, baseEnd_7766235] using wordTrace_append hprefix tailTrace_7766235
  have hstable : (prefixWord ++ tailWord_7766235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766235).length < 2 ^ (prefixWord ++ tailWord_7766235).sum := by decide
  have hdescent : baseEnd_7766235 < baseStart_7766235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766262 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_7766262 : Nat := 118140960795 + 7766262 * 2 ^ 59
def prefixEnd_7766262 : Nat := 4983230072969 + 3 ^ 40 * 7766262 * 2
def baseEnd_7766262 : Nat := 1329275098249399565969539

theorem tailTrace_7766262 : CollatzResearch.WordTrace tailWord_7766262 prefixEnd_7766262 1329275098249399565969539 := by
  unfold tailWord_7766262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17703677861885413799802815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188839230526777747197896693 17703677861885413799802815)
  ·
    refine ⟨26555516792828120699704223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17703677861885413799802815 26555516792828120699704223)
    ·
      refine ⟨39833275189242181049556335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26555516792828120699704223 39833275189242181049556335)
      ·
        refine ⟨59749912783863271574334503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39833275189242181049556335 59749912783863271574334503)
        ·
          refine ⟨89624869175794907361501755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59749912783863271574334503 89624869175794907361501755)
          ·
            refine ⟨134437303763692361042252633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89624869175794907361501755 134437303763692361042252633)
            ·
              refine ⟨100827977822769270781689475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134437303763692361042252633 100827977822769270781689475)
              ·
                refine ⟨151241966734153906172534213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100827977822769270781689475 151241966734153906172534213)
                ·
                  refine ⟨28357868762653857407350165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151241966734153906172534213 28357868762653857407350165)
                  ·
                    refine ⟨1329275098249399565969539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28357868762653857407350165 1329275098249399565969539)
                    ·
                      rfl

theorem cell23_7766262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_7766262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766262 prefixEnd_7766262 := by exact prefixLift 7766262
  have htrace : WordTrace (prefixWord ++ tailWord_7766262) baseStart_7766262 baseEnd_7766262 := by
    simpa [prefixWord, tailWord_7766262, baseEnd_7766262] using wordTrace_append hprefix tailTrace_7766262
  have hstable : (prefixWord ++ tailWord_7766262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766262).length < 2 ^ (prefixWord ++ tailWord_7766262).sum := by decide
  have hdescent : baseEnd_7766262 < baseStart_7766262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766265 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7766265 : Nat := 118140960795 + 7766265 * 2 ^ 59
def prefixEnd_7766265 : Nat := 4983230072969 + 3 ^ 40 * 7766265 * 2
def baseEnd_7766265 : Nat := 3987826835190162186171103

theorem tailTrace_7766265 : CollatzResearch.WordTrace tailWord_7766265 prefixEnd_7766265 3987826835190162186171103 := by
  unfold tailWord_7766265
  simp only [CollatzResearch.WordTrace]
  refine ⟨283258955209155752309204249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188839303472770501539469499 283258955209155752309204249)
  ·
    refine ⟨212444216406866814231903187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283258955209155752309204249 212444216406866814231903187)
    ·
      refine ⟨318666324610300221347854781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212444216406866814231903187 318666324610300221347854781)
      ·
        refine ⟨119499871728862583005445543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318666324610300221347854781 119499871728862583005445543)
        ·
          refine ⟨179249807593293874508168315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119499871728862583005445543 179249807593293874508168315)
          ·
            refine ⟨268874711389940811762252473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179249807593293874508168315 268874711389940811762252473)
            ·
              refine ⟨201656033542455608821689355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268874711389940811762252473 201656033542455608821689355)
              ·
                refine ⟨302484050313683413232534033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201656033542455608821689355 302484050313683413232534033)
                ·
                  refine ⟨226863037735262559924400525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302484050313683413232534033 226863037735262559924400525)
                  ·
                    refine ⟨85073639150723459971650197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226863037735262559924400525 85073639150723459971650197)
                    ·
                      refine ⟨3987826835190162186171103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85073639150723459971650197 3987826835190162186171103)
                      ·
                        rfl

theorem cell23_7766265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7766265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766265 prefixEnd_7766265 := by exact prefixLift 7766265
  have htrace : WordTrace (prefixWord ++ tailWord_7766265) baseStart_7766265 baseEnd_7766265 := by
    simpa [prefixWord, tailWord_7766265, baseEnd_7766265] using wordTrace_append hprefix tailTrace_7766265
  have hstable : (prefixWord ++ tailWord_7766265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766265).length < 2 ^ (prefixWord ++ tailWord_7766265).sum := by decide
  have hdescent : baseEnd_7766265 < baseStart_7766265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766282 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7766282 : Nat := 118140960795 + 7766282 * 2 ^ 59
def prefixEnd_7766282 : Nat := 4983230072969 + 3 ^ 40 * 7766282 * 2
def baseEnd_7766282 : Nat := 3987835564361288619658525

theorem tailTrace_7766282 : CollatzResearch.WordTrace tailWord_7766282 prefixEnd_7766282 3987835564361288619658525 := by
  unfold tailWord_7766282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70814893812523541053143275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188839716833396109475048733 70814893812523541053143275)
  ·
    refine ⟨106222340718785311579714913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70814893812523541053143275 106222340718785311579714913)
    ·
      refine ⟨79666755539088983684786185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106222340718785311579714913 79666755539088983684786185)
      ·
        refine ⟨59750066654316737763589639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79666755539088983684786185 59750066654316737763589639)
        ·
          refine ⟨89625099981475106645384459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59750066654316737763589639 89625099981475106645384459)
          ·
            refine ⟨134437649972212659968076689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89625099981475106645384459 134437649972212659968076689)
            ·
              refine ⟨100828237479159494976057517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134437649972212659968076689 100828237479159494976057517)
              ·
                refine ⟨37810589054684810616021569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100828237479159494976057517 37810589054684810616021569)
                ·
                  refine ⟨28357941791013607962016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37810589054684810616021569 28357941791013607962016177)
                  ·
                    refine ⟨21268456343260205971512133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28357941791013607962016177 21268456343260205971512133)
                    ·
                      refine ⟨3987835564361288619658525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21268456343260205971512133 3987835564361288619658525)
                      ·
                        rfl

theorem cell23_7766282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7766282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766282 prefixEnd_7766282 := by exact prefixLift 7766282
  have htrace : WordTrace (prefixWord ++ tailWord_7766282) baseStart_7766282 baseEnd_7766282 := by
    simpa [prefixWord, tailWord_7766282, baseEnd_7766282] using wordTrace_append hprefix tailTrace_7766282
  have hstable : (prefixWord ++ tailWord_7766282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766282).length < 2 ^ (prefixWord ++ tailWord_7766282).sum := by decide
  have hdescent : baseEnd_7766282 < baseStart_7766282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766332 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7766332 : Nat := 118140960795 + 7766332 * 2 ^ 59
def prefixEnd_7766332 : Nat := 4983230072969 + 3 ^ 40 * 7766332 * 2
def baseEnd_7766332 : Nat := 3987861238394013424033295

theorem tailTrace_7766332 : CollatzResearch.WordTrace tailWord_7766332 prefixEnd_7766332 3987861238394013424033295 := by
  unfold tailWord_7766332
  simp only [CollatzResearch.WordTrace]
  refine ⟨141630699449956511375946625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188840932599942015167928833 141630699449956511375946625)
  ·
    refine ⟨106223024587467383531959969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141630699449956511375946625 106223024587467383531959969)
    ·
      refine ⟨79667268440600537648969977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106223024587467383531959969 79667268440600537648969977)
      ·
        refine ⟨59750451330450403236727483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79667268440600537648969977 59750451330450403236727483)
        ·
          refine ⟨89625676995675604855091225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59750451330450403236727483 89625676995675604855091225)
          ·
            refine ⟨67219257746756703641318419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89625676995675604855091225 67219257746756703641318419)
            ·
              refine ⟨100828886620135055461977629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67219257746756703641318419 100828886620135055461977629)
              ·
                refine ⟨37810832482550645798241611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100828886620135055461977629 37810832482550645798241611)
                ·
                  refine ⟨56716248723825968697362417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37810832482550645798241611 56716248723825968697362417)
                  ·
                    refine ⟨42537186542869476523021813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56716248723825968697362417 42537186542869476523021813)
                    ·
                      refine ⟨3987861238394013424033295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42537186542869476523021813 3987861238394013424033295)
                      ·
                        rfl

theorem cell23_7766332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7766332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766332 prefixEnd_7766332 := by exact prefixLift 7766332
  have htrace : WordTrace (prefixWord ++ tailWord_7766332) baseStart_7766332 baseEnd_7766332 := by
    simpa [prefixWord, tailWord_7766332, baseEnd_7766332] using wordTrace_append hprefix tailTrace_7766332
  have hstable : (prefixWord ++ tailWord_7766332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766332).length < 2 ^ (prefixWord ++ tailWord_7766332).sum := by decide
  have hdescent : baseEnd_7766332 < baseStart_7766332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766356 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_7766356 : Nat := 118140960795 + 7766356 * 2 ^ 59
def prefixEnd_7766356 : Nat := 4983230072969 + 3 ^ 40 * 7766356 * 2
def baseEnd_7766356 : Nat := 1329291187309907110044395

theorem tailTrace_7766356 : CollatzResearch.WordTrace tailWord_7766356 prefixEnd_7766356 1329291187309907110044395 := by
  unfold tailWord_7766356
  simp only [CollatzResearch.WordTrace]
  refine ⟨141631137125913037425383461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188841516167884049900511281 141631137125913037425383461)
  ·
    refine ⟨26555838211108694517259399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141631137125913037425383461 26555838211108694517259399)
    ·
      refine ⟨39833757316663041775889099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26555838211108694517259399 39833757316663041775889099)
      ·
        refine ⟨59750635974994562663833649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39833757316663041775889099 59750635974994562663833649)
        ·
          refine ⟨44812976981245921997875237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59750635974994562663833649 44812976981245921997875237)
          ·
            refine ⟨8402433183983610374601607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44812976981245921997875237 8402433183983610374601607)
            ·
              refine ⟨12603649775975415561902411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402433183983610374601607 12603649775975415561902411)
              ·
                refine ⟨18905474663963123342853617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603649775975415561902411 18905474663963123342853617)
                ·
                  refine ⟨14179105997972342507140213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18905474663963123342853617 14179105997972342507140213)
                  ·
                    refine ⟨1329291187309907110044395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14179105997972342507140213 1329291187309907110044395)
                    ·
                      rfl

theorem cell23_7766356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_7766356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766356 prefixEnd_7766356 := by exact prefixLift 7766356
  have htrace : WordTrace (prefixWord ++ tailWord_7766356) baseStart_7766356 baseEnd_7766356 := by
    simpa [prefixWord, tailWord_7766356, baseEnd_7766356] using wordTrace_append hprefix tailTrace_7766356
  have hstable : (prefixWord ++ tailWord_7766356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766356).length < 2 ^ (prefixWord ++ tailWord_7766356).sum := by decide
  have hdescent : baseEnd_7766356 < baseStart_7766356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766359 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_7766359 : Nat := 118140960795 + 7766359 * 2 ^ 59
def prefixEnd_7766359 : Nat := 4983230072969 + 3 ^ 40 * 7766359 * 2
def baseEnd_7766359 : Nat := 3987875102371684818395671

theorem tailTrace_7766359 : CollatzResearch.WordTrace tailWord_7766359 prefixEnd_7766359 3987875102371684818395671 := by
  unfold tailWord_7766359
  simp only [CollatzResearch.WordTrace]
  refine ⟨283262383670815206363126131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188841589113876804242084087 283262383670815206363126131)
  ·
    refine ⟨424893575506222809544689197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283262383670815206363126131 424893575506222809544689197)
    ·
      refine ⟨159335090814833553579258449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424893575506222809544689197 159335090814833553579258449)
      ·
        refine ⟨119501318111125165184443837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159335090814833553579258449 119501318111125165184443837)
        ·
          refine ⟨44812994291671936944166439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119501318111125165184443837 44812994291671936944166439)
          ·
            refine ⟨67219491437507905416249659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44812994291671936944166439 67219491437507905416249659)
            ·
              refine ⟨100829237156261858124374489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67219491437507905416249659 100829237156261858124374489)
              ·
                refine ⟨75621927867196393593280867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100829237156261858124374489 75621927867196393593280867)
                ·
                  refine ⟨113432891800794590389921301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75621927867196393593280867 113432891800794590389921301)
                  ·
                    refine ⟨5317166803162246424527561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113432891800794590389921301 5317166803162246424527561)
                    ·
                      refine ⟨3987875102371684818395671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317166803162246424527561 3987875102371684818395671)
                      ·
                        rfl

theorem cell23_7766359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_7766359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766359 prefixEnd_7766359 := by exact prefixLift 7766359
  have htrace : WordTrace (prefixWord ++ tailWord_7766359) baseStart_7766359 baseEnd_7766359 := by
    simpa [prefixWord, tailWord_7766359, baseEnd_7766359] using wordTrace_append hprefix tailTrace_7766359
  have hstable : (prefixWord ++ tailWord_7766359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766359).length < 2 ^ (prefixWord ++ tailWord_7766359).sum := by decide
  have hdescent : baseEnd_7766359 < baseStart_7766359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766372 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7766372 : Nat := 118140960795 + 7766372 * 2 ^ 59
def prefixEnd_7766372 : Nat := 4983230072969 + 3 ^ 40 * 7766372 * 2
def baseEnd_7766372 : Nat := 3987881777620193267533111

theorem tailTrace_7766372 : CollatzResearch.WordTrace tailWord_7766372 prefixEnd_7766372 3987881777620193267533111 := by
  unfold tailWord_7766372
  simp only [CollatzResearch.WordTrace]
  refine ⟨141631428909884054791674685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188841905213178739722232913 141631428909884054791674685)
  ·
    refine ⟨53111785841206520546878007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141631428909884054791674685 53111785841206520546878007)
    ·
      refine ⟨79667678761809780820317011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53111785841206520546878007 79667678761809780820317011)
      ·
        refine ⟨119501518142714671230475517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79667678761809780820317011 119501518142714671230475517)
        ·
          refine ⟨44813069303518001711428319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119501518142714671230475517 44813069303518001711428319)
          ·
            refine ⟨67219603955277002567142479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44813069303518001711428319 67219603955277002567142479)
            ·
              refine ⟨100829405932915503850713719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67219603955277002567142479 100829405932915503850713719)
              ·
                refine ⟨151244108899373255776070579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100829405932915503850713719 151244108899373255776070579)
                ·
                  refine ⟨226866163349059883664105869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151244108899373255776070579 226866163349059883664105869)
                  ·
                    refine ⟨85074811255897456374039701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226866163349059883664105869 85074811255897456374039701)
                    ·
                      refine ⟨3987881777620193267533111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85074811255897456374039701 3987881777620193267533111)
                      ·
                        rfl

theorem cell23_7766372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7766372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766372 prefixEnd_7766372 := by exact prefixLift 7766372
  have htrace : WordTrace (prefixWord ++ tailWord_7766372) baseStart_7766372 baseEnd_7766372 := by
    simpa [prefixWord, tailWord_7766372, baseEnd_7766372] using wordTrace_append hprefix tailTrace_7766372
  have hstable : (prefixWord ++ tailWord_7766372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766372).length < 2 ^ (prefixWord ++ tailWord_7766372).sum := by decide
  have hdescent : baseEnd_7766372 < baseStart_7766372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766376 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7766376 : Nat := 118140960795 + 7766376 * 2 ^ 59
def prefixEnd_7766376 : Nat := 4983230072969 + 3 ^ 40 * 7766376 * 2
def baseEnd_7766376 : Nat := 3987883831542811251883093

theorem tailTrace_7766376 : CollatzResearch.WordTrace tailWord_7766376 prefixEnd_7766376 3987883831542811251883093 := by
  unfold tailWord_7766376
  simp only [CollatzResearch.WordTrace]
  refine ⟨141631501855876809133247491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188842002474502412177663321 141631501855876809133247491)
  ·
    refine ⟨212447252783815213699871237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141631501855876809133247491 212447252783815213699871237)
    ·
      refine ⟨39833859896965352568725857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212447252783815213699871237 39833859896965352568725857)
      ·
        refine ⟨29875394922724014426544393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39833859896965352568725857 29875394922724014426544393)
        ·
          refine ⟨22406546192043010819908295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29875394922724014426544393 22406546192043010819908295)
          ·
            refine ⟨33609819288064516229862443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22406546192043010819908295 33609819288064516229862443)
            ·
              refine ⟨50414728932096774344793665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33609819288064516229862443 50414728932096774344793665)
              ·
                refine ⟨37811046699072580758595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50414728932096774344793665 37811046699072580758595249)
                ·
                  refine ⟨28358285024304435568946437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37811046699072580758595249 28358285024304435568946437)
                  ·
                    refine ⟨5317178442057081669177457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28358285024304435568946437 5317178442057081669177457)
                    ·
                      refine ⟨3987883831542811251883093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317178442057081669177457 3987883831542811251883093)
                      ·
                        rfl

theorem cell23_7766376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7766376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766376 prefixEnd_7766376 := by exact prefixLift 7766376
  have htrace : WordTrace (prefixWord ++ tailWord_7766376) baseStart_7766376 baseEnd_7766376 := by
    simpa [prefixWord, tailWord_7766376, baseEnd_7766376] using wordTrace_append hprefix tailTrace_7766376
  have hstable : (prefixWord ++ tailWord_7766376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766376).length < 2 ^ (prefixWord ++ tailWord_7766376).sum := by decide
  have hdescent : baseEnd_7766376 < baseStart_7766376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766386 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7766386 : Nat := 118140960795 + 7766386 * 2 ^ 59
def prefixEnd_7766386 : Nat := 4983230072969 + 3 ^ 40 * 7766386 * 2
def baseEnd_7766386 : Nat := 1329296322116452070919349

theorem tailTrace_7766386 : CollatzResearch.WordTrace tailWord_7766386 prefixEnd_7766386 1329296322116452070919349 := by
  unfold tailWord_7766386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70815842110429347493589753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188842245627811593316239341 70815842110429347493589753)
  ·
    refine ⟨53111881582822010620192315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70815842110429347493589753 53111881582822010620192315)
    ·
      refine ⟨79667822374233015930288473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53111881582822010620192315 79667822374233015930288473)
      ·
        refine ⟨59750866780674761947716355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79667822374233015930288473 59750866780674761947716355)
        ·
          refine ⟨89626300171012142921574533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59750866780674761947716355 89626300171012142921574533)
          ·
            refine ⟨16804931282064776797795225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89626300171012142921574533 16804931282064776797795225)
            ·
              refine ⟨12603698461548582598346419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16804931282064776797795225 12603698461548582598346419)
              ·
                refine ⟨18905547692322873897519629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603698461548582598346419 18905547692322873897519629)
                ·
                  refine ⟨7089580384621077711569861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18905547692322873897519629 7089580384621077711569861)
                  ·
                    refine ⟨1329296322116452070919349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7089580384621077711569861 1329296322116452070919349)
                    ·
                      rfl

theorem cell23_7766386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7766386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766386 prefixEnd_7766386 := by exact prefixLift 7766386
  have htrace : WordTrace (prefixWord ++ tailWord_7766386) baseStart_7766386 baseEnd_7766386 := by
    simpa [prefixWord, tailWord_7766386, baseEnd_7766386] using wordTrace_append hprefix tailTrace_7766386
  have hstable : (prefixWord ++ tailWord_7766386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766386).length < 2 ^ (prefixWord ++ tailWord_7766386).sum := by decide
  have hdescent : baseEnd_7766386 < baseStart_7766386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766436 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_7766436 : Nat := 118140960795 + 7766436 * 2 ^ 59
def prefixEnd_7766436 : Nat := 4983230072969 + 3 ^ 40 * 7766436 * 2
def baseEnd_7766436 : Nat := 3987914640382081017132817

theorem tailTrace_7766436 : CollatzResearch.WordTrace tailWord_7766436 prefixEnd_7766436 3987914640382081017132817 := by
  unfold tailWord_7766436
  simp only [CollatzResearch.WordTrace]
  refine ⟨141632596045768124256839581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188843461394357499009119441 141632596045768124256839581)
  ·
    refine ⟨53112223517163046596314843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141632596045768124256839581 53112223517163046596314843)
    ·
      refine ⟨79668335275744569894472265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53112223517163046596314843 79668335275744569894472265)
      ·
        refine ⟨59751251456808427420854199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79668335275744569894472265 59751251456808427420854199)
        ·
          refine ⟨89626877185212641131281299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59751251456808427420854199 89626877185212641131281299)
          ·
            refine ⟨134440315777818961696921949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89626877185212641131281299 134440315777818961696921949)
            ·
              refine ⟨50415118416682110636345731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134440315777818961696921949 50415118416682110636345731)
              ·
                refine ⟨75622677625023165954518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50415118416682110636345731 75622677625023165954518597)
                ·
                  refine ⟨14179252054691843616472237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75622677625023165954518597 14179252054691843616472237)
                  ·
                    refine ⟨5317219520509441356177089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14179252054691843616472237 5317219520509441356177089)
                    ·
                      refine ⟨3987914640382081017132817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317219520509441356177089 3987914640382081017132817)
                      ·
                        rfl

theorem cell23_7766436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_7766436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766436 prefixEnd_7766436 := by exact prefixLift 7766436
  have htrace : WordTrace (prefixWord ++ tailWord_7766436) baseStart_7766436 baseEnd_7766436 := by
    simpa [prefixWord, tailWord_7766436, baseEnd_7766436] using wordTrace_append hprefix tailTrace_7766436
  have hstable : (prefixWord ++ tailWord_7766436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766436).length < 2 ^ (prefixWord ++ tailWord_7766436).sum := by decide
  have hdescent : baseEnd_7766436 < baseStart_7766436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766476 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_7766476 : Nat := 118140960795 + 7766476 * 2 ^ 59
def prefixEnd_7766476 : Nat := 4983230072969 + 3 ^ 40 * 7766476 * 2
def baseEnd_7766476 : Nat := 1329311726536086953544211

theorem tailTrace_7766476 : CollatzResearch.WordTrace tailWord_7766476 prefixEnd_7766476 1329311726536086953544211 := by
  unfold tailWord_7766476
  simp only [CollatzResearch.WordTrace]
  refine ⟨141633325505695667672567641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188844434007594223563423521 141633325505695667672567641)
  ·
    refine ⟨106224994129271750754425731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141633325505695667672567641 106224994129271750754425731)
    ·
      refine ⟨159337491193907626131638597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106224994129271750754425731 159337491193907626131638597)
      ·
        refine ⟨29875779598857679899682237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159337491193907626131638597 29875779598857679899682237)
        ·
          refine ⟨11203417349571629962380839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29875779598857679899682237 11203417349571629962380839)
          ·
            refine ⟨16805126024357444943571259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203417349571629962380839 16805126024357444943571259)
            ·
              refine ⟨25207689036536167415356889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805126024357444943571259 25207689036536167415356889)
              ·
                refine ⟨18905766777402125561517667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25207689036536167415356889 18905766777402125561517667)
                ·
                  refine ⟨28358650166103188342276501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18905766777402125561517667 28358650166103188342276501)
                  ·
                    refine ⟨1329311726536086953544211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28358650166103188342276501 1329311726536086953544211)
                    ·
                      rfl

theorem cell23_7766476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_7766476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766476 prefixEnd_7766476 := by exact prefixLift 7766476
  have htrace : WordTrace (prefixWord ++ tailWord_7766476) baseStart_7766476 baseEnd_7766476 := by
    simpa [prefixWord, tailWord_7766476, baseEnd_7766476] using wordTrace_append hprefix tailTrace_7766476
  have hstable : (prefixWord ++ tailWord_7766476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766476).length < 2 ^ (prefixWord ++ tailWord_7766476).sum := by decide
  have hdescent : baseEnd_7766476 < baseStart_7766476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766493 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7766493 : Nat := 118140960795 + 7766493 * 2 ^ 59
def prefixEnd_7766493 : Nat := 4983230072969 + 3 ^ 40 * 7766493 * 2
def baseEnd_7766493 : Nat := 1329314636259795764706685

theorem tailTrace_7766493 : CollatzResearch.WordTrace tailWord_7766493 prefixEnd_7766493 1329314636259795764706685 := by
  unfold tailWord_7766493
  simp only [CollatzResearch.WordTrace]
  refine ⟨283267271052329747248504133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188844847368219831499002755 283267271052329747248504133)
  ·
    refine ⟨53112613322311827609094525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283267271052329747248504133 53112613322311827609094525)
    ·
      refine ⟨19917229995866935353410447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53112613322311827609094525 19917229995866935353410447)
      ·
        refine ⟨29875844993800403030115671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19917229995866935353410447 29875844993800403030115671)
        ·
          refine ⟨44813767490700604545173507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29875844993800403030115671 44813767490700604545173507)
          ·
            refine ⟨67220651236050906817760261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44813767490700604545173507 67220651236050906817760261)
            ·
              refine ⟨12603872106759545028330049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67220651236050906817760261 12603872106759545028330049)
              ·
                refine ⟨9452904080069658771247537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12603872106759545028330049 9452904080069658771247537)
                ·
                  refine ⟨7089678060052244078435653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9452904080069658771247537 7089678060052244078435653)
                  ·
                    refine ⟨1329314636259795764706685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7089678060052244078435653 1329314636259795764706685)
                    ·
                      rfl

theorem cell23_7766493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7766493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766493 prefixEnd_7766493 := by exact prefixLift 7766493
  have htrace : WordTrace (prefixWord ++ tailWord_7766493) baseStart_7766493 baseEnd_7766493 := by
    simpa [prefixWord, tailWord_7766493, baseEnd_7766493] using wordTrace_append hprefix tailTrace_7766493
  have hstable : (prefixWord ++ tailWord_7766493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766493).length < 2 ^ (prefixWord ++ tailWord_7766493).sum := by decide
  have hdescent : baseEnd_7766493 < baseStart_7766493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766506 : List Nat := [3, 1, 3, 1, 3, 3, 1, 8]
def baseStart_7766506 : Nat := 118140960795 + 7766506 * 2 ^ 59
def prefixEnd_7766506 : Nat := 4983230072969 + 3 ^ 40 * 7766506 * 2
def baseEnd_7766506 : Nat := 147701873482514657157685

theorem tailTrace_7766506 : CollatzResearch.WordTrace tailWord_7766506 prefixEnd_7766506 147701873482514657157685 := by
  unfold tailWord_7766506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70816936300320662617181843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188845163467521766979151581 70816936300320662617181843)
  ·
    refine ⟨106225404450480993925772765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70816936300320662617181843 106225404450480993925772765)
    ·
      refine ⟨39834526668930372722164787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106225404450480993925772765 39834526668930372722164787)
      ·
        refine ⟨59751790003395559083247181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39834526668930372722164787 59751790003395559083247181)
        ·
          refine ⟨22406921251273334656217693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59751790003395559083247181 22406921251273334656217693)
          ·
            refine ⟨8402595469227500496081635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22406921251273334656217693 8402595469227500496081635)
            ·
              refine ⟨12603893203841250744122453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402595469227500496081635 12603893203841250744122453)
              ·
                refine ⟨147701873482514657157685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12603893203841250744122453 147701873482514657157685)
                ·
                  rfl

theorem cell23_7766506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_7766506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766506 prefixEnd_7766506 := by exact prefixLift 7766506
  have htrace : WordTrace (prefixWord ++ tailWord_7766506) baseStart_7766506 baseEnd_7766506 := by
    simpa [prefixWord, tailWord_7766506, baseEnd_7766506] using wordTrace_append hprefix tailTrace_7766506
  have hstable : (prefixWord ++ tailWord_7766506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766506).length < 2 ^ (prefixWord ++ tailWord_7766506).sum := by decide
  have hdescent : baseEnd_7766506 < baseStart_7766506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766517 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7766517 : Nat := 118140960795 + 7766517 * 2 ^ 59
def prefixEnd_7766517 : Nat := 4983230072969 + 3 ^ 40 * 7766517 * 2
def baseEnd_7766517 : Nat := 3987956232315095200219945

theorem tailTrace_7766517 : CollatzResearch.WordTrace tailWord_7766517 prefixEnd_7766517 3987956232315095200219945 := by
  unfold tailWord_7766517
  simp only [CollatzResearch.WordTrace]
  refine ⟨283268146404242799347377805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188845430936161866231585203 283268146404242799347377805)
  ·
    refine ⟨106225554901591049755266677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283268146404242799347377805 106225554901591049755266677)
    ·
      refine ⟨9958645772024160914556251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106225554901591049755266677 9958645772024160914556251)
      ·
        refine ⟨14937968658036241371834377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9958645772024160914556251 14937968658036241371834377)
        ·
          refine ⟨11203476493527181028875783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14937968658036241371834377 11203476493527181028875783)
          ·
            refine ⟨16805214740290771543313675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203476493527181028875783 16805214740290771543313675)
            ·
              refine ⟨25207822110436157314970513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805214740290771543313675 25207822110436157314970513)
              ·
                refine ⟨18905866582827117986227885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25207822110436157314970513 18905866582827117986227885)
                ·
                  refine ⟨7089699968560169244835457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18905866582827117986227885 7089699968560169244835457)
                  ·
                    refine ⟨5317274976420126933626593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089699968560169244835457 5317274976420126933626593)
                    ·
                      refine ⟨3987956232315095200219945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317274976420126933626593 3987956232315095200219945)
                      ·
                        rfl

theorem cell23_7766517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7766517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766517 prefixEnd_7766517 := by exact prefixLift 7766517
  have htrace : WordTrace (prefixWord ++ tailWord_7766517) baseStart_7766517 baseEnd_7766517 := by
    simpa [prefixWord, tailWord_7766517, baseEnd_7766517] using wordTrace_append hprefix tailTrace_7766517
  have hstable : (prefixWord ++ tailWord_7766517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766517).length < 2 ^ (prefixWord ++ tailWord_7766517).sum := by decide
  have hdescent : baseEnd_7766517 < baseStart_7766517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766534 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7766534 : Nat := 118140960795 + 7766534 * 2 ^ 59
def prefixEnd_7766534 : Nat := 4983230072969 + 3 ^ 40 * 7766534 * 2
def baseEnd_7766534 : Nat := 3987964961486221633707367

theorem tailTrace_7766534 : CollatzResearch.WordTrace tailWord_7766534 prefixEnd_7766534 3987964961486221633707367 := by
  unfold tailWord_7766534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852148951411912851585833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188845844296787474167164437 8852148951411912851585833)
  ·
    refine ⟨6639111713558934638689375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8852148951411912851585833 6639111713558934638689375)
    ·
      refine ⟨9958667570338401958034063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639111713558934638689375 9958667570338401958034063)
      ·
        refine ⟨14938001355507602937051095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9958667570338401958034063 14938001355507602937051095)
        ·
          refine ⟨22407002033261404405576643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14938001355507602937051095 22407002033261404405576643)
          ·
            refine ⟨33610503049892106608364965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407002033261404405576643 33610503049892106608364965)
            ·
              refine ⟨6301969321854769989068431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33610503049892106608364965 6301969321854769989068431)
              ·
                refine ⟨9452953982782154983602647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6301969321854769989068431 9452953982782154983602647)
                ·
                  refine ⟨14179430974173232475403971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452953982782154983602647 14179430974173232475403971)
                  ·
                    refine ⟨21269146461259848713105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14179430974173232475403971 21269146461259848713105957)
                    ·
                      refine ⟨3987964961486221633707367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21269146461259848713105957 3987964961486221633707367)
                      ·
                        rfl

theorem cell23_7766534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7766534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766534 prefixEnd_7766534 := by exact prefixLift 7766534
  have htrace : WordTrace (prefixWord ++ tailWord_7766534) baseStart_7766534 baseEnd_7766534 := by
    simpa [prefixWord, tailWord_7766534, baseEnd_7766534] using wordTrace_append hprefix tailTrace_7766534
  have hstable : (prefixWord ++ tailWord_7766534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766534).length < 2 ^ (prefixWord ++ tailWord_7766534).sum := by decide
  have hdescent : baseEnd_7766534 < baseStart_7766534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766549 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7766549 : Nat := 118140960795 + 7766549 * 2 ^ 59
def prefixEnd_7766549 : Nat := 4983230072969 + 3 ^ 40 * 7766549 * 2
def baseEnd_7766549 : Nat := 1329324221232013025006599

theorem tailTrace_7766549 : CollatzResearch.WordTrace tailWord_7766549 prefixEnd_7766549 1329324221232013025006599 := by
  unfold tailWord_7766549
  simp only [CollatzResearch.WordTrace]
  refine ⟨283269313540126868812542701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188846209026751245875028467 283269313540126868812542701)
  ·
    refine ⟨106225992577547575804703513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283269313540126868812542701 106225992577547575804703513)
    ·
      refine ⟨79669494433160681853527635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106225992577547575804703513 79669494433160681853527635)
      ·
        refine ⟨119504241649741022780291453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79669494433160681853527635 119504241649741022780291453)
        ·
          refine ⟨44814090618652883542609295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119504241649741022780291453 44814090618652883542609295)
          ·
            refine ⟨67221135927979325313913943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44814090618652883542609295 67221135927979325313913943)
            ·
              refine ⟨100831703891968987970870915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67221135927979325313913943 100831703891968987970870915)
              ·
                refine ⟨151247555837953481956306373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100831703891968987970870915 151247555837953481956306373)
                ·
                  refine ⟨28358916719616277866807445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151247555837953481956306373 28358916719616277866807445)
                  ·
                    refine ⟨1329324221232013025006599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28358916719616277866807445 1329324221232013025006599)
                    ·
                      rfl

theorem cell23_7766549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7766549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766549 prefixEnd_7766549 := by exact prefixLift 7766549
  have htrace : WordTrace (prefixWord ++ tailWord_7766549) baseStart_7766549 baseEnd_7766549 := by
    simpa [prefixWord, tailWord_7766549, baseEnd_7766549] using wordTrace_append hprefix tailTrace_7766549
  have hstable : (prefixWord ++ tailWord_7766549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766549).length < 2 ^ (prefixWord ++ tailWord_7766549).sum := by decide
  have hdescent : baseEnd_7766549 < baseStart_7766549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766559 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7766559 : Nat := 118140960795 + 7766559 * 2 ^ 59
def prefixEnd_7766559 : Nat := 4983230072969 + 3 ^ 40 * 7766559 * 2
def baseEnd_7766559 : Nat := 3987977798502584035894751

theorem tailTrace_7766559 : CollatzResearch.WordTrace tailWord_7766559 prefixEnd_7766559 3987977798502584035894751 := by
  unfold tailWord_7766559
  simp only [CollatzResearch.WordTrace]
  refine ⟨283269678270090640520406731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188846452180060427013604487 283269678270090640520406731)
  ·
    refine ⟨424904517405135960780610097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283269678270090640520406731 424904517405135960780610097)
    ·
      refine ⟨318678388053851970585457573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424904517405135960780610097 318678388053851970585457573)
      ·
        refine ⟨59752197760097244484773295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318678388053851970585457573 59752197760097244484773295)
        ·
          refine ⟨89628296640145866727159943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59752197760097244484773295 89628296640145866727159943)
          ·
            refine ⟨134442444960218800090739915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89628296640145866727159943 134442444960218800090739915)
            ·
              refine ⟨201663667440328200136109873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134442444960218800090739915 201663667440328200136109873)
              ·
                refine ⟨151247750580246150102082405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201663667440328200136109873 151247750580246150102082405)
                ·
                  refine ⟨28358953233796153144140451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151247750580246150102082405 28358953233796153144140451)
                  ·
                    refine ⟨42538429850694229716210677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28358953233796153144140451 42538429850694229716210677)
                    ·
                      refine ⟨3987977798502584035894751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42538429850694229716210677 3987977798502584035894751)
                      ·
                        rfl

theorem cell23_7766559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7766559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766559 prefixEnd_7766559 := by exact prefixLift 7766559
  have htrace : WordTrace (prefixWord ++ tailWord_7766559) baseStart_7766559 baseEnd_7766559 := by
    simpa [prefixWord, tailWord_7766559, baseEnd_7766559] using wordTrace_append hprefix tailTrace_7766559
  have hstable : (prefixWord ++ tailWord_7766559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766559).length < 2 ^ (prefixWord ++ tailWord_7766559).sum := by decide
  have hdescent : baseEnd_7766559 < baseStart_7766559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766567 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7766567 : Nat := 118140960795 + 7766567 * 2 ^ 59
def prefixEnd_7766567 : Nat := 4983230072969 + 3 ^ 40 * 7766567 * 2
def baseEnd_7766567 : Nat := 3987981906347820004594715

theorem tailTrace_7766567 : CollatzResearch.WordTrace tailWord_7766567 prefixEnd_7766567 3987981906347820004594715 := by
  unfold tailWord_7766567
  simp only [CollatzResearch.WordTrace]
  refine ⟨283269970054061657886697955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188846646702707771924465303 283269970054061657886697955)
  ·
    refine ⟨424904955081092486830046933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283269970054061657886697955 424904955081092486830046933)
    ·
      refine ⟨9958709884713105160079225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 424904955081092486830046933 9958709884713105160079225)
      ·
        refine ⟨7469032413534828870059419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9958709884713105160079225 7469032413534828870059419)
        ·
          refine ⟨11203548620302243305089129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469032413534828870059419 11203548620302243305089129)
          ·
            refine ⟨8402661465226682478816847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11203548620302243305089129 8402661465226682478816847)
            ·
              refine ⟨12603992197840023718225271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402661465226682478816847 12603992197840023718225271)
              ·
                refine ⟨18905988296760035577337907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603992197840023718225271 18905988296760035577337907)
                ·
                  refine ⟨28358982445140053366006861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18905988296760035577337907 28358982445140053366006861)
                  ·
                    refine ⟨10634618416927520012252573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28358982445140053366006861 10634618416927520012252573)
                    ·
                      refine ⟨3987981906347820004594715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634618416927520012252573 3987981906347820004594715)
                      ·
                        rfl

theorem cell23_7766567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7766567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766567 prefixEnd_7766567 := by exact prefixLift 7766567
  have htrace : WordTrace (prefixWord ++ tailWord_7766567) baseStart_7766567 baseEnd_7766567 := by
    simpa [prefixWord, tailWord_7766567, baseEnd_7766567] using wordTrace_append hprefix tailTrace_7766567
  have hstable : (prefixWord ++ tailWord_7766567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766567).length < 2 ^ (prefixWord ++ tailWord_7766567).sum := by decide
  have hdescent : baseEnd_7766567 < baseStart_7766567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766579 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 7]
def baseStart_7766579 : Nat := 118140960795 + 7766579 * 2 ^ 59
def prefixEnd_7766579 : Nat := 4983230072969 + 3 ^ 40 * 7766579 * 2
def baseEnd_7766579 : Nat := 443109785346185995293851

theorem tailTrace_7766579 : CollatzResearch.WordTrace tailWord_7766579 prefixEnd_7766579 443109785346185995293851 := by
  unfold tailWord_7766579
  simp only [CollatzResearch.WordTrace]
  refine ⟨283270407730018183936134791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188846938486678789290756527 283270407730018183936134791)
  ·
    refine ⟨424905611595027275904202187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283270407730018183936134791 424905611595027275904202187)
    ·
      refine ⟨637358417392540913856303281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424905611595027275904202187 637358417392540913856303281)
      ·
        refine ⟨478018813044405685392227461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637358417392540913856303281 478018813044405685392227461)
        ·
          refine ⟨89628527445826066011042649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478018813044405685392227461 89628527445826066011042649)
          ·
            refine ⟨67221395584369549508281987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89628527445826066011042649 67221395584369549508281987)
            ·
              refine ⟨100832093376554324262422981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67221395584369549508281987 100832093376554324262422981)
              ·
                refine ⟨18906017508103935799204309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100832093376554324262422981 18906017508103935799204309)
                ·
                  refine ⟨443109785346185995293851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18906017508103935799204309 443109785346185995293851)
                  ·
                    rfl

theorem cell23_7766579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 7].length) (baseStart_7766579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766579 prefixEnd_7766579 := by exact prefixLift 7766579
  have htrace : WordTrace (prefixWord ++ tailWord_7766579) baseStart_7766579 baseEnd_7766579 := by
    simpa [prefixWord, tailWord_7766579, baseEnd_7766579] using wordTrace_append hprefix tailTrace_7766579
  have hstable : (prefixWord ++ tailWord_7766579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766579).length < 2 ^ (prefixWord ++ tailWord_7766579).sum := by decide
  have hdescent : baseEnd_7766579 < baseStart_7766579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766606 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_7766606 : Nat := 118140960795 + 7766606 * 2 ^ 59
def prefixEnd_7766606 : Nat := 4983230072969 + 3 ^ 40 * 7766606 * 2
def baseEnd_7766606 : Nat := 3988001932093345352007035

theorem tailTrace_7766606 : CollatzResearch.WordTrace tailWord_7766606 prefixEnd_7766606 3988001932093345352007035 := by
  unfold tailWord_7766606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35408924062615045943420959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188847595000613578364911781 35408924062615045943420959)
  ·
    refine ⟨53113386093922568915131439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35408924062615045943420959 53113386093922568915131439)
    ·
      refine ⟨79670079140883853372697159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53113386093922568915131439 79670079140883853372697159)
      ·
        refine ⟨119505118711325780059045739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79670079140883853372697159 119505118711325780059045739)
        ·
          refine ⟨179257678066988670088568609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119505118711325780059045739 179257678066988670088568609)
          ·
            refine ⟨134443258550241502566426457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179257678066988670088568609 134443258550241502566426457)
            ·
              refine ⟨100832443912681126924819843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134443258550241502566426457 100832443912681126924819843)
              ·
                refine ⟨151248665869021690387229765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100832443912681126924819843 151248665869021690387229765)
                ·
                  refine ⟨28359124850441566947605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151248665869021690387229765 28359124850441566947605581)
                  ·
                    refine ⟨10634671818915587605352093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28359124850441566947605581 10634671818915587605352093)
                    ·
                      refine ⟨3988001932093345352007035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634671818915587605352093 3988001932093345352007035)
                      ·
                        rfl

theorem cell23_7766606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_7766606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766606 prefixEnd_7766606 := by exact prefixLift 7766606
  have htrace : WordTrace (prefixWord ++ tailWord_7766606) baseStart_7766606 baseEnd_7766606 := by
    simpa [prefixWord, tailWord_7766606, baseEnd_7766606] using wordTrace_append hprefix tailTrace_7766606
  have hstable : (prefixWord ++ tailWord_7766606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766606).length < 2 ^ (prefixWord ++ tailWord_7766606).sum := by decide
  have hdescent : baseEnd_7766606 < baseStart_7766606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766639 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 8]
def baseStart_7766639 : Nat := 118140960795 + 7766639 * 2 ^ 59
def prefixEnd_7766639 : Nat := 4983230072969 + 3 ^ 40 * 7766639 * 2
def baseEnd_7766639 : Nat := 1329339625651647907631461

theorem tailTrace_7766639 : CollatzResearch.WordTrace tailWord_7766639 prefixEnd_7766639 1329339625651647907631461 := by
  unfold tailWord_7766639
  simp only [CollatzResearch.WordTrace]
  refine ⟨283272596109800814183318971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188848397406533876122212647 283272596109800814183318971)
  ·
    refine ⟨424908894164701221274978457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283272596109800814183318971 424908894164701221274978457)
    ·
      refine ⟨318681670623525915956233843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424908894164701221274978457 318681670623525915956233843)
      ·
        refine ⟨478022505935288873934350765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318681670623525915956233843 478022505935288873934350765)
        ·
          refine ⟨179258439725733327725381537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478022505935288873934350765 179258439725733327725381537)
          ·
            refine ⟨134443829794299995794036153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179258439725733327725381537 134443829794299995794036153)
            ·
              refine ⟨100832872345724996845527115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134443829794299995794036153 100832872345724996845527115)
              ·
                refine ⟨151249308518587495268290673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100832872345724996845527115 151249308518587495268290673)
                ·
                  refine ⟨113436981388940621451218005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151249308518587495268290673 113436981388940621451218005)
                  ·
                    refine ⟨1329339625651647907631461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113436981388940621451218005 1329339625651647907631461)
                    ·
                      rfl

theorem cell23_7766639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_7766639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766639 prefixEnd_7766639 := by exact prefixLift 7766639
  have htrace : WordTrace (prefixWord ++ tailWord_7766639) baseStart_7766639 baseEnd_7766639 := by
    simpa [prefixWord, tailWord_7766639, baseEnd_7766639] using wordTrace_append hprefix tailTrace_7766639
  have hstable : (prefixWord ++ tailWord_7766639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766639).length < 2 ^ (prefixWord ++ tailWord_7766639).sum := by decide
  have hdescent : baseEnd_7766639 < baseStart_7766639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766658 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7766658 : Nat := 118140960795 + 7766658 * 2 ^ 59
def prefixEnd_7766658 : Nat := 4983230072969 + 3 ^ 40 * 7766658 * 2
def baseEnd_7766658 : Nat := 3988028633087379148556797

theorem tailTrace_7766658 : CollatzResearch.WordTrace tailWord_7766658 prefixEnd_7766658 3988028633087379148556797 := by
  unfold tailWord_7766658
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818322274182995107065157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188848859397821320285507085 70818322274182995107065157)
  ·
    refine ⟨13278435426409311582574717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70818322274182995107065157 13278435426409311582574717)
    ·
      refine ⟨4979413284903491843465519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13278435426409311582574717 4979413284903491843465519)
      ·
        refine ⟨7469119927355237765198279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979413284903491843465519 7469119927355237765198279)
        ·
          refine ⟨11203679891032856647797419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469119927355237765198279 11203679891032856647797419)
          ·
            refine ⟨16805519836549284971696129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203679891032856647797419 16805519836549284971696129)
            ·
              refine ⟨12604139877411963728772097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16805519836549284971696129 12604139877411963728772097)
              ·
                refine ⟨9453104908058972796579073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604139877411963728772097 9453104908058972796579073)
                ·
                  refine ⟨7089828681044229597434305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453104908058972796579073 7089828681044229597434305)
                  ·
                    refine ⟨5317371510783172198075729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089828681044229597434305 5317371510783172198075729)
                    ·
                      refine ⟨3988028633087379148556797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317371510783172198075729 3988028633087379148556797)
                      ·
                        rfl

theorem cell23_7766658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7766658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766658 prefixEnd_7766658 := by exact prefixLift 7766658
  have htrace : WordTrace (prefixWord ++ tailWord_7766658) baseStart_7766658 baseEnd_7766658 := by
    simpa [prefixWord, tailWord_7766658, baseEnd_7766658] using wordTrace_append hprefix tailTrace_7766658
  have hstable : (prefixWord ++ tailWord_7766658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766658).length < 2 ^ (prefixWord ++ tailWord_7766658).sum := by decide
  have hdescent : baseEnd_7766658 < baseStart_7766658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766663 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_7766663 : Nat := 118140960795 + 7766663 * 2 ^ 59
def prefixEnd_7766663 : Nat := 4983230072969 + 3 ^ 40 * 7766663 * 2
def baseEnd_7766663 : Nat := 3988031200490651628994273

theorem tailTrace_7766663 : CollatzResearch.WordTrace tailWord_7766663 prefixEnd_7766663 3988031200490651628994273 := by
  unfold tailWord_7766663
  simp only [CollatzResearch.WordTrace]
  refine ⟨283273471461713866282192643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188848980974475910854795095 283273471461713866282192643)
  ·
    refine ⟨424910207192570799423288965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283273471461713866282192643 424910207192570799423288965)
    ·
      refine ⟨79670663848607024891866681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424910207192570799423288965 79670663848607024891866681)
      ·
        refine ⟨59752997886455268668900011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79670663848607024891866681 59752997886455268668900011)
        ·
          refine ⟨89629496829682903003350017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59752997886455268668900011 89629496829682903003350017)
          ·
            refine ⟨67222122622262177252512513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89629496829682903003350017 67222122622262177252512513)
            ·
              refine ⟨50416591966696632939384385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67222122622262177252512513 50416591966696632939384385)
              ·
                refine ⟨37812443975022474704538289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50416591966696632939384385 37812443975022474704538289)
                ·
                  refine ⟨28359332981266856028403717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37812443975022474704538289 28359332981266856028403717)
                  ·
                    refine ⟨5317374933987535505325697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28359332981266856028403717 5317374933987535505325697)
                    ·
                      refine ⟨3988031200490651628994273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317374933987535505325697 3988031200490651628994273)
                      ·
                        rfl

theorem cell23_7766663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_7766663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766663 prefixEnd_7766663 := by exact prefixLift 7766663
  have htrace : WordTrace (prefixWord ++ tailWord_7766663) baseStart_7766663 baseEnd_7766663 := by
    simpa [prefixWord, tailWord_7766663, baseEnd_7766663] using wordTrace_append hprefix tailTrace_7766663
  have hstable : (prefixWord ++ tailWord_7766663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766663).length < 2 ^ (prefixWord ++ tailWord_7766663).sum := by decide
  have hdescent : baseEnd_7766663 < baseStart_7766663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766713 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7766713 : Nat := 118140960795 + 7766713 * 2 ^ 59
def prefixEnd_7766713 : Nat := 4983230072969 + 3 ^ 40 * 7766713 * 2
def baseEnd_7766713 : Nat := 3988056874523376433369043

theorem tailTrace_7766713 : CollatzResearch.WordTrace tailWord_7766713 prefixEnd_7766713 3988056874523376433369043 := by
  unfold tailWord_7766713
  simp only [CollatzResearch.WordTrace]
  refine ⟨283275295111532724821512793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188850196741021816547675195 283275295111532724821512793)
  ·
    refine ⟨212456471333649543616134595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283275295111532724821512793 212456471333649543616134595)
    ·
      refine ⟨318684707000474315424201893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212456471333649543616134595 318684707000474315424201893)
      ·
        refine ⟨59753382562588934142037855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318684707000474315424201893 59753382562588934142037855)
        ·
          refine ⟨89630073843883401213056783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59753382562588934142037855 89630073843883401213056783)
          ·
            refine ⟨134445110765825101819585175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89630073843883401213056783 134445110765825101819585175)
            ·
              refine ⟨201667666148737652729377763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134445110765825101819585175 201667666148737652729377763)
              ·
                refine ⟨302501499223106479094066645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201667666148737652729377763 302501499223106479094066645)
                ·
                  refine ⟨7089878888041558103767187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 302501499223106479094066645 7089878888041558103767187)
                  ·
                    refine ⟨10634818332062337155650781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7089878888041558103767187 10634818332062337155650781)
                    ·
                      refine ⟨3988056874523376433369043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634818332062337155650781 3988056874523376433369043)
                      ·
                        rfl

theorem cell23_7766713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7766713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766713 prefixEnd_7766713 := by exact prefixLift 7766713
  have htrace : WordTrace (prefixWord ++ tailWord_7766713) baseStart_7766713 baseEnd_7766713 := by
    simpa [prefixWord, tailWord_7766713, baseEnd_7766713] using wordTrace_append hprefix tailTrace_7766713
  have hstable : (prefixWord ++ tailWord_7766713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766713).length < 2 ^ (prefixWord ++ tailWord_7766713).sum := by decide
  have hdescent : baseEnd_7766713 < baseStart_7766713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766730 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_7766730 : Nat := 118140960795 + 7766730 * 2 ^ 59
def prefixEnd_7766730 : Nat := 4983230072969 + 3 ^ 40 * 7766730 * 2
def baseEnd_7766730 : Nat := 3988065603694502866856465

theorem tailTrace_7766730 : CollatzResearch.WordTrace tailWord_7766730 prefixEnd_7766730 3988065603694502866856465 := by
  unfold tailWord_7766730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70818978788117784181220411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188850610101647424483254429 70818978788117784181220411)
  ·
    refine ⟨106228468182176676271830617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70818978788117784181220411 106228468182176676271830617)
    ·
      refine ⟨79671351136632507203872963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106228468182176676271830617 79671351136632507203872963)
      ·
        refine ⟨119507026704948760805809445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79671351136632507203872963 119507026704948760805809445)
        ·
          refine ⟨22407567507177892651089271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119507026704948760805809445 22407567507177892651089271)
          ·
            refine ⟨33611351260766838976633907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407567507177892651089271 33611351260766838976633907)
            ·
              refine ⟨50417026891150258464950861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33611351260766838976633907 50417026891150258464950861)
              ·
                refine ⟨18906385084181346924356573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50417026891150258464950861 18906385084181346924356573)
                ·
                  refine ⟨7089894406568005096633715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18906385084181346924356573 7089894406568005096633715)
                  ·
                    refine ⟨10634841609852007644950573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7089894406568005096633715 10634841609852007644950573)
                    ·
                      refine ⟨3988065603694502866856465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634841609852007644950573 3988065603694502866856465)
                      ·
                        rfl

theorem cell23_7766730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_7766730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766730 prefixEnd_7766730 := by exact prefixLift 7766730
  have htrace : WordTrace (prefixWord ++ tailWord_7766730) baseStart_7766730 baseEnd_7766730 := by
    simpa [prefixWord, tailWord_7766730, baseEnd_7766730] using wordTrace_append hprefix tailTrace_7766730
  have hstable : (prefixWord ++ tailWord_7766730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766730).length < 2 ^ (prefixWord ++ tailWord_7766730).sum := by decide
  have hdescent : baseEnd_7766730 < baseStart_7766730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766770 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7766770 : Nat := 118140960795 + 7766770 * 2 ^ 59
def prefixEnd_7766770 : Nat := 4983230072969 + 3 ^ 40 * 7766770 * 2
def baseEnd_7766770 : Nat := 3988086142920682710356281

theorem tailTrace_7766770 : CollatzResearch.WordTrace tailWord_7766770 prefixEnd_7766770 3988086142920682710356281 := by
  unfold tailWord_7766770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70819343518081555889084441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188851582714884149037558509 70819343518081555889084441)
  ·
    refine ⟨53114507638561166916813331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70819343518081555889084441 53114507638561166916813331)
    ·
      refine ⟨79671761457841750375219997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53114507638561166916813331 79671761457841750375219997)
      ·
        refine ⟨29876910546690656390707499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79671761457841750375219997 29876910546690656390707499)
        ·
          refine ⟨44815365820035984586061249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29876910546690656390707499 44815365820035984586061249)
          ·
            refine ⟨33611524365026988439545937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44815365820035984586061249 33611524365026988439545937)
            ·
              refine ⟨25208643273770241329659453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33611524365026988439545937 25208643273770241329659453)
              ·
                refine ⟨9453241227663840498622295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25208643273770241329659453 9453241227663840498622295)
                ·
                  refine ⟨14179861841495760747933443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9453241227663840498622295 14179861841495760747933443)
                  ·
                    refine ⟨21269792762243641121900165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14179861841495760747933443 21269792762243641121900165)
                    ·
                      refine ⟨3988086142920682710356281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21269792762243641121900165 3988086142920682710356281)
                      ·
                        rfl

theorem cell23_7766770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7766770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766770 prefixEnd_7766770 := by exact prefixLift 7766770
  have htrace : WordTrace (prefixWord ++ tailWord_7766770) baseStart_7766770 baseEnd_7766770 := by
    simpa [prefixWord, tailWord_7766770, baseEnd_7766770] using wordTrace_append hprefix tailTrace_7766770
  have hstable : (prefixWord ++ tailWord_7766770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766770).length < 2 ^ (prefixWord ++ tailWord_7766770).sum := by decide
  have hdescent : baseEnd_7766770 < baseStart_7766770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766796 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7766796 : Nat := 118140960795 + 7766796 * 2 ^ 59
def prefixEnd_7766796 : Nat := 4983230072969 + 3 ^ 40 * 7766796 * 2
def baseEnd_7766796 : Nat := 3988099493417699608631161

theorem tailTrace_7766796 : CollatzResearch.WordTrace tailWord_7766796 prefixEnd_7766796 3988099493417699608631161 := by
  unfold tailWord_7766796
  simp only [CollatzResearch.WordTrace]
  refine ⟨141639161185116014998392121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188852214913488019997856161 141639161185116014998392121)
  ·
    refine ⟨106229370888837011248794091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141639161185116014998392121 106229370888837011248794091)
    ·
      refine ⟨159344056333255516873191137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106229370888837011248794091 159344056333255516873191137)
      ·
        refine ⟨119508042249941637654893353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159344056333255516873191137 119508042249941637654893353)
        ·
          refine ⟨89631031687456228241170015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119508042249941637654893353 89631031687456228241170015)
          ·
            refine ⟨134446547531184342361755023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89631031687456228241170015 134446547531184342361755023)
            ·
              refine ⟨201669821296776513542632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134446547531184342361755023 201669821296776513542632535)
              ·
                refine ⟨302504731945164770313948803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201669821296776513542632535 302504731945164770313948803)
                ·
                  refine ⟨453757097917747155470923205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302504731945164770313948803 453757097917747155470923205)
                  ·
                    refine ⟨85079455859577591650798101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453757097917747155470923205 85079455859577591650798101)
                    ·
                      refine ⟨3988099493417699608631161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85079455859577591650798101 3988099493417699608631161)
                      ·
                        rfl

theorem cell23_7766796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7766796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766796 prefixEnd_7766796 := by exact prefixLift 7766796
  have htrace : WordTrace (prefixWord ++ tailWord_7766796) baseStart_7766796 baseEnd_7766796 := by
    simpa [prefixWord, tailWord_7766796, baseEnd_7766796] using wordTrace_append hprefix tailTrace_7766796
  have hstable : (prefixWord ++ tailWord_7766796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766796).length < 2 ^ (prefixWord ++ tailWord_7766796).sum := by decide
  have hdescent : baseEnd_7766796 < baseStart_7766796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766803 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3]
def baseStart_7766803 : Nat := 118140960795 + 7766803 * 2 ^ 59
def prefixEnd_7766803 : Nat := 4983230072969 + 3 ^ 40 * 7766803 * 2
def baseEnd_7766803 : Nat := 3988103087782281081243629

theorem tailTrace_7766803 : CollatzResearch.WordTrace tailWord_7766803 prefixEnd_7766803 3988103087782281081243629 := by
  unfold tailWord_7766803
  simp only [CollatzResearch.WordTrace]
  refine ⟨283278577681206670192289063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188852385120804446794859375 283278577681206670192289063)
  ·
    refine ⟨424917866521810005288433595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283278577681206670192289063 424917866521810005288433595)
    ·
      refine ⟨637376799782715007932650393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424917866521810005288433595 637376799782715007932650393)
      ·
        refine ⟨478032599837036255949487795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637376799782715007932650393 478032599837036255949487795)
        ·
          refine ⟨717048899755554383924231693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478032599837036255949487795 717048899755554383924231693)
          ·
            refine ⟨268893337408332893971586885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717048899755554383924231693 268893337408332893971586885)
            ·
              refine ⟨50417500764062417619672541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268893337408332893971586885 50417500764062417619672541)
              ·
                refine ⟨18906562786523406607377203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50417500764062417619672541 18906562786523406607377203)
                ·
                  refine ⟨28359844179785109911065805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18906562786523406607377203 28359844179785109911065805)
                  ·
                    refine ⟨10634941567419416216649677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28359844179785109911065805 10634941567419416216649677)
                    ·
                      refine ⟨3988103087782281081243629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634941567419416216649677 3988103087782281081243629)
                      ·
                        rfl

theorem cell23_7766803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_7766803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766803 prefixEnd_7766803 := by exact prefixLift 7766803
  have htrace : WordTrace (prefixWord ++ tailWord_7766803) baseStart_7766803 baseEnd_7766803 := by
    simpa [prefixWord, tailWord_7766803, baseEnd_7766803] using wordTrace_append hprefix tailTrace_7766803
  have hstable : (prefixWord ++ tailWord_7766803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766803).length < 2 ^ (prefixWord ++ tailWord_7766803).sum := by decide
  have hdescent : baseEnd_7766803 < baseStart_7766803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766837 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_7766837 : Nat := 118140960795 + 7766837 * 2 ^ 59
def prefixEnd_7766837 : Nat := 4983230072969 + 3 ^ 40 * 7766837 * 2
def baseEnd_7766837 : Nat := 3988120546124533948218473

theorem tailTrace_7766837 : CollatzResearch.WordTrace tailWord_7766837 prefixEnd_7766837 3988120546124533948218473 := by
  unfold tailWord_7766837
  simp only [CollatzResearch.WordTrace]
  refine ⟨283279817763083493999026765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188853211842055662666017843 283279817763083493999026765)
  ·
    refine ⟨106229931661156310249635037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283279817763083493999026765 106229931661156310249635037)
    ·
      refine ⟨39836224372933616343613139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106229931661156310249635037 39836224372933616343613139)
      ·
        refine ⟨59754336559400424515419709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39836224372933616343613139 59754336559400424515419709)
        ·
          refine ⟨22407876209775159193282391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59754336559400424515419709 22407876209775159193282391)
          ·
            refine ⟨33611814314662738789923587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407876209775159193282391 33611814314662738789923587)
            ·
              refine ⟨50417721471994108184885381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33611814314662738789923587 50417721471994108184885381)
              ·
                refine ⟨9453322775998895284666009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50417721471994108184885381 9453322775998895284666009)
                ·
                  refine ⟨7089992081999171463499507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453322775998895284666009 7089992081999171463499507)
                  ·
                    refine ⟨10634988122998757195249261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7089992081999171463499507 10634988122998757195249261)
                    ·
                      refine ⟨3988120546124533948218473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10634988122998757195249261 3988120546124533948218473)
                      ·
                        rfl

theorem cell23_7766837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_7766837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766837 prefixEnd_7766837 := by exact prefixLift 7766837
  have htrace : WordTrace (prefixWord ++ tailWord_7766837) baseStart_7766837 baseEnd_7766837 := by
    simpa [prefixWord, tailWord_7766837, baseEnd_7766837] using wordTrace_append hprefix tailTrace_7766837
  have hstable : (prefixWord ++ tailWord_7766837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766837).length < 2 ^ (prefixWord ++ tailWord_7766837).sum := by decide
  have hdescent : baseEnd_7766837 < baseStart_7766837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766838 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7766838 : Nat := 118140960795 + 7766838 * 2 ^ 59
def prefixEnd_7766838 : Nat := 4983230072969 + 3 ^ 40 * 7766838 * 2
def baseEnd_7766838 : Nat := 3988121059605188444305969

theorem tailTrace_7766838 : CollatzResearch.WordTrace tailWord_7766838 prefixEnd_7766838 3988121059605188444305969 := by
  unfold tailWord_7766838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704990889754991948113323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188853236157386580779875445 17704990889754991948113323)
  ·
    refine ⟨26557486334632487922169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17704990889754991948113323 26557486334632487922169985)
    ·
      refine ⟨19918114750974365941627489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26557486334632487922169985 19918114750974365941627489)
      ·
        refine ⟨14938586063230774456220617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19918114750974365941627489 14938586063230774456220617)
        ·
          refine ⟨11203939547423080842165463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14938586063230774456220617 11203939547423080842165463)
          ·
            refine ⟨16805909321134621263248195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11203939547423080842165463 16805909321134621263248195)
            ·
              refine ⟨25208863981701931894872293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16805909321134621263248195 25208863981701931894872293)
              ·
                refine ⟨4726661996569112230288555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25208863981701931894872293 4726661996569112230288555)
                ·
                  refine ⟨7089992994853668345432833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726661996569112230288555 7089992994853668345432833)
                  ·
                    refine ⟨5317494746140251259074625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7089992994853668345432833 5317494746140251259074625)
                    ·
                      refine ⟨3988121059605188444305969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317494746140251259074625 3988121059605188444305969)
                      ·
                        rfl

theorem cell23_7766838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7766838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766838 prefixEnd_7766838 := by exact prefixLift 7766838
  have htrace : WordTrace (prefixWord ++ tailWord_7766838) baseStart_7766838 baseEnd_7766838 := by
    simpa [prefixWord, tailWord_7766838, baseEnd_7766838] using wordTrace_append hprefix tailTrace_7766838
  have hstable : (prefixWord ++ tailWord_7766838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766838).length < 2 ^ (prefixWord ++ tailWord_7766838).sum := by decide
  have hdescent : baseEnd_7766838 < baseStart_7766838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766963 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_7766963 : Nat := 118140960795 + 7766963 * 2 ^ 59
def prefixEnd_7766963 : Nat := 4983230072969 + 3 ^ 40 * 7766963 * 2
def baseEnd_7766963 : Nat := 3988185244687000455242893

theorem tailTrace_7766963 : CollatzResearch.WordTrace tailWord_7766963 prefixEnd_7766963 3988185244687000455242893 := by
  unfold tailWord_7766963
  simp only [CollatzResearch.WordTrace]
  refine ⟨283284413360627017518113543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188856275573751345012075695 283284413360627017518113543)
  ·
    refine ⟨424926620040940526277170315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283284413360627017518113543 424926620040940526277170315)
    ·
      refine ⟨637389930061410789415755473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424926620040940526277170315 637389930061410789415755473)
      ·
        refine ⟨478042447546058092061816605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637389930061410789415755473 478042447546058092061816605)
        ·
          refine ⟨179265917829771784523181227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478042447546058092061816605 179265917829771784523181227)
          ·
            refine ⟨268898876744657676784771841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179265917829771784523181227 268898876744657676784771841)
            ·
              refine ⟨201674157558493257588578881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268898876744657676784771841 201674157558493257588578881)
              ·
                refine ⟨151255618168869943191434161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201674157558493257588578881 151255618168869943191434161)
                ·
                  refine ⟨113441713626652457393575621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151255618168869943191434161 113441713626652457393575621)
                  ·
                    refine ⟨21270321304997335761295429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113441713626652457393575621 21270321304997335761295429)
                    ·
                      refine ⟨3988185244687000455242893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21270321304997335761295429 3988185244687000455242893)
                      ·
                        rfl

theorem cell23_7766963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_7766963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766963 prefixEnd_7766963 := by exact prefixLift 7766963
  have htrace : WordTrace (prefixWord ++ tailWord_7766963) baseStart_7766963 baseEnd_7766963 := by
    simpa [prefixWord, tailWord_7766963, baseEnd_7766963] using wordTrace_append hprefix tailTrace_7766963
  have hstable : (prefixWord ++ tailWord_7766963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766963).length < 2 ^ (prefixWord ++ tailWord_7766963).sum := by decide
  have hdescent : baseEnd_7766963 < baseStart_7766963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766970 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_7766970 : Nat := 118140960795 + 7766970 * 2 ^ 59
def prefixEnd_7766970 : Nat := 4983230072969 + 3 ^ 40 * 7766970 * 2
def baseEnd_7766970 : Nat := 3988188839051581927855361

theorem tailTrace_7766970 : CollatzResearch.WordTrace tailWord_7766970 prefixEnd_7766970 3988188839051581927855361 := by
  unfold tailWord_7766970
  simp only [CollatzResearch.WordTrace]
  refine ⟨70821167167900414428404591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188856445781067771809078909 70821167167900414428404591)
  ·
    refine ⟨106231750751850621642606887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70821167167900414428404591 106231750751850621642606887)
    ·
      refine ⟨159347626127775932463910331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106231750751850621642606887 159347626127775932463910331)
      ·
        refine ⟨239021439191663898695865497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159347626127775932463910331 239021439191663898695865497)
        ·
          refine ⟨179266079393747924021899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239021439191663898695865497 179266079393747924021899123)
          ·
            refine ⟨268899119090621886032848685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179266079393747924021899123 268899119090621886032848685)
            ·
              refine ⟨100837169658983207262318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268899119090621886032848685 100837169658983207262318257)
              ·
                refine ⟨75627877244237405446738693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100837169658983207262318257 75627877244237405446738693)
                ·
                  refine ⟨14180226983294513521263505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75627877244237405446738693 14180226983294513521263505)
                  ·
                    refine ⟨10635170237470885140947629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14180226983294513521263505 10635170237470885140947629)
                    ·
                      refine ⟨3988188839051581927855361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635170237470885140947629 3988188839051581927855361)
                      ·
                        rfl

theorem cell23_7766970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_7766970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766970 prefixEnd_7766970 := by exact prefixLift 7766970
  have htrace : WordTrace (prefixWord ++ tailWord_7766970) baseStart_7766970 baseEnd_7766970 := by
    simpa [prefixWord, tailWord_7766970, baseEnd_7766970] using wordTrace_append hprefix tailTrace_7766970
  have hstable : (prefixWord ++ tailWord_7766970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766970).length < 2 ^ (prefixWord ++ tailWord_7766970).sum := by decide
  have hdescent : baseEnd_7766970 < baseStart_7766970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7766987 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3]
def baseStart_7766987 : Nat := 118140960795 + 7766987 * 2 ^ 59
def prefixEnd_7766987 : Nat := 4983230072969 + 3 ^ 40 * 7766987 * 2
def baseEnd_7766987 : Nat := 3988197568222708361342783

theorem tailTrace_7766987 : CollatzResearch.WordTrace tailWord_7766987 prefixEnd_7766987 3988197568222708361342783 := by
  unfold tailWord_7766987
  simp only [CollatzResearch.WordTrace]
  refine ⟨283285288712540069616987215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188856859141693379744658143 283285288712540069616987215)
  ·
    refine ⟨424927933068810104425480823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283285288712540069616987215 424927933068810104425480823)
    ·
      refine ⟨637391899603215156638221235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424927933068810104425480823 637391899603215156638221235)
      ·
        refine ⟨956087849404822734957331853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637391899603215156638221235 956087849404822734957331853)
        ·
          refine ⟨358532943526808525608999445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 956087849404822734957331853 358532943526808525608999445)
          ·
            refine ⟨16806231727819149637921849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358532943526808525608999445 16806231727819149637921849)
            ·
              refine ⟨12604673795864362228441387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806231727819149637921849 12604673795864362228441387)
              ·
                refine ⟨18907010693796543342662081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604673795864362228441387 18907010693796543342662081)
                ·
                  refine ⟨14180258020347407506996561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18907010693796543342662081 14180258020347407506996561)
                  ·
                    refine ⟨10635193515260555630247421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14180258020347407506996561 10635193515260555630247421)
                    ·
                      refine ⟨3988197568222708361342783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635193515260555630247421 3988197568222708361342783)
                      ·
                        rfl

theorem cell23_7766987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].length) (baseStart_7766987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7766987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7766987 prefixEnd_7766987 := by exact prefixLift 7766987
  have htrace : WordTrace (prefixWord ++ tailWord_7766987) baseStart_7766987 baseEnd_7766987 := by
    simpa [prefixWord, tailWord_7766987, baseEnd_7766987] using wordTrace_append hprefix tailTrace_7766987
  have hstable : (prefixWord ++ tailWord_7766987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7766987).length < 2 ^ (prefixWord ++ tailWord_7766987).sum := by decide
  have hdescent : baseEnd_7766987 < baseStart_7766987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7766987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767007 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 6]
def baseStart_7767007 : Nat := 118140960795 + 7767007 * 2 ^ 59
def prefixEnd_7767007 : Nat := 4983230072969 + 3 ^ 40 * 7767007 * 2
def baseEnd_7767007 : Nat := 443134204203977587010299

theorem tailTrace_7767007 : CollatzResearch.WordTrace tailWord_7767007 prefixEnd_7767007 443134204203977587010299 := by
  unfold tailWord_7767007
  simp only [CollatzResearch.WordTrace]
  refine ⟨283286018172467613032715275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188857345448311742021810183 283286018172467613032715275)
  ·
    refine ⟨424929027258701419549072913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283286018172467613032715275 424929027258701419549072913)
    ·
      refine ⟨318696770444026064661804685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424929027258701419549072913 318696770444026064661804685)
      ·
        refine ⟨119511288916509774248176757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318696770444026064661804685 119511288916509774248176757)
        ·
          refine ⟨11204183335922791335766571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119511288916509774248176757 11204183335922791335766571)
          ·
            refine ⟨16806275003884187003649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204183335922791335766571 16806275003884187003649857)
            ·
              refine ⟨12604706252913140252737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806275003884187003649857 12604706252913140252737393)
              ·
                refine ⟨9453529689684855189553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604706252913140252737393 9453529689684855189553045)
                ·
                  refine ⟨443134204203977587010299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9453529689684855189553045 443134204203977587010299)
                  ·
                    rfl

theorem cell23_7767007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 6].length) (baseStart_7767007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767007 prefixEnd_7767007 := by exact prefixLift 7767007
  have htrace : WordTrace (prefixWord ++ tailWord_7767007) baseStart_7767007 baseEnd_7767007 := by
    simpa [prefixWord, tailWord_7767007, baseEnd_7767007] using wordTrace_append hprefix tailTrace_7767007
  have hstable : (prefixWord ++ tailWord_7767007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767007).length < 2 ^ (prefixWord ++ tailWord_7767007).sum := by decide
  have hdescent : baseEnd_7767007 < baseStart_7767007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767038 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7767038 : Nat := 118140960795 + 7767038 * 2 ^ 59
def prefixEnd_7767038 : Nat := 4983230072969 + 3 ^ 40 * 7767038 * 2
def baseEnd_7767038 : Nat := 3988223755736087661805049

theorem tailTrace_7767038 : CollatzResearch.WordTrace tailWord_7767038 prefixEnd_7767038 3988223755736087661805049 := by
  unfold tailWord_7767038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35410893604419413165886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188858099223570203551395845 35410893604419413165886721)
  ·
    refine ⟨26558170203314559874415041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35410893604419413165886721 26558170203314559874415041)
    ·
      refine ⟨19918627652485919905811281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26558170203314559874415041 19918627652485919905811281)
      ·
        refine ⟨14938970739364439929358461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19918627652485919905811281 14938970739364439929358461)
        ·
          refine ⟨5602114027261664973509423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14938970739364439929358461 5602114027261664973509423)
          ·
            refine ⟨8403171040892497460264135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602114027261664973509423 8403171040892497460264135)
            ·
              refine ⟨12604756561338746190396203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403171040892497460264135 12604756561338746190396203)
              ·
                refine ⟨18907134842008119285594305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12604756561338746190396203 18907134842008119285594305)
                ·
                  refine ⟨14180351131506089464195729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18907134842008119285594305 14180351131506089464195729)
                  ·
                    refine ⟨10635263348629567098146797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14180351131506089464195729 10635263348629567098146797)
                    ·
                      refine ⟨3988223755736087661805049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635263348629567098146797 3988223755736087661805049)
                      ·
                        rfl

theorem cell23_7767038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7767038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767038 prefixEnd_7767038 := by exact prefixLift 7767038
  have htrace : WordTrace (prefixWord ++ tailWord_7767038) baseStart_7767038 baseEnd_7767038 := by
    simpa [prefixWord, tailWord_7767038, baseEnd_7767038] using wordTrace_append hprefix tailTrace_7767038
  have hstable : (prefixWord ++ tailWord_7767038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767038).length < 2 ^ (prefixWord ++ tailWord_7767038).sum := by decide
  have hdescent : baseEnd_7767038 < baseStart_7767038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767051 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 1, 1, 3]
def baseStart_7767051 : Nat := 118140960795 + 7767051 * 2 ^ 59
def prefixEnd_7767051 : Nat := 4983230072969 + 3 ^ 40 * 7767051 * 2
def baseEnd_7767051 : Nat := 3988230430984596110942489

theorem tailTrace_7767051 : CollatzResearch.WordTrace tailWord_7767051 prefixEnd_7767051 3988230430984596110942489 := by
  unfold tailWord_7767051
  simp only [CollatzResearch.WordTrace]
  refine ⟨283287622984308208547317007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188858415322872139031544671 283287622984308208547317007)
  ·
    refine ⟨424931434476462312820975511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283287622984308208547317007 424931434476462312820975511)
    ·
      refine ⟨637397151714693469231463267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424931434476462312820975511 637397151714693469231463267)
      ·
        refine ⟨956095727572040203847194901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637397151714693469231463267 956095727572040203847194901)
        ·
          refine ⟨44816987229939384555337261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 956095727572040203847194901 44816987229939384555337261)
          ·
            refine ⟨16806370211227269208251473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44816987229939384555337261 16806370211227269208251473)
            ·
              refine ⟨12604777658420451906188605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806370211227269208251473 12604777658420451906188605)
              ·
                refine ⟨4726791621907669464820727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12604777658420451906188605 4726791621907669464820727)
                ·
                  refine ⟨7090187432861504197231091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4726791621907669464820727 7090187432861504197231091)
                  ·
                    refine ⟨10635281149292256295846637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090187432861504197231091 10635281149292256295846637)
                    ·
                      refine ⟨3988230430984596110942489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635281149292256295846637 3988230430984596110942489)
                      ·
                        rfl

theorem cell23_7767051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 1, 3].length) (baseStart_7767051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767051 prefixEnd_7767051 := by exact prefixLift 7767051
  have htrace : WordTrace (prefixWord ++ tailWord_7767051) baseStart_7767051 baseEnd_7767051 := by
    simpa [prefixWord, tailWord_7767051, baseEnd_7767051] using wordTrace_append hprefix tailTrace_7767051
  have hstable : (prefixWord ++ tailWord_7767051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767051).length < 2 ^ (prefixWord ++ tailWord_7767051).sum := by decide
  have hdescent : baseEnd_7767051 < baseStart_7767051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767054 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_7767054 : Nat := 118140960795 + 7767054 * 2 ^ 59
def prefixEnd_7767054 : Nat := 4983230072969 + 3 ^ 40 * 7767054 * 2
def baseEnd_7767054 : Nat := 1329410657142186533068325

theorem tailTrace_7767054 : CollatzResearch.WordTrace tailWord_7767054 prefixEnd_7767054 1329410657142186533068325 := by
  unfold tailWord_7767054
  simp only [CollatzResearch.WordTrace]
  refine ⟨35410966550412167507459527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188858488268864893373117477 35410966550412167507459527)
  ·
    refine ⟨53116449825618251261189291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35410966550412167507459527 53116449825618251261189291)
    ·
      refine ⟨79674674738427376891783937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53116449825618251261189291 79674674738427376891783937)
      ·
        refine ⟨59756006053820532668837953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79674674738427376891783937 59756006053820532668837953)
        ·
          refine ⟨44817004540365399501628465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59756006053820532668837953 44817004540365399501628465)
          ·
            refine ⟨33612753405274049626221349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44817004540365399501628465 33612753405274049626221349)
            ·
              refine ⟨6302391263488884304916503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33612753405274049626221349 6302391263488884304916503)
              ·
                refine ⟨9453586895233326457374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302391263488884304916503 9453586895233326457374755)
                ·
                  refine ⟨14180380342849989686062133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9453586895233326457374755 14180380342849989686062133)
                  ·
                    refine ⟨1329410657142186533068325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14180380342849989686062133 1329410657142186533068325)
                    ·
                      rfl

theorem cell23_7767054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_7767054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767054 prefixEnd_7767054 := by exact prefixLift 7767054
  have htrace : WordTrace (prefixWord ++ tailWord_7767054) baseStart_7767054 baseEnd_7767054 := by
    simpa [prefixWord, tailWord_7767054, baseEnd_7767054] using wordTrace_append hprefix tailTrace_7767054
  have hstable : (prefixWord ++ tailWord_7767054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767054).length < 2 ^ (prefixWord ++ tailWord_7767054).sum := by decide
  have hdescent : baseEnd_7767054 < baseStart_7767054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767058 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_7767058 : Nat := 118140960795 + 7767058 * 2 ^ 59
def prefixEnd_7767058 : Nat := 4983230072969 + 3 ^ 40 * 7767058 * 2
def baseEnd_7767058 : Nat := 443137113927686398172773

theorem tailTrace_7767058 : CollatzResearch.WordTrace tailWord_7767058 prefixEnd_7767058 443137113927686398172773 := by
  unfold tailWord_7767058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70821969573820712185705457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188858585530188565828547885 70821969573820712185705457)
  ·
    refine ⟨53116477180365534139279093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70821969573820712185705457 53116477180365534139279093)
    ·
      refine ⟨4979669735659268825557415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53116477180365534139279093 4979669735659268825557415)
      ·
        refine ⟨7469504603488903238336123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979669735659268825557415 7469504603488903238336123)
        ·
          refine ⟨11204256905233354857504185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469504603488903238336123 11204256905233354857504185)
          ·
            refine ⟨8403192678925016143128139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11204256905233354857504185 8403192678925016143128139)
            ·
              refine ⟨12604789018387524214692209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403192678925016143128139 12604789018387524214692209)
              ·
                refine ⟨9453591763790643161019157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12604789018387524214692209 9453591763790643161019157)
                ·
                  refine ⟨443137113927686398172773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9453591763790643161019157 443137113927686398172773)
                  ·
                    rfl

theorem cell23_7767058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_7767058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767058 prefixEnd_7767058 := by exact prefixLift 7767058
  have htrace : WordTrace (prefixWord ++ tailWord_7767058) baseStart_7767058 baseEnd_7767058 := by
    simpa [prefixWord, tailWord_7767058, baseEnd_7767058] using wordTrace_append hprefix tailTrace_7767058
  have hstable : (prefixWord ++ tailWord_7767058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767058).length < 2 ^ (prefixWord ++ tailWord_7767058).sum := by decide
  have hdescent : baseEnd_7767058 < baseStart_7767058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767084 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_7767084 : Nat := 118140960795 + 7767084 * 2 ^ 59
def prefixEnd_7767084 : Nat := 4983230072969 + 3 ^ 40 * 7767084 * 2
def baseEnd_7767084 : Nat := 1329415791948731493943279

theorem tailTrace_7767084 : CollatzResearch.WordTrace tailWord_7767084 prefixEnd_7767084 1329415791948731493943279 := by
  unfold tailWord_7767084
  simp only [CollatzResearch.WordTrace]
  refine ⟨141644413296594327591634153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188859217728792436788845537 141644413296594327591634153)
  ·
    refine ⟨106233309972445745693725615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141644413296594327591634153 106233309972445745693725615)
    ·
      refine ⟨159349964958668618540588423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106233309972445745693725615 159349964958668618540588423)
      ·
        refine ⟨239024947438002927810882635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159349964958668618540588423 239024947438002927810882635)
        ·
          refine ⟨358537421157004391716323953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239024947438002927810882635 358537421157004391716323953)
          ·
            refine ⟨268903065867753293787242965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358537421157004391716323953 268903065867753293787242965)
            ·
              refine ⟨6302415606275467823138507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268903065867753293787242965 6302415606275467823138507)
              ·
                refine ⟨9453623409413201734707761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302415606275467823138507 9453623409413201734707761)
                ·
                  refine ⟨7090217557059901301030821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453623409413201734707761 7090217557059901301030821)
                  ·
                    refine ⟨1329415791948731493943279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090217557059901301030821 1329415791948731493943279)
                    ·
                      rfl

theorem cell23_7767084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_7767084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767084 prefixEnd_7767084 := by exact prefixLift 7767084
  have htrace : WordTrace (prefixWord ++ tailWord_7767084) baseStart_7767084 baseEnd_7767084 := by
    simpa [prefixWord, tailWord_7767084, baseEnd_7767084] using wordTrace_append hprefix tailTrace_7767084
  have hstable : (prefixWord ++ tailWord_7767084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767084).length < 2 ^ (prefixWord ++ tailWord_7767084).sum := by decide
  have hdescent : baseEnd_7767084 < baseStart_7767084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767097 : List Nat := [1, 2, 1, 5, 2, 1, 4, 7]
def baseStart_7767097 : Nat := 118140960795 + 7767097 * 2 ^ 59
def prefixEnd_7767097 : Nat := 4983230072969 + 3 ^ 40 * 7767097 * 2
def baseEnd_7767097 : Nat := 147713113003507515961751

theorem tailTrace_7767097 : CollatzResearch.WordTrace tailWord_7767097 prefixEnd_7767097 147713113003507515961751 := by
  unfold tailWord_7767097
  simp only [CollatzResearch.WordTrace]
  refine ⟨283289300742141558403491545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188859533828094372268994363 283289300742141558403491545)
  ·
    refine ⟨212466975556606168802618659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283289300742141558403491545 212466975556606168802618659)
    ·
      refine ⟨318700463334909253203927989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212466975556606168802618659 318700463334909253203927989)
      ·
        refine ⟨29878168437647742487868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318700463334909253203927989 29878168437647742487868249)
        ·
          refine ⟨22408626328235806865901187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29878168437647742487868249 22408626328235806865901187)
          ·
            refine ⟨33612939492353710298851781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22408626328235806865901187 33612939492353710298851781)
            ·
              refine ⟨6302426154816320681034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33612939492353710298851781 6302426154816320681034709)
              ·
                refine ⟨147713113003507515961751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6302426154816320681034709 147713113003507515961751)
                ·
                  rfl

theorem cell23_7767097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 7].length) (baseStart_7767097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767097 prefixEnd_7767097 := by exact prefixLift 7767097
  have htrace : WordTrace (prefixWord ++ tailWord_7767097) baseStart_7767097 baseEnd_7767097 := by
    simpa [prefixWord, tailWord_7767097, baseEnd_7767097] using wordTrace_append hprefix tailTrace_7767097
  have hstable : (prefixWord ++ tailWord_7767097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767097).length < 2 ^ (prefixWord ++ tailWord_7767097).sum := by decide
  have hdescent : baseEnd_7767097 < baseStart_7767097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767107 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 3]
def baseStart_7767107 : Nat := 118140960795 + 7767107 * 2 ^ 59
def prefixEnd_7767107 : Nat := 4983230072969 + 3 ^ 40 * 7767107 * 2
def baseEnd_7767107 : Nat := 3988259185901247891842231

theorem tailTrace_7767107 : CollatzResearch.WordTrace tailWord_7767107 prefixEnd_7767107 3988259185901247891842231 := by
  unfold tailWord_7767107
  simp only [CollatzResearch.WordTrace]
  refine ⟨283289665472105330111355575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188859776981403553407570383 283289665472105330111355575)
  ·
    refine ⟨424934498208157995167033363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283289665472105330111355575 424934498208157995167033363)
    ·
      refine ⟨637401747312236992750550045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424934498208157995167033363 637401747312236992750550045)
      ·
        refine ⟨239025655242088872281456267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637401747312236992750550045 239025655242088872281456267)
        ·
          refine ⟨358538482863133308422184401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239025655242088872281456267 358538482863133308422184401)
          ·
            refine ⟨268903862147349981316638301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358538482863133308422184401 268903862147349981316638301)
            ·
              refine ⟨100838948305256242993739363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268903862147349981316638301 100838948305256242993739363)
              ·
                refine ⟨151258422457884364490609045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100838948305256242993739363 151258422457884364490609045)
                ·
                  refine ⟨7090238552713329585497299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151258422457884364490609045 7090238552713329585497299)
                  ·
                    refine ⟨10635357829069994378245949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090238552713329585497299 10635357829069994378245949)
                    ·
                      refine ⟨3988259185901247891842231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635357829069994378245949 3988259185901247891842231)
                      ·
                        rfl

theorem cell23_7767107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_7767107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767107 prefixEnd_7767107 := by exact prefixLift 7767107
  have htrace : WordTrace (prefixWord ++ tailWord_7767107) baseStart_7767107 baseEnd_7767107 := by
    simpa [prefixWord, tailWord_7767107, baseEnd_7767107] using wordTrace_append hprefix tailTrace_7767107
  have hstable : (prefixWord ++ tailWord_7767107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767107).length < 2 ^ (prefixWord ++ tailWord_7767107).sum := by decide
  have hdescent : baseEnd_7767107 < baseStart_7767107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767124 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_7767124 : Nat := 118140960795 + 7767124 * 2 ^ 59
def prefixEnd_7767124 : Nat := 4983230072969 + 3 ^ 40 * 7767124 * 2
def baseEnd_7767124 : Nat := 3988267915072374325329653

theorem tailTrace_7767124 : CollatzResearch.WordTrace tailWord_7767124 prefixEnd_7767124 3988267915072374325329653 := by
  unfold tailWord_7767124
  simp only [CollatzResearch.WordTrace]
  refine ⟨141645142756521871007362213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188860190342029161343149617 141645142756521871007362213)
  ·
    refine ⟨26558464266847850813880415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141645142756521871007362213 26558464266847850813880415)
    ·
      refine ⟨39837696400271776220820623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558464266847850813880415 39837696400271776220820623)
      ·
        refine ⟨59756544600407664331230935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39837696400271776220820623 59756544600407664331230935)
        ·
          refine ⟨89634816900611496496846403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59756544600407664331230935 89634816900611496496846403)
          ·
            refine ⟨134452225350917244745269605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89634816900611496496846403 134452225350917244745269605)
            ·
              refine ⟨25209792253296983389738051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134452225350917244745269605 25209792253296983389738051)
              ·
                refine ⟨37814688379945475084607077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25209792253296983389738051 37814688379945475084607077)
                ·
                  refine ⟨7090254071239776578363827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37814688379945475084607077 7090254071239776578363827)
                  ·
                    refine ⟨10635381106859664867545741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090254071239776578363827 10635381106859664867545741)
                    ·
                      refine ⟨3988267915072374325329653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635381106859664867545741 3988267915072374325329653)
                      ·
                        rfl

theorem cell23_7767124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_7767124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767124 prefixEnd_7767124 := by exact prefixLift 7767124
  have htrace : WordTrace (prefixWord ++ tailWord_7767124) baseStart_7767124 baseEnd_7767124 := by
    simpa [prefixWord, tailWord_7767124, baseEnd_7767124] using wordTrace_append hprefix tailTrace_7767124
  have hstable : (prefixWord ++ tailWord_7767124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767124).length < 2 ^ (prefixWord ++ tailWord_7767124).sum := by decide
  have hdescent : baseEnd_7767124 < baseStart_7767124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767140 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7767140 : Nat := 118140960795 + 7767140 * 2 ^ 59
def prefixEnd_7767140 : Nat := 4983230072969 + 3 ^ 40 * 7767140 * 2
def baseEnd_7767140 : Nat := 1329425376920948754243193

theorem tailTrace_7767140 : CollatzResearch.WordTrace tailWord_7767140 prefixEnd_7767140 1329425376920948754243193 := by
  unfold tailWord_7767140
  simp only [CollatzResearch.WordTrace]
  refine ⟨141645434540492888373653437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188860579387323851164871249 141645434540492888373653437)
  ·
    refine ⟨53117037952684833140120039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141645434540492888373653437 53117037952684833140120039)
    ·
      refine ⟨79675556929027249710180059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53117037952684833140120039 79675556929027249710180059)
      ·
        refine ⟨119513335393540874565270089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79675556929027249710180059 119513335393540874565270089)
        ·
          refine ⟨89635001545155655923952567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119513335393540874565270089 89635001545155655923952567)
          ·
            refine ⟨134452502317733483885928851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89635001545155655923952567 134452502317733483885928851)
            ·
              refine ⟨201678753476600225828893277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134452502317733483885928851 201678753476600225828893277)
              ·
                refine ⟨75629532553725084685834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201678753476600225828893277 75629532553725084685834979)
                ·
                  refine ⟨113444298830587627028752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75629532553725084685834979 113444298830587627028752469)
                  ·
                    refine ⟨1329425376920948754243193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113444298830587627028752469 1329425376920948754243193)
                    ·
                      rfl

theorem cell23_7767140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7767140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767140 prefixEnd_7767140 := by exact prefixLift 7767140
  have htrace : WordTrace (prefixWord ++ tailWord_7767140) baseStart_7767140 baseEnd_7767140 := by
    simpa [prefixWord, tailWord_7767140, baseEnd_7767140] using wordTrace_append hprefix tailTrace_7767140
  have hstable : (prefixWord ++ tailWord_7767140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767140).length < 2 ^ (prefixWord ++ tailWord_7767140).sum := by decide
  have hdescent : baseEnd_7767140 < baseStart_7767140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767147 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 4, 2]
def baseStart_7767147 : Nat := 118140960795 + 7767147 * 2 ^ 59
def prefixEnd_7767147 : Nat := 4983230072969 + 3 ^ 40 * 7767147 * 2
def baseEnd_7767147 : Nat := 3988279725127427735342047

theorem tailTrace_7767147 : CollatzResearch.WordTrace tailWord_7767147 prefixEnd_7767147 3988279725127427735342047 := by
  unfold tailWord_7767147
  simp only [CollatzResearch.WordTrace]
  refine ⟨283291124391960416942811695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188860749594640277961874463 283291124391960416942811695)
  ·
    refine ⟨424936686587940625414217543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283291124391960416942811695 424936686587940625414217543)
    ·
      refine ⟨637405029881910938121326315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424936686587940625414217543 637405029881910938121326315)
      ·
        refine ⟨956107544822866407181989473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637405029881910938121326315 956107544822866407181989473)
        ·
          refine ⟨717080658617149805386492105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956107544822866407181989473 717080658617149805386492105)
          ·
            refine ⟨537810493962862354039869079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717080658617149805386492105 537810493962862354039869079)
            ·
              refine ⟨806715740944293531059803619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537810493962862354039869079 806715740944293531059803619)
              ·
                refine ⟨1210073611416440296589705429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806715740944293531059803619 1210073611416440296589705429)
                ·
                  refine ⟨28361100267572819451321221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1210073611416440296589705429 28361100267572819451321221)
                  ·
                    refine ⟨5317706300169903647122729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28361100267572819451321221 5317706300169903647122729)
                    ·
                      refine ⟨3988279725127427735342047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317706300169903647122729 3988279725127427735342047)
                      ·
                        rfl

theorem cell23_7767147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4, 2].length) (baseStart_7767147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767147 prefixEnd_7767147 := by exact prefixLift 7767147
  have htrace : WordTrace (prefixWord ++ tailWord_7767147) baseStart_7767147 baseEnd_7767147 := by
    simpa [prefixWord, tailWord_7767147, baseEnd_7767147] using wordTrace_append hprefix tailTrace_7767147
  have hstable : (prefixWord ++ tailWord_7767147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767147).length < 2 ^ (prefixWord ++ tailWord_7767147).sum := by decide
  have hdescent : baseEnd_7767147 < baseStart_7767147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767164 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_7767164 : Nat := 118140960795 + 7767164 * 2 ^ 59
def prefixEnd_7767164 : Nat := 4983230072969 + 3 ^ 40 * 7767164 * 2
def baseEnd_7767164 : Nat := 3988288454298554168829469

theorem tailTrace_7767164 : CollatzResearch.WordTrace tailWord_7767164 prefixEnd_7767164 3988288454298554168829469 := by
  unfold tailWord_7767164
  simp only [CollatzResearch.WordTrace]
  refine ⟨141645872216449414423090273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188861162955265885897453697 141645872216449414423090273)
  ·
    refine ⟨106234404162337060817317705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141645872216449414423090273 106234404162337060817317705)
    ·
      refine ⟨79675803121752795612988279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106234404162337060817317705 79675803121752795612988279)
      ·
        refine ⟨119513704682629193419482419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79675803121752795612988279 119513704682629193419482419)
        ·
          refine ⟨179270557023943790129223629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119513704682629193419482419 179270557023943790129223629)
          ·
            refine ⟨67226458883978921298458861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179270557023943790129223629 67226458883978921298458861)
            ·
              refine ⟨25209922081492095486922073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67226458883978921298458861 25209922081492095486922073)
              ·
                refine ⟨18907441561119071615191555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25209922081492095486922073 18907441561119071615191555)
                ·
                  refine ⟨28361162341678607422787333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18907441561119071615191555 28361162341678607422787333)
                  ·
                    refine ⟨5317717939064738891772625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28361162341678607422787333 5317717939064738891772625)
                    ·
                      refine ⟨3988288454298554168829469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317717939064738891772625 3988288454298554168829469)
                      ·
                        rfl

theorem cell23_7767164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_7767164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767164 prefixEnd_7767164 := by exact prefixLift 7767164
  have htrace : WordTrace (prefixWord ++ tailWord_7767164) baseStart_7767164 baseEnd_7767164 := by
    simpa [prefixWord, tailWord_7767164, baseEnd_7767164] using wordTrace_append hprefix tailTrace_7767164
  have hstable : (prefixWord ++ tailWord_7767164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767164).length < 2 ^ (prefixWord ++ tailWord_7767164).sum := by decide
  have hdescent : baseEnd_7767164 < baseStart_7767164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767180 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7767180 : Nat := 118140960795 + 7767180 * 2 ^ 59
def prefixEnd_7767180 : Nat := 4983230072969 + 3 ^ 40 * 7767180 * 2
def baseEnd_7767180 : Nat := 3988296669989026106229395

theorem tailTrace_7767180 : CollatzResearch.WordTrace tailWord_7767180 prefixEnd_7767180 3988296669989026106229395 := by
  unfold tailWord_7767180
  simp only [CollatzResearch.WordTrace]
  refine ⟨141646164000420431789381497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188861552000560575719175329 141646164000420431789381497)
  ·
    refine ⟨106234623000315323842036123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141646164000420431789381497 106234623000315323842036123)
    ·
      refine ⟨159351934500472985763054185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106234623000315323842036123 159351934500472985763054185)
      ·
        refine ⟨119513950875354739322290639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159351934500472985763054185 119513950875354739322290639)
        ·
          refine ⟨179270926313032108983435959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119513950875354739322290639 179270926313032108983435959)
          ·
            refine ⟨268906389469548163475153939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179270926313032108983435959 268906389469548163475153939)
            ·
              refine ⟨403359584204322245212730909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268906389469548163475153939 403359584204322245212730909)
              ·
                refine ⟨151259844076620841954774091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403359584204322245212730909 151259844076620841954774091)
                ·
                  refine ⟨226889766114931262932161137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151259844076620841954774091 226889766114931262932161137)
                  ·
                    refine ⟨170167324586198447199120853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226889766114931262932161137 170167324586198447199120853)
                    ·
                      refine ⟨3988296669989026106229395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170167324586198447199120853 3988296669989026106229395)
                      ·
                        rfl

theorem cell23_7767180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7767180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767180 prefixEnd_7767180 := by exact prefixLift 7767180
  have htrace : WordTrace (prefixWord ++ tailWord_7767180) baseStart_7767180 baseEnd_7767180 := by
    simpa [prefixWord, tailWord_7767180, baseEnd_7767180] using wordTrace_append hprefix tailTrace_7767180
  have hstable : (prefixWord ++ tailWord_7767180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767180).length < 2 ^ (prefixWord ++ tailWord_7767180).sum := by decide
  have hdescent : baseEnd_7767180 < baseStart_7767180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767194 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7767194 : Nat := 118140960795 + 7767194 * 2 ^ 59
def prefixEnd_7767194 : Nat := 4983230072969 + 3 ^ 40 * 7767194 * 2
def baseEnd_7767194 : Nat := 3988303858718189051454331

theorem tailTrace_7767194 : CollatzResearch.WordTrace tailWord_7767194 prefixEnd_7767194 3988303858718189051454331 := by
  unfold tailWord_7767194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823209655697535992443159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188861892415193429313181757 70823209655697535992443159)
  ·
    refine ⟨106234814483546303988664739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70823209655697535992443159 106234814483546303988664739)
    ·
      refine ⟨159352221725319455982997109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106234814483546303988664739 159352221725319455982997109)
      ·
        refine ⟨14939270786748698998405979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159352221725319455982997109 14939270786748698998405979)
        ·
          refine ⟨22408906180123048497608969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939270786748698998405979 22408906180123048497608969)
          ·
            refine ⟨16806679635092286373206727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408906180123048497608969 16806679635092286373206727)
            ·
              refine ⟨25210019452638429559810091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16806679635092286373206727 25210019452638429559810091)
              ·
                refine ⟨37815029178957644339715137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210019452638429559810091 37815029178957644339715137)
                ·
                  refine ⟨28361271884218233254786353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37815029178957644339715137 28361271884218233254786353)
                  ·
                    refine ⟨21270953913163674941089765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28361271884218233254786353 21270953913163674941089765)
                    ·
                      refine ⟨3988303858718189051454331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21270953913163674941089765 3988303858718189051454331)
                      ·
                        rfl

theorem cell23_7767194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7767194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767194 prefixEnd_7767194 := by exact prefixLift 7767194
  have htrace : WordTrace (prefixWord ++ tailWord_7767194) baseStart_7767194 baseEnd_7767194 := by
    simpa [prefixWord, tailWord_7767194, baseEnd_7767194] using wordTrace_append hprefix tailTrace_7767194
  have hstable : (prefixWord ++ tailWord_7767194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767194).length < 2 ^ (prefixWord ++ tailWord_7767194).sum := by decide
  have hdescent : baseEnd_7767194 < baseStart_7767194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767198 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7767198 : Nat := 118140960795 + 7767198 * 2 ^ 59
def prefixEnd_7767198 : Nat := 4983230072969 + 3 ^ 40 * 7767198 * 2
def baseEnd_7767198 : Nat := 3988305912640807035804313

theorem tailTrace_7767198 : CollatzResearch.WordTrace tailWord_7767198 prefixEnd_7767198 3988305912640807035804313 := by
  unfold tailWord_7767198
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411623064346956581614781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188861989676517101768612165 35411623064346956581614781)
  ·
    refine ⟨13279358649130108718105543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35411623064346956581614781 13279358649130108718105543)
    ·
      refine ⟨19919037973695163077158315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279358649130108718105543 19919037973695163077158315)
      ·
        refine ⟨29878556960542744615737473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919037973695163077158315 29878556960542744615737473)
        ·
          refine ⟨22408917720407058461803105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29878556960542744615737473 22408917720407058461803105)
          ·
            refine ⟨16806688290305293846352329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408917720407058461803105 16806688290305293846352329)
            ·
              refine ⟨12605016217728970384764247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806688290305293846352329 12605016217728970384764247)
              ·
                refine ⟨18907524326593455577146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605016217728970384764247 18907524326593455577146371)
                ·
                  refine ⟨28361286489890183365719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18907524326593455577146371 28361286489890183365719557)
                  ·
                    refine ⟨5317741216854409381072417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28361286489890183365719557 5317741216854409381072417)
                    ·
                      refine ⟨3988305912640807035804313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317741216854409381072417 3988305912640807035804313)
                      ·
                        rfl

theorem cell23_7767198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7767198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767198 prefixEnd_7767198 := by exact prefixLift 7767198
  have htrace : WordTrace (prefixWord ++ tailWord_7767198) baseStart_7767198 baseEnd_7767198 := by
    simpa [prefixWord, tailWord_7767198, baseEnd_7767198] using wordTrace_append hprefix tailTrace_7767198
  have hstable : (prefixWord ++ tailWord_7767198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767198).length < 2 ^ (prefixWord ++ tailWord_7767198).sum := by decide
  have hdescent : baseEnd_7767198 < baseStart_7767198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767237 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_7767237 : Nat := 118140960795 + 7767237 * 2 ^ 59
def prefixEnd_7767237 : Nat := 4983230072969 + 3 ^ 40 * 7767237 * 2
def baseEnd_7767237 : Nat := 3988325938386332383216633

theorem tailTrace_7767237 : CollatzResearch.WordTrace tailWord_7767237 prefixEnd_7767237 3988325938386332383216633 := by
  unfold tailWord_7767237
  simp only [CollatzResearch.WordTrace]
  refine ⟨283294406961634362313587965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188862937974422908209058643 283294406961634362313587965)
  ·
    refine ⟨106235402610612885867595487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283294406961634362313587965 106235402610612885867595487)
    ·
      refine ⟨159353103915919328801393231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106235402610612885867595487 159353103915919328801393231)
      ·
        refine ⟨239029655873878993202089847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159353103915919328801393231 239029655873878993202089847)
        ·
          refine ⟨358544483810818489803134771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239029655873878993202089847 358544483810818489803134771)
          ·
            refine ⟨537816725716227734704702157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358544483810818489803134771 537816725716227734704702157)
            ·
              refine ⟨201681272143585400514263309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537816725716227734704702157 201681272143585400514263309)
              ·
                refine ⟨75630477053844525192848741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201681272143585400514263309 75630477053844525192848741)
                ·
                  refine ⟨14180714447595848473659139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75630477053844525192848741 14180714447595848473659139)
                  ·
                    refine ⟨21271071671393772710488709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14180714447595848473659139 21271071671393772710488709)
                    ·
                      refine ⟨3988325938386332383216633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21271071671393772710488709 3988325938386332383216633)
                      ·
                        rfl

theorem cell23_7767237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_7767237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767237 prefixEnd_7767237 := by exact prefixLift 7767237
  have htrace : WordTrace (prefixWord ++ tailWord_7767237) baseStart_7767237 baseEnd_7767237 := by
    simpa [prefixWord, tailWord_7767237, baseEnd_7767237] using wordTrace_append hprefix tailTrace_7767237
  have hstable : (prefixWord ++ tailWord_7767237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767237).length < 2 ^ (prefixWord ++ tailWord_7767237).sum := by decide
  have hdescent : baseEnd_7767237 < baseStart_7767237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767264 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_7767264 : Nat := 118140960795 + 7767264 * 2 ^ 59
def prefixEnd_7767264 : Nat := 4983230072969 + 3 ^ 40 * 7767264 * 2
def baseEnd_7767264 : Nat := 1329446600788001259193003

theorem tailTrace_7767264 : CollatzResearch.WordTrace tailWord_7767264 prefixEnd_7767264 1329446600788001259193003 := by
  unfold tailWord_7767264
  simp only [CollatzResearch.WordTrace]
  refine ⟨141647695866268272962410423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188863594488357697283213897 141647695866268272962410423)
  ·
    refine ⟨212471543799402409443615635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141647695866268272962410423 212471543799402409443615635)
    ·
      refine ⟨318707315699103614165423453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212471543799402409443615635 318707315699103614165423453)
      ·
        refine ⟨119515243387163855312033795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318707315699103614165423453 119515243387163855312033795)
        ·
          refine ⟨179272865080745782968050693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119515243387163855312033795 179272865080745782968050693)
          ·
            refine ⟨33613662202639834306509505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179272865080745782968050693 33613662202639834306509505)
            ·
              refine ⟨25210246651979875729882129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33613662202639834306509505 25210246651979875729882129)
              ·
                refine ⟨18907684988984906797411597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25210246651979875729882129 18907684988984906797411597)
                ·
                  refine ⟨7090381870869340049029349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18907684988984906797411597 7090381870869340049029349)
                  ·
                    refine ⟨1329446600788001259193003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090381870869340049029349 1329446600788001259193003)
                    ·
                      rfl

theorem cell23_7767264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_7767264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767264 prefixEnd_7767264 := by exact prefixLift 7767264
  have htrace : WordTrace (prefixWord ++ tailWord_7767264) baseStart_7767264 baseEnd_7767264 := by
    simpa [prefixWord, tailWord_7767264, baseEnd_7767264] using wordTrace_append hprefix tailTrace_7767264
  have hstable : (prefixWord ++ tailWord_7767264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767264).length < 2 ^ (prefixWord ++ tailWord_7767264).sum := by decide
  have hdescent : baseEnd_7767264 < baseStart_7767264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767274 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_7767274 : Nat := 118140960795 + 7767274 * 2 ^ 59
def prefixEnd_7767274 : Nat := 4983230072969 + 3 ^ 40 * 7767274 * 2
def baseEnd_7767274 : Nat := 3988344937170548738453963

theorem tailTrace_7767274 : CollatzResearch.WordTrace tailWord_7767274 prefixEnd_7767274 3988344937170548738453963 := by
  unfold tailWord_7767274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70823939115625079408171219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188863837641666878421789917 70823939115625079408171219)
  ·
    refine ⟨106235908673437619112256829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70823939115625079408171219 106235908673437619112256829)
    ·
      refine ⟨39838465752539107167096311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106235908673437619112256829 39838465752539107167096311)
      ·
        refine ⟨59757698628808660750644467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39838465752539107167096311 59757698628808660750644467)
        ·
          refine ⟨89636547943212991125966701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59757698628808660750644467 89636547943212991125966701)
          ·
            refine ⟨33613705478704871672237513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89636547943212991125966701 33613705478704871672237513)
            ·
              refine ⟨25210279109028653754178135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33613705478704871672237513 25210279109028653754178135)
              ·
                refine ⟨37815418663542980631267203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210279109028653754178135 37815418663542980631267203)
                ·
                  refine ⟨56723127995314470946900805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37815418663542980631267203 56723127995314470946900805)
                  ·
                    refine ⟨10635586499121463302543901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56723127995314470946900805 10635586499121463302543901)
                    ·
                      refine ⟨3988344937170548738453963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635586499121463302543901 3988344937170548738453963)
                      ·
                        rfl

theorem cell23_7767274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_7767274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767274 prefixEnd_7767274 := by exact prefixLift 7767274
  have htrace : WordTrace (prefixWord ++ tailWord_7767274) baseStart_7767274 baseEnd_7767274 := by
    simpa [prefixWord, tailWord_7767274, baseEnd_7767274] using wordTrace_append hprefix tailTrace_7767274
  have hstable : (prefixWord ++ tailWord_7767274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767274).length < 2 ^ (prefixWord ++ tailWord_7767274).sum := by decide
  have hdescent : baseEnd_7767274 < baseStart_7767274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767287 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_7767287 : Nat := 118140960795 + 7767287 * 2 ^ 59
def prefixEnd_7767287 : Nat := 4983230072969 + 3 ^ 40 * 7767287 * 2
def baseEnd_7767287 : Nat := 3988351612419057187591403

theorem tailTrace_7767287 : CollatzResearch.WordTrace tailWord_7767287 prefixEnd_7767287 3988351612419057187591403 := by
  unfold tailWord_7767287
  simp only [CollatzResearch.WordTrace]
  refine ⟨283296230611453220852908115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188864153740968813901938743 283296230611453220852908115)
  ·
    refine ⟨424944345917179831279362173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283296230611453220852908115 424944345917179831279362173)
    ·
      refine ⟨159354129718942436729760815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424944345917179831279362173 159354129718942436729760815)
      ·
        refine ⟨239031194578413655094641223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159354129718942436729760815 239031194578413655094641223)
        ·
          refine ⟨358546791867620482641961835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239031194578413655094641223 358546791867620482641961835)
          ·
            refine ⟨537820187801430723962942753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358546791867620482641961835 537820187801430723962942753)
            ·
              refine ⟨403365140851073042972207065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537820187801430723962942753 403365140851073042972207065)
              ·
                refine ⟨302523855638304782229155299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403365140851073042972207065 302523855638304782229155299)
                ·
                  refine ⟨453785783457457173343732949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302523855638304782229155299 453785783457457173343732949)
                  ·
                    refine ⟨10635604299784152500243741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 453785783457457173343732949 10635604299784152500243741)
                    ·
                      refine ⟨3988351612419057187591403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635604299784152500243741 3988351612419057187591403)
                      ·
                        rfl

theorem cell23_7767287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_7767287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767287 prefixEnd_7767287 := by exact prefixLift 7767287
  have htrace : WordTrace (prefixWord ++ tailWord_7767287) baseStart_7767287 baseEnd_7767287 := by
    simpa [prefixWord, tailWord_7767287, baseEnd_7767287] using wordTrace_append hprefix tailTrace_7767287
  have hstable : (prefixWord ++ tailWord_7767287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767287).length < 2 ^ (prefixWord ++ tailWord_7767287).sum := by decide
  have hdescent : baseEnd_7767287 < baseStart_7767287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767294 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_7767294 : Nat := 118140960795 + 7767294 * 2 ^ 59
def prefixEnd_7767294 : Nat := 4983230072969 + 3 ^ 40 * 7767294 * 2
def baseEnd_7767294 : Nat := 443150578531515406689319

theorem tailTrace_7767294 : CollatzResearch.WordTrace tailWord_7767294 prefixEnd_7767294 443150578531515406689319 := by
  unfold tailWord_7767294
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412060740303482631051617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188864323948285240698941957 35412060740303482631051617)
  ·
    refine ⟨26559045555227611973288713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35412060740303482631051617 26559045555227611973288713)
    ·
      refine ⟨19919284166420708979966535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26559045555227611973288713 19919284166420708979966535)
      ·
        refine ⟨29878926249631063469949803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919284166420708979966535 29878926249631063469949803)
        ·
          refine ⟨44818389374446595204924705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29878926249631063469949803 44818389374446595204924705)
          ·
            refine ⟨33613792030834946403693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44818389374446595204924705 33613792030834946403693529)
            ·
              refine ⟨25210344023126209802770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33613792030834946403693529 25210344023126209802770147)
              ·
                refine ⟨37815516034689314704155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210344023126209802770147 37815516034689314704155221)
                ·
                  refine ⟨443150578531515406689319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37815516034689314704155221 443150578531515406689319)
                  ·
                    rfl

theorem cell23_7767294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_7767294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767294 prefixEnd_7767294 := by exact prefixLift 7767294
  have htrace : WordTrace (prefixWord ++ tailWord_7767294) baseStart_7767294 baseEnd_7767294 := by
    simpa [prefixWord, tailWord_7767294, baseEnd_7767294] using wordTrace_append hprefix tailTrace_7767294
  have hstable : (prefixWord ++ tailWord_7767294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767294).length < 2 ^ (prefixWord ++ tailWord_7767294).sum := by decide
  have hdescent : baseEnd_7767294 < baseStart_7767294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767331 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 2, 3, 2]
def baseStart_7767331 : Nat := 118140960795 + 7767331 * 2 ^ 59
def prefixEnd_7767331 : Nat := 4983230072969 + 3 ^ 40 * 7767331 * 2
def baseEnd_7767331 : Nat := 3988374205567855015441201

theorem tailTrace_7767331 : CollatzResearch.WordTrace tailWord_7767331 prefixEnd_7767331 3988374205567855015441201 := by
  unfold tailWord_7767331
  simp only [CollatzResearch.WordTrace]
  refine ⟨283297835423293816367509847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188865223615529210911673231 283297835423293816367509847)
  ·
    refine ⟨424946753134940724551264771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283297835423293816367509847 424946753134940724551264771)
    ·
      refine ⟨637420129702411086826897157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424946753134940724551264771 637420129702411086826897157)
      ·
        refine ⟨119516274319202078780043217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637420129702411086826897157 119516274319202078780043217)
        ·
          refine ⟨89637205739401559085032413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119516274319202078780043217 89637205739401559085032413)
          ·
            refine ⟨33613952152275584656887155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89637205739401559085032413 33613952152275584656887155)
            ·
              refine ⟨50420928228413376985330733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33613952152275584656887155 50420928228413376985330733)
              ·
                refine ⟨18907848085655016369499025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50420928228413376985330733 18907848085655016369499025)
                ·
                  refine ⟨14180886064241262277124269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18907848085655016369499025 14180886064241262277124269)
                  ·
                    refine ⟨5317832274090473353921601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14180886064241262277124269 5317832274090473353921601)
                    ·
                      refine ⟨3988374205567855015441201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317832274090473353921601 3988374205567855015441201)
                      ·
                        rfl

theorem cell23_7767331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_7767331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767331 prefixEnd_7767331 := by exact prefixLift 7767331
  have htrace : WordTrace (prefixWord ++ tailWord_7767331) baseStart_7767331 baseEnd_7767331 := by
    simpa [prefixWord, tailWord_7767331, baseEnd_7767331] using wordTrace_append hprefix tailTrace_7767331
  have hstable : (prefixWord ++ tailWord_7767331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767331).length < 2 ^ (prefixWord ++ tailWord_7767331).sum := by decide
  have hdescent : baseEnd_7767331 < baseStart_7767331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767348 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_7767348 : Nat := 118140960795 + 7767348 * 2 ^ 59
def prefixEnd_7767348 : Nat := 4983230072969 + 3 ^ 40 * 7767348 * 2
def baseEnd_7767348 : Nat := 3988382934738981448928623

theorem tailTrace_7767348 : CollatzResearch.WordTrace tailWord_7767348 prefixEnd_7767348 3988382934738981448928623 := by
  unfold tailWord_7767348
  simp only [CollatzResearch.WordTrace]
  refine ⟨141649227732116114135439349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188865636976154818847252465 141649227732116114135439349)
  ·
    refine ⟨13279615099885885700197439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141649227732116114135439349 13279615099885885700197439)
    ·
      refine ⟨19919422649828828550296159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279615099885885700197439 19919422649828828550296159)
      ·
        refine ⟨29879133974743242825444239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919422649828828550296159 29879133974743242825444239)
        ·
          refine ⟨44818700962114864238166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29879133974743242825444239 44818700962114864238166359)
          ·
            refine ⟨67228051443172296357249539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44818700962114864238166359 67228051443172296357249539)
            ·
              refine ⟨100842077164758444535874309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67228051443172296357249539 100842077164758444535874309)
              ·
                refine ⟨18907889468392208350476433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100842077164758444535874309 18907889468392208350476433)
                ·
                  refine ⟨14180917101294156262857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18907889468392208350476433 14180917101294156262857325)
                  ·
                    refine ⟨5317843912985308598571497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14180917101294156262857325 5317843912985308598571497)
                    ·
                      refine ⟨3988382934738981448928623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317843912985308598571497 3988382934738981448928623)
                      ·
                        rfl

theorem cell23_7767348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_7767348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767348 prefixEnd_7767348 := by exact prefixLift 7767348
  have htrace : WordTrace (prefixWord ++ tailWord_7767348) baseStart_7767348 baseEnd_7767348 := by
    simpa [prefixWord, tailWord_7767348, baseEnd_7767348] using wordTrace_append hprefix tailTrace_7767348
  have hstable : (prefixWord ++ tailWord_7767348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767348).length < 2 ^ (prefixWord ++ tailWord_7767348).sum := by decide
  have hdescent : baseEnd_7767348 < baseStart_7767348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767361 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7767361 : Nat := 118140960795 + 7767361 * 2 ^ 59
def prefixEnd_7767361 : Nat := 4983230072969 + 3 ^ 40 * 7767361 * 2
def baseEnd_7767361 : Nat := 3988389609987489898066063

theorem tailTrace_7767361 : CollatzResearch.WordTrace tailWord_7767361 prefixEnd_7767361 3988389609987489898066063 := by
  unfold tailWord_7767361
  simp only [CollatzResearch.WordTrace]
  refine ⟨283298929613185131491101937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188865953075456754327401291 283298929613185131491101937)
  ·
    refine ⟨212474197209888848618326453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283298929613185131491101937 212474197209888848618326453)
    ·
      refine ⟨19919455988427079557968105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212474197209888848618326453 19919455988427079557968105)
      ·
        refine ⟨14939591991320309668476079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19919455988427079557968105 14939591991320309668476079)
        ·
          refine ⟨22409387986980464502714119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939591991320309668476079 22409387986980464502714119)
          ·
            refine ⟨33614081980470696754071179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22409387986980464502714119 33614081980470696754071179)
            ·
              refine ⟨50421122970706045131106769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33614081980470696754071179 50421122970706045131106769)
              ·
                refine ⟨37815842228029533848330077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50421122970706045131106769 37815842228029533848330077)
                ·
                  refine ⟨14180940835511075193123779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37815842228029533848330077 14180940835511075193123779)
                  ·
                    refine ⟨21271411253266612789685669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14180940835511075193123779 21271411253266612789685669)
                    ·
                      refine ⟨3988389609987489898066063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21271411253266612789685669 3988389609987489898066063)
                      ·
                        rfl

theorem cell23_7767361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7767361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767361 prefixEnd_7767361 := by exact prefixLift 7767361
  have htrace : WordTrace (prefixWord ++ tailWord_7767361) baseStart_7767361 baseEnd_7767361 := by
    simpa [prefixWord, tailWord_7767361, baseEnd_7767361] using wordTrace_append hprefix tailTrace_7767361
  have hstable : (prefixWord ++ tailWord_7767361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767361).length < 2 ^ (prefixWord ++ tailWord_7767361).sum := by decide
  have hdescent : baseEnd_7767361 < baseStart_7767361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767381 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7767381 : Nat := 118140960795 + 7767381 * 2 ^ 59
def prefixEnd_7767381 : Nat := 4983230072969 + 3 ^ 40 * 7767381 * 2
def baseEnd_7767381 : Nat := 3988399879600579819815971

theorem tailTrace_7767381 : CollatzResearch.WordTrace tailWord_7767381 prefixEnd_7767381 3988399879600579819815971 := by
  unfold tailWord_7767381
  simp only [CollatzResearch.WordTrace]
  refine ⟨283299659073112674906829997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188866439382075116604553331 283299659073112674906829997)
  ·
    refine ⟨106237372152417253090061249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283299659073112674906829997 106237372152417253090061249)
    ·
      refine ⟨79678029114312939817545937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106237372152417253090061249 79678029114312939817545937)
      ·
        refine ⟨59758521835734704863159453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79678029114312939817545937 59758521835734704863159453)
        ·
          refine ⟨22409445688400514323684795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59758521835734704863159453 22409445688400514323684795)
          ·
            refine ⟨33614168532600771485527193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22409445688400514323684795 33614168532600771485527193)
            ·
              refine ⟨25210626399450578614145395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33614168532600771485527193 25210626399450578614145395)
              ·
                refine ⟨37815939599175867921218093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210626399450578614145395 37815939599175867921218093)
                ·
                  refine ⟨14180977349690950470456785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37815939599175867921218093 14180977349690950470456785)
                  ·
                    refine ⟨10635733012268212852842589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14180977349690950470456785 10635733012268212852842589)
                    ·
                      refine ⟨3988399879600579819815971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635733012268212852842589 3988399879600579819815971)
                      ·
                        rfl

theorem cell23_7767381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7767381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767381 prefixEnd_7767381 := by exact prefixLift 7767381
  have htrace : WordTrace (prefixWord ++ tailWord_7767381) baseStart_7767381 baseEnd_7767381 := by
    simpa [prefixWord, tailWord_7767381, baseEnd_7767381] using wordTrace_append hprefix tailTrace_7767381
  have hstable : (prefixWord ++ tailWord_7767381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767381).length < 2 ^ (prefixWord ++ tailWord_7767381).sum := by decide
  have hdescent : baseEnd_7767381 < baseStart_7767381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767384 : List Nat := [2, 1, 2, 2, 1, 1, 7, 7]
def baseStart_7767384 : Nat := 118140960795 + 7767384 * 2 ^ 59
def prefixEnd_7767384 : Nat := 4983230072969 + 3 ^ 40 * 7767384 * 2
def baseEnd_7767384 : Nat := 147718571112686789188091

theorem tailTrace_7767384 : CollatzResearch.WordTrace tailWord_7767384 prefixEnd_7767384 147718571112686789188091 := by
  unfold tailWord_7767384
  simp only [CollatzResearch.WordTrace]
  refine ⟨141649884246050903209594603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188866512328067870946126137 141649884246050903209594603)
  ·
    refine ⟨212474826369076354814391905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141649884246050903209594603 212474826369076354814391905)
    ·
      refine ⟨159356119776807266110793929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212474826369076354814391905 159356119776807266110793929)
      ·
        refine ⟨119517089832605449583095447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159356119776807266110793929 119517089832605449583095447)
        ·
          refine ⟨179275634748908174374643171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119517089832605449583095447 179275634748908174374643171)
          ·
            refine ⟨268913452123362261561964757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179275634748908174374643171 268913452123362261561964757)
            ·
              refine ⟨6302659034141303005358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268913452123362261561964757 6302659034141303005358549)
              ·
                refine ⟨147718571112686789188091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6302659034141303005358549 147718571112686789188091)
                ·
                  rfl

theorem cell23_7767384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 7].length) (baseStart_7767384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767384 prefixEnd_7767384 := by exact prefixLift 7767384
  have htrace : WordTrace (prefixWord ++ tailWord_7767384) baseStart_7767384 baseEnd_7767384 := by
    simpa [prefixWord, tailWord_7767384, baseEnd_7767384] using wordTrace_append hprefix tailTrace_7767384
  have hstable : (prefixWord ++ tailWord_7767384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767384).length < 2 ^ (prefixWord ++ tailWord_7767384).sum := by decide
  have hdescent : baseEnd_7767384 < baseStart_7767384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767395 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7767395 : Nat := 118140960795 + 7767395 * 2 ^ 59
def prefixEnd_7767395 : Nat := 4983230072969 + 3 ^ 40 * 7767395 * 2
def baseEnd_7767395 : Nat := 3988407068329742765040907

theorem tailTrace_7767395 : CollatzResearch.WordTrace tailWord_7767395 prefixEnd_7767395 3988407068329742765040907 := by
  unfold tailWord_7767395
  simp only [CollatzResearch.WordTrace]
  refine ⟨283300169695061955297839639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188866779796707970198559759 283300169695061955297839639)
  ·
    refine ⟨424950254542592932946759459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283300169695061955297839639 424950254542592932946759459)
    ·
      refine ⟨637425381813889399420139189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424950254542592932946759459 637425381813889399420139189)
      ·
        refine ⟨59758629545052131195638049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 637425381813889399420139189 59758629545052131195638049)
        ·
          refine ⟨44818972158789098396728537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59758629545052131195638049 44818972158789098396728537)
          ·
            refine ⟨33614229119091823797546403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44818972158789098396728537 33614229119091823797546403)
            ·
              refine ⟨50421343678637735696319605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33614229119091823797546403 50421343678637735696319605)
              ·
                refine ⟨4727000969872287721529963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50421343678637735696319605 4727000969872287721529963)
                ·
                  refine ⟨7090501454808431582294945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727000969872287721529963 7090501454808431582294945)
                  ·
                    refine ⟨5317876091106323686721209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7090501454808431582294945 5317876091106323686721209)
                    ·
                      refine ⟨3988407068329742765040907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317876091106323686721209 3988407068329742765040907)
                      ·
                        rfl

theorem cell23_7767395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7767395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767395 prefixEnd_7767395 := by exact prefixLift 7767395
  have htrace : WordTrace (prefixWord ++ tailWord_7767395) baseStart_7767395 baseEnd_7767395 := by
    simpa [prefixWord, tailWord_7767395, baseEnd_7767395] using wordTrace_append hprefix tailTrace_7767395
  have hstable : (prefixWord ++ tailWord_7767395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767395).length < 2 ^ (prefixWord ++ tailWord_7767395).sum := by decide
  have hdescent : baseEnd_7767395 < baseStart_7767395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767422 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7767422 : Nat := 118140960795 + 7767422 * 2 ^ 59
def prefixEnd_7767422 : Nat := 4983230072969 + 3 ^ 40 * 7767422 * 2
def baseEnd_7767422 : Nat := 1329473644102471386467761

theorem tailTrace_7767422 : CollatzResearch.WordTrace tailWord_7767422 prefixEnd_7767422 1329473644102471386467761 := by
  unfold tailWord_7767422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412644308245517363634065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188867436310642759272715013 35412644308245517363634065)
  ·
    refine ⟨26559483231184138022725549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35412644308245517363634065 26559483231184138022725549)
    ·
      refine ⟨9959806211694051758522081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26559483231184138022725549 9959806211694051758522081)
      ·
        refine ⟨7469854658770538818891561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959806211694051758522081 7469854658770538818891561)
        ·
          refine ⟨5602390994077904114168671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469854658770538818891561 5602390994077904114168671)
          ·
            refine ⟨8403586491116856171253007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602390994077904114168671 8403586491116856171253007)
            ·
              refine ⟨12605379736675284256879511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403586491116856171253007 12605379736675284256879511)
              ·
                refine ⟨18908069605012926385319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605379736675284256879511 18908069605012926385319267)
                ·
                  refine ⟨28362104407519389577978901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18908069605012926385319267 28362104407519389577978901)
                  ·
                    refine ⟨1329473644102471386467761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28362104407519389577978901 1329473644102471386467761)
                    ·
                      rfl

theorem cell23_7767422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7767422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767422 prefixEnd_7767422 := by exact prefixLift 7767422
  have htrace : WordTrace (prefixWord ++ tailWord_7767422) baseStart_7767422 baseEnd_7767422 := by
    simpa [prefixWord, tailWord_7767422, baseEnd_7767422] using wordTrace_append hprefix tailTrace_7767422
  have hstable : (prefixWord ++ tailWord_7767422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767422).length < 2 ^ (prefixWord ++ tailWord_7767422).sum := by decide
  have hdescent : baseEnd_7767422 < baseStart_7767422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767425 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7767425 : Nat := 118140960795 + 7767425 * 2 ^ 59
def prefixEnd_7767425 : Nat := 4983230072969 + 3 ^ 40 * 7767425 * 2
def baseEnd_7767425 : Nat := 3988422472749377647665769

theorem tailTrace_7767425 : CollatzResearch.WordTrace tailWord_7767425 prefixEnd_7767425 3988422472749377647665769 := by
  unfold tailWord_7767425
  simp only [CollatzResearch.WordTrace]
  refine ⟨283301263884953270421431729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188867509256635513614287819 283301263884953270421431729)
  ·
    refine ⟨212475947913714952816073797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283301263884953270421431729 212475947913714952816073797)
    ·
      refine ⟨39839240233821553653013837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212475947913714952816073797 39839240233821553653013837)
      ·
        refine ⟨14939715087683082619880189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39839240233821553653013837 14939715087683082619880189)
        ·
          refine ⟨5602393157881155982455071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14939715087683082619880189 5602393157881155982455071)
          ·
            refine ⟨8403589736821733973682607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602393157881155982455071 8403589736821733973682607)
            ·
              refine ⟨12605384605232600960523911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403589736821733973682607 12605384605232600960523911)
              ·
                refine ⟨18908076907848901440785867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605384605232600960523911 18908076907848901440785867)
                ·
                  refine ⟨28362115361773352161178801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18908076907848901440785867 28362115361773352161178801)
                  ·
                    refine ⟨21271586521330014120884101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28362115361773352161178801 21271586521330014120884101)
                    ·
                      refine ⟨3988422472749377647665769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21271586521330014120884101 3988422472749377647665769)
                      ·
                        rfl

theorem cell23_7767425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7767425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767425 prefixEnd_7767425 := by exact prefixLift 7767425
  have htrace : WordTrace (prefixWord ++ tailWord_7767425) baseStart_7767425 baseEnd_7767425 := by
    simpa [prefixWord, tailWord_7767425, baseEnd_7767425] using wordTrace_append hprefix tailTrace_7767425
  have hstable : (prefixWord ++ tailWord_7767425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767425).length < 2 ^ (prefixWord ++ tailWord_7767425).sum := by decide
  have hdescent : baseEnd_7767425 < baseStart_7767425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767428 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7767428 : Nat := 118140960795 + 7767428 * 2 ^ 59
def prefixEnd_7767428 : Nat := 4983230072969 + 3 ^ 40 * 7767428 * 2
def baseEnd_7767428 : Nat := 3988424013191341135928255

theorem tailTrace_7767428 : CollatzResearch.WordTrace tailWord_7767428 prefixEnd_7767428 3988424013191341135928255 := by
  unfold tailWord_7767428
  simp only [CollatzResearch.WordTrace]
  refine ⟨141650686651971200966895469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188867582202628267955860625 141650686651971200966895469)
  ·
    refine ⟨53119007494489200362585801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141650686651971200966895469 53119007494489200362585801)
    ·
      refine ⟨39839255620866900271939351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53119007494489200362585801 39839255620866900271939351)
      ·
        refine ⟨59758883431300350407909027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39839255620866900271939351 59758883431300350407909027)
        ·
          refine ⟨89638325146950525611863541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59758883431300350407909027 89638325146950525611863541)
          ·
            refine ⟨8403592982526611776112207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89638325146950525611863541 8403592982526611776112207)
            ·
              refine ⟨12605389473789917664168311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403592982526611776112207 12605389473789917664168311)
              ·
                refine ⟨18908084210684876496252467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605389473789917664168311 18908084210684876496252467)
                ·
                  refine ⟨28362126316027314744378701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18908084210684876496252467 28362126316027314744378701)
                  ·
                    refine ⟨10635797368510243029142013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28362126316027314744378701 10635797368510243029142013)
                    ·
                      refine ⟨3988424013191341135928255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635797368510243029142013 3988424013191341135928255)
                      ·
                        rfl

theorem cell23_7767428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7767428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767428 prefixEnd_7767428 := by exact prefixLift 7767428
  have htrace : WordTrace (prefixWord ++ tailWord_7767428) baseStart_7767428 baseEnd_7767428 := by
    simpa [prefixWord, tailWord_7767428, baseEnd_7767428] using wordTrace_append hprefix tailTrace_7767428
  have hstable : (prefixWord ++ tailWord_7767428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767428).length < 2 ^ (prefixWord ++ tailWord_7767428).sum := by decide
  have hdescent : baseEnd_7767428 < baseStart_7767428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767468 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_7767468 : Nat := 118140960795 + 7767468 * 2 ^ 59
def prefixEnd_7767468 : Nat := 4983230072969 + 3 ^ 40 * 7767468 * 2
def baseEnd_7767468 : Nat := 3988444552417520979428071

theorem tailTrace_7767468 : CollatzResearch.WordTrace tailWord_7767468 prefixEnd_7767468 3988444552417520979428071 := by
  unfold tailWord_7767468
  simp only [CollatzResearch.WordTrace]
  refine ⟨141651416111898744382623529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188868554815864992510164705 141651416111898744382623529)
  ·
    refine ⟨106238562083924058286967647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141651416111898744382623529 106238562083924058286967647)
    ·
      refine ⟨159357843125886087430451471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106238562083924058286967647 159357843125886087430451471)
      ·
        refine ⟨239036764688829131145677207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159357843125886087430451471 239036764688829131145677207)
        ·
          refine ⟨358555147033243696718515811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239036764688829131145677207 358555147033243696718515811)
          ·
            refine ⟨537832720549865545077773717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358555147033243696718515811 537832720549865545077773717)
            ·
              refine ⟨25210908775774947425520643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 537832720549865545077773717 25210908775774947425520643)
              ·
                refine ⟨37816363163662421138280965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210908775774947425520643 37816363163662421138280965)
                ·
                  refine ⟨7090568093186703963427681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37816363163662421138280965 7090568093186703963427681)
                  ·
                    refine ⟨5317926069890027972570761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7090568093186703963427681 5317926069890027972570761)
                    ·
                      refine ⟨3988444552417520979428071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317926069890027972570761 3988444552417520979428071)
                      ·
                        rfl

theorem cell23_7767468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_7767468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767468 prefixEnd_7767468 := by exact prefixLift 7767468
  have htrace : WordTrace (prefixWord ++ tailWord_7767468) baseStart_7767468 baseEnd_7767468 := by
    simpa [prefixWord, tailWord_7767468, baseEnd_7767468] using wordTrace_append hprefix tailTrace_7767468
  have hstable : (prefixWord ++ tailWord_7767468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767468).length < 2 ^ (prefixWord ++ tailWord_7767468).sum := by decide
  have hdescent : baseEnd_7767468 < baseStart_7767468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767474 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_7767474 : Nat := 118140960795 + 7767474 * 2 ^ 59
def prefixEnd_7767474 : Nat := 4983230072969 + 3 ^ 40 * 7767474 * 2
def baseEnd_7767474 : Nat := 443160848144605328439227

theorem tailTrace_7767474 : CollatzResearch.WordTrace tailWord_7767474 prefixEnd_7767474 443160848144605328439227 := by
  unfold tailWord_7767474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70825762765443937947491369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188868700707850501193310317 70825762765443937947491369)
  ·
    refine ⟨53119322074082953460618527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70825762765443937947491369 53119322074082953460618527)
    ·
      refine ⟨79678983111124430190927791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53119322074082953460618527 79678983111124430190927791)
      ·
        refine ⟨119518474666686645286391687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79678983111124430190927791 119518474666686645286391687)
        ·
          refine ⟨179277712000029967929587531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119518474666686645286391687 179277712000029967929587531)
          ·
            refine ⟨268916568000044951894381297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179277712000029967929587531 268916568000044951894381297)
            ·
              refine ⟨201687426000033713920785973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268916568000044951894381297 201687426000033713920785973)
              ·
                refine ⟨18908196187503160680073685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201687426000033713920785973 18908196187503160680073685)
                ·
                  refine ⟨443160848144605328439227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18908196187503160680073685 443160848144605328439227)
                  ·
                    rfl

theorem cell23_7767474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_7767474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767474 prefixEnd_7767474 := by exact prefixLift 7767474
  have htrace : WordTrace (prefixWord ++ tailWord_7767474) baseStart_7767474 baseEnd_7767474 := by
    simpa [prefixWord, tailWord_7767474, baseEnd_7767474] using wordTrace_append hprefix tailTrace_7767474
  have hstable : (prefixWord ++ tailWord_7767474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767474).length < 2 ^ (prefixWord ++ tailWord_7767474).sum := by decide
  have hdescent : baseEnd_7767474 < baseStart_7767474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767485 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7767485 : Nat := 118140960795 + 7767485 * 2 ^ 59
def prefixEnd_7767485 : Nat := 4983230072969 + 3 ^ 40 * 7767485 * 2
def baseEnd_7767485 : Nat := 3988453281588647412915493

theorem tailTrace_7767485 : CollatzResearch.WordTrace tailWord_7767485 prefixEnd_7767485 3988453281588647412915493 := by
  unfold tailWord_7767485
  simp only [CollatzResearch.WordTrace]
  refine ⟨283303452264735900668615909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188868968176490600445743939 283303452264735900668615909)
  ·
    refine ⟨53119397299637981375365483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283303452264735900668615909 53119397299637981375365483)
    ·
      refine ⟨79679095949456972063048225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53119397299637981375365483 79679095949456972063048225)
      ·
        refine ⟨59759321962092729047286169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79679095949456972063048225 59759321962092729047286169)
        ·
          refine ⟨44819491471569546785464627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59759321962092729047286169 44819491471569546785464627)
          ·
            refine ⟨67229237207354320178196941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44819491471569546785464627 67229237207354320178196941)
            ·
              refine ⟨25210963952757870066823853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67229237207354320178196941 25210963952757870066823853)
              ·
                refine ⟨9454111482284201275058945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25210963952757870066823853 9454111482284201275058945)
                ·
                  refine ⟨7090583611713150956294209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454111482284201275058945 7090583611713150956294209)
                  ·
                    refine ⟨5317937708784863217220657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7090583611713150956294209 5317937708784863217220657)
                    ·
                      refine ⟨3988453281588647412915493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317937708784863217220657 3988453281588647412915493)
                      ·
                        rfl

theorem cell23_7767485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7767485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767485 prefixEnd_7767485 := by exact prefixLift 7767485
  have htrace : WordTrace (prefixWord ++ tailWord_7767485) baseStart_7767485 baseEnd_7767485 := by
    simpa [prefixWord, tailWord_7767485, baseEnd_7767485] using wordTrace_append hprefix tailTrace_7767485
  have hstable : (prefixWord ++ tailWord_7767485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767485).length < 2 ^ (prefixWord ++ tailWord_7767485).sum := by decide
  have hdescent : baseEnd_7767485 < baseStart_7767485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767504 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_7767504 : Nat := 118140960795 + 7767504 * 2 ^ 59
def prefixEnd_7767504 : Nat := 4983230072969 + 3 ^ 40 * 7767504 * 2
def baseEnd_7767504 : Nat := 1329487679240360946192635

theorem tailTrace_7767504 : CollatzResearch.WordTrace tailWord_7767504 prefixEnd_7767504 1329487679240360946192635 := by
  unfold tailWord_7767504
  simp only [CollatzResearch.WordTrace]
  refine ⟨141652072625833533456778783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188869430167778044609038377 141652072625833533456778783)
  ·
    refine ⟨212478108938750300185168175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141652072625833533456778783 212478108938750300185168175)
    ·
      refine ⟨318717163408125450277752263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212478108938750300185168175 318717163408125450277752263)
      ·
        refine ⟨478075745112188175416628395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318717163408125450277752263 478075745112188175416628395)
        ·
          refine ⟨717113617668282263124942593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478075745112188175416628395 717113617668282263124942593)
          ·
            refine ⟨537835213251211697343706945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717113617668282263124942593 537835213251211697343706945)
            ·
              refine ⟨403376409938408773007780209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537835213251211697343706945 403376409938408773007780209)
              ·
                refine ⟨302532307453806579755835157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403376409938408773007780209 302532307453806579755835157)
                ·
                  refine ⟨14181201911897183426054773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302532307453806579755835157 14181201911897183426054773)
                  ·
                    refine ⟨1329487679240360946192635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14181201911897183426054773 1329487679240360946192635)
                    ·
                      rfl

theorem cell23_7767504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_7767504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767504 prefixEnd_7767504 := by exact prefixLift 7767504
  have htrace : WordTrace (prefixWord ++ tailWord_7767504) baseStart_7767504 baseEnd_7767504 := by
    simpa [prefixWord, tailWord_7767504, baseEnd_7767504] using wordTrace_append hprefix tailTrace_7767504
  have hstable : (prefixWord ++ tailWord_7767504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767504).length < 2 ^ (prefixWord ++ tailWord_7767504).sum := by decide
  have hdescent : baseEnd_7767504 < baseStart_7767504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767511 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_7767511 : Nat := 118140960795 + 7767511 * 2 ^ 59
def prefixEnd_7767511 : Nat := 4983230072969 + 3 ^ 40 * 7767511 * 2
def baseEnd_7767511 : Nat := 3988466632085664311190373

theorem tailTrace_7767511 : CollatzResearch.WordTrace tailWord_7767511 prefixEnd_7767511 3988466632085664311190373 := by
  unfold tailWord_7767511
  simp only [CollatzResearch.WordTrace]
  refine ⟨283304400562641707109062387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188869600375094471406041591 283304400562641707109062387)
  ·
    refine ⟨424956600843962560663593581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283304400562641707109062387 424956600843962560663593581)
    ·
      refine ⟨159358725316485960248847593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424956600843962560663593581 159358725316485960248847593)
      ·
        refine ⟨119519043987364470186635695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159358725316485960248847593 119519043987364470186635695)
        ·
          refine ⟨179278565981046705279953543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119519043987364470186635695 179278565981046705279953543)
          ·
            refine ⟨268917848971570057919930315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179278565981046705279953543 268917848971570057919930315)
            ·
              refine ⟨403376773457355086879895473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268917848971570057919930315 403376773457355086879895473)
              ·
                refine ⟨302532580093016315159921605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403376773457355086879895473 302532580093016315159921605)
                ·
                  refine ⟨56724858767440559092485301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302532580093016315159921605 56724858767440559092485301)
                  ·
                    refine ⟨5317955509447552414920497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56724858767440559092485301 5317955509447552414920497)
                    ·
                      refine ⟨3988466632085664311190373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5317955509447552414920497 3988466632085664311190373)
                      ·
                        rfl

theorem cell23_7767511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_7767511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767511 prefixEnd_7767511 := by exact prefixLift 7767511
  have htrace : WordTrace (prefixWord ++ tailWord_7767511) baseStart_7767511 baseEnd_7767511 := by
    simpa [prefixWord, tailWord_7767511, baseEnd_7767511] using wordTrace_append hprefix tailTrace_7767511
  have hstable : (prefixWord ++ tailWord_7767511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767511).length < 2 ^ (prefixWord ++ tailWord_7767511).sum := by decide
  have hdescent : baseEnd_7767511 < baseStart_7767511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767521 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_7767521 : Nat := 118140960795 + 7767521 * 2 ^ 59
def prefixEnd_7767521 : Nat := 4983230072969 + 3 ^ 40 * 7767521 * 2
def baseEnd_7767521 : Nat := 1329490588964069757355109

theorem tailTrace_7767521 : CollatzResearch.WordTrace tailWord_7767521 prefixEnd_7767521 1329490588964069757355109 := by
  unfold tailWord_7767521
  simp only [CollatzResearch.WordTrace]
  refine ⟨283304765292605478816926417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188869843528403652544617611 283304765292605478816926417)
  ·
    refine ⟨212478573969454109112694813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283304765292605478816926417 212478573969454109112694813)
    ·
      refine ⟨79679465238545290917260555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212478573969454109112694813 79679465238545290917260555)
      ·
        refine ⟨119519197857817936375890833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79679465238545290917260555 119519197857817936375890833)
        ·
          refine ⟨89639398393363452281918125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119519197857817936375890833 89639398393363452281918125)
          ·
            refine ⟨33614774397511294605719297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89639398393363452281918125 33614774397511294605719297)
            ·
              refine ⟨25211080798133470954289473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33614774397511294605719297 25211080798133470954289473)
              ·
                refine ⟨18908310598600103215717105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25211080798133470954289473 18908310598600103215717105)
                ·
                  refine ⟨14181232948950077411787829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18908310598600103215717105 14181232948950077411787829)
                  ·
                    refine ⟨1329490588964069757355109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14181232948950077411787829 1329490588964069757355109)
                    ·
                      rfl

theorem cell23_7767521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_7767521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767521 prefixEnd_7767521 := by exact prefixLift 7767521
  have htrace : WordTrace (prefixWord ++ tailWord_7767521) baseStart_7767521 baseEnd_7767521 := by
    simpa [prefixWord, tailWord_7767521, baseEnd_7767521] using wordTrace_append hprefix tailTrace_7767521
  have hstable : (prefixWord ++ tailWord_7767521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767521).length < 2 ^ (prefixWord ++ tailWord_7767521).sum := by decide
  have hdescent : baseEnd_7767521 < baseStart_7767521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767525 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 5]
def baseStart_7767525 : Nat := 118140960795 + 7767525 * 2 ^ 59
def prefixEnd_7767525 : Nat := 4983230072969 + 3 ^ 40 * 7767525 * 2
def baseEnd_7767525 : Nat := 443163757868314139601701

theorem tailTrace_7767525 : CollatzResearch.WordTrace tailWord_7767525 prefixEnd_7767525 443163757868314139601701 := by
  unfold tailWord_7767525
  simp only [CollatzResearch.WordTrace]
  refine ⟨283304911184590987500072029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188869940789727325000048019 283304911184590987500072029)
  ·
    refine ⟨106239341694221620312527011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283304911184590987500072029 106239341694221620312527011)
    ·
      refine ⟨159359012541332430468790517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106239341694221620312527011 159359012541332430468790517)
      ·
        refine ⟨14939907425749915356449111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159359012541332430468790517 14939907425749915356449111)
        ·
          refine ⟨22409861138624873034673667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939907425749915356449111 22409861138624873034673667)
          ·
            refine ⟨33614791707937309552010501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22409861138624873034673667 33614791707937309552010501)
            ·
              refine ⟨6302773445238245541001969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33614791707937309552010501 6302773445238245541001969)
              ·
                refine ⟨4727080083928684155751477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302773445238245541001969 4727080083928684155751477)
                ·
                  refine ⟨443163757868314139601701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727080083928684155751477 443163757868314139601701)
                  ·
                    rfl

theorem cell23_7767525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_7767525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767525 prefixEnd_7767525 := by exact prefixLift 7767525
  have htrace : WordTrace (prefixWord ++ tailWord_7767525) baseStart_7767525 baseEnd_7767525 := by
    simpa [prefixWord, tailWord_7767525, baseEnd_7767525] using wordTrace_append hprefix tailTrace_7767525
  have hstable : (prefixWord ++ tailWord_7767525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767525).length < 2 ^ (prefixWord ++ tailWord_7767525).sum := by decide
  have hdescent : baseEnd_7767525 < baseStart_7767525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767561 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_7767561 : Nat := 118140960795 + 7767561 * 2 ^ 59
def prefixEnd_7767561 : Nat := 4983230072969 + 3 ^ 40 * 7767561 * 2
def baseEnd_7767561 : Nat := 3988492306118389115565143

theorem tailTrace_7767561 : CollatzResearch.WordTrace tailWord_7767561 prefixEnd_7767561 3988492306118389115565143 := by
  unfold tailWord_7767561
  simp only [CollatzResearch.WordTrace]
  refine ⟨283306224212460565648382537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188870816141640377098921691 283306224212460565648382537)
  ·
    refine ⟨212479668159345424236286903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283306224212460565648382537 212479668159345424236286903)
    ·
      refine ⟨318719502239018136354430355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212479668159345424236286903 318719502239018136354430355)
      ·
        refine ⟨478079253358527204531645533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318719502239018136354430355 478079253358527204531645533)
        ·
          refine ⟨179279720009447701699367075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478079253358527204531645533 179279720009447701699367075)
          ·
            refine ⟨268919580014171552549050613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179279720009447701699367075 268919580014171552549050613)
            ·
              refine ⟨25211210626328583051473495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268919580014171552549050613 25211210626328583051473495)
              ·
                refine ⟨37816815939492874577210243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25211210626328583051473495 37816815939492874577210243)
                ·
                  refine ⟨56725223909239311865815365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37816815939492874577210243 56725223909239311865815365)
                  ·
                    refine ⟨10635979482982370974840381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56725223909239311865815365 10635979482982370974840381)
                    ·
                      refine ⟨3988492306118389115565143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10635979482982370974840381 3988492306118389115565143)
                      ·
                        rfl

theorem cell23_7767561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_7767561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767561 prefixEnd_7767561 := by exact prefixLift 7767561
  have htrace : WordTrace (prefixWord ++ tailWord_7767561) baseStart_7767561 baseEnd_7767561 := by
    simpa [prefixWord, tailWord_7767561, baseEnd_7767561] using wordTrace_append hprefix tailTrace_7767561
  have hstable : (prefixWord ++ tailWord_7767561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767561).length < 2 ^ (prefixWord ++ tailWord_7767561).sum := by decide
  have hdescent : baseEnd_7767561 < baseStart_7767561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767581 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 8]
def baseStart_7767581 : Nat := 118140960795 + 7767581 * 2 ^ 59
def prefixEnd_7767581 : Nat := 4983230072969 + 3 ^ 40 * 7767581 * 2
def baseEnd_7767581 : Nat := 443166952859053226368339

theorem tailTrace_7767581 : CollatzResearch.WordTrace tailWord_7767581 prefixEnd_7767581 443166952859053226368339 := by
  unfold tailWord_7767581
  simp only [CollatzResearch.WordTrace]
  refine ⟨283306953672388109064110597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188871302448258739376073731 283306953672388109064110597)
  ·
    refine ⟨53120053813572770449520737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283306953672388109064110597 53120053813572770449520737)
    ·
      refine ⟨39840040360179577837140553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53120053813572770449520737 39840040360179577837140553)
      ·
        refine ⟨29880030270134683377855415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39840040360179577837140553 29880030270134683377855415)
        ·
          refine ⟨44820045405202025066783123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29880030270134683377855415 44820045405202025066783123)
          ·
            refine ⟨67230068107803037600174685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44820045405202025066783123 67230068107803037600174685)
            ·
              refine ⟨25211275540426139100065507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67230068107803037600174685 25211275540426139100065507)
              ·
                refine ⟨37816913310639208650098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25211275540426139100065507 37816913310639208650098261)
                ·
                  refine ⟨443166952859053226368339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37816913310639208650098261 443166952859053226368339)
                  ·
                    rfl

theorem cell23_7767581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_7767581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767581 prefixEnd_7767581 := by exact prefixLift 7767581
  have htrace : WordTrace (prefixWord ++ tailWord_7767581) baseStart_7767581 baseEnd_7767581 := by
    simpa [prefixWord, tailWord_7767581, baseEnd_7767581] using wordTrace_append hprefix tailTrace_7767581
  have hstable : (prefixWord ++ tailWord_7767581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767581).length < 2 ^ (prefixWord ++ tailWord_7767581).sum := by decide
  have hdescent : baseEnd_7767581 < baseStart_7767581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767585 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7767585 : Nat := 118140960795 + 7767585 * 2 ^ 59
def prefixEnd_7767585 : Nat := 4983230072969 + 3 ^ 40 * 7767585 * 2
def baseEnd_7767585 : Nat := 1329501543218032340555011

theorem tailTrace_7767585 : CollatzResearch.WordTrace tailWord_7767585 prefixEnd_7767585 1329501543218032340555011 := by
  unfold tailWord_7767585
  simp only [CollatzResearch.WordTrace]
  refine ⟨283307099564373617747256209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188871399709582411831504139 283307099564373617747256209)
  ·
    refine ⟨212480324673280213310442157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283307099564373617747256209 212480324673280213310442157)
    ·
      refine ⟨79680121752480079991415809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212480324673280213310442157 79680121752480079991415809)
      ·
        refine ⟨59760091314360059993561857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79680121752480079991415809 59760091314360059993561857)
        ·
          refine ⟨44820068485770044995171393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59760091314360059993561857 44820068485770044995171393)
          ·
            refine ⟨33615051364327533746378545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44820068485770044995171393 33615051364327533746378545)
            ·
              refine ⟨25211288523245650309783909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33615051364327533746378545 25211288523245650309783909)
              ·
                refine ⟨4727116598108559433084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25211288523245650309783909 4727116598108559433084483)
                ·
                  refine ⟨7090674897162839149626725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727116598108559433084483 7090674897162839149626725)
                  ·
                    refine ⟨1329501543218032340555011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090674897162839149626725 1329501543218032340555011)
                    ·
                      rfl

theorem cell23_7767585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7767585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767585 prefixEnd_7767585 := by exact prefixLift 7767585
  have htrace : WordTrace (prefixWord ++ tailWord_7767585) baseStart_7767585 baseEnd_7767585 := by
    simpa [prefixWord, tailWord_7767585, baseEnd_7767585] using wordTrace_append hprefix tailTrace_7767585
  have hstable : (prefixWord ++ tailWord_7767585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767585).length < 2 ^ (prefixWord ++ tailWord_7767585).sum := by decide
  have hdescent : baseEnd_7767585 < baseStart_7767585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767628 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_7767628 : Nat := 118140960795 + 7767628 * 2 ^ 59
def prefixEnd_7767628 : Nat := 4983230072969 + 3 ^ 40 * 7767628 * 2
def baseEnd_7767628 : Nat := 1329508903107413451142445

theorem tailTrace_7767628 : CollatzResearch.WordTrace tailWord_7767628 prefixEnd_7767628 1329508903107413451142445 := by
  unfold tailWord_7767628
  simp only [CollatzResearch.WordTrace]
  refine ⟨141654333951608918045535769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188872445268811890727381025 141654333951608918045535769)
  ·
    refine ⟨106240750463706688534151827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141654333951608918045535769 106240750463706688534151827)
    ·
      refine ⟨159361125695560032801227741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106240750463706688534151827 159361125695560032801227741)
      ·
        refine ⟨59760422135835012300460403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159361125695560032801227741 59760422135835012300460403)
        ·
          refine ⟨89640633203752518450690605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59760422135835012300460403 89640633203752518450690605)
          ·
            refine ⟨33615237451407194419008977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89640633203752518450690605 33615237451407194419008977)
            ·
              refine ⟨25211428088555395814256733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33615237451407194419008977 25211428088555395814256733)
              ·
                refine ⟨9454285533208273430346275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25211428088555395814256733 9454285533208273430346275)
                ·
                  refine ⟨14181428299812410145519413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9454285533208273430346275 14181428299812410145519413)
                  ·
                    refine ⟨1329508903107413451142445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14181428299812410145519413 1329508903107413451142445)
                    ·
                      rfl

theorem cell23_7767628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_7767628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767628 prefixEnd_7767628 := by exact prefixLift 7767628
  have htrace : WordTrace (prefixWord ++ tailWord_7767628) baseStart_7767628 baseEnd_7767628 := by
    simpa [prefixWord, tailWord_7767628, baseEnd_7767628] using wordTrace_append hprefix tailTrace_7767628
  have hstable : (prefixWord ++ tailWord_7767628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767628).length < 2 ^ (prefixWord ++ tailWord_7767628).sum := by decide
  have hdescent : baseEnd_7767628 < baseStart_7767628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767631 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_7767631 : Nat := 118140960795 + 7767631 * 2 ^ 59
def prefixEnd_7767631 : Nat := 4983230072969 + 3 ^ 40 * 7767631 * 2
def baseEnd_7767631 : Nat := 3988528249764203841689821

theorem tailTrace_7767631 : CollatzResearch.WordTrace tailWord_7767631 prefixEnd_7767631 3988528249764203841689821 := by
  unfold tailWord_7767631
  simp only [CollatzResearch.WordTrace]
  refine ⟨283308777322206967603430747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188872518214804645068953831 283308777322206967603430747)
  ·
    refine ⟨424963165983310451405146121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283308777322206967603430747 424963165983310451405146121)
    ·
      refine ⟨318722374487482838553859591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424963165983310451405146121 318722374487482838553859591)
      ·
        refine ⟨478083561731224257830789387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318722374487482838553859591 478083561731224257830789387)
        ·
          refine ⟨717125342596836386746184081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478083561731224257830789387 717125342596836386746184081)
          ·
            refine ⟨537844006947627290059638061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717125342596836386746184081 537844006947627290059638061)
            ·
              refine ⟨201691502605360233772364273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537844006947627290059638061 201691502605360233772364273)
              ·
                refine ⟨151268626954020175329273205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201691502605360233772364273 151268626954020175329273205)
                ·
                  refine ⟨14181433776939391437119363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151268626954020175329273205 14181433776939391437119363)
                  ·
                    refine ⟨21272150665409087155679045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14181433776939391437119363 21272150665409087155679045)
                    ·
                      refine ⟨3988528249764203841689821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21272150665409087155679045 3988528249764203841689821)
                      ·
                        rfl

theorem cell23_7767631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_7767631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767631 prefixEnd_7767631 := by exact prefixLift 7767631
  have htrace : WordTrace (prefixWord ++ tailWord_7767631) baseStart_7767631 baseEnd_7767631 := by
    simpa [prefixWord, tailWord_7767631, baseEnd_7767631] using wordTrace_append hprefix tailTrace_7767631
  have hstable : (prefixWord ++ tailWord_7767631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767631).length < 2 ^ (prefixWord ++ tailWord_7767631).sum := by decide
  have hdescent : baseEnd_7767631 < baseStart_7767631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767662 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_7767662 : Nat := 118140960795 + 7767662 * 2 ^ 59
def prefixEnd_7767662 : Nat := 4983230072969 + 3 ^ 40 * 7767662 * 2
def baseEnd_7767662 : Nat := 1329514722554831073467393

theorem tailTrace_7767662 : CollatzResearch.WordTrace tailWord_7767662 prefixEnd_7767662 1329514722554831073467393 := by
  unfold tailWord_7767662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35413738498136832487226155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188873271990063106598539493 35413738498136832487226155)
  ·
    refine ⟨53120607747205248730839233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35413738498136832487226155 53120607747205248730839233)
    ·
      refine ⟨39840455810403936548129425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53120607747205248730839233 39840455810403936548129425)
      ·
        refine ⟨29880341857802952411097069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39840455810403936548129425 29880341857802952411097069)
        ·
          refine ⟨11205128196676107154161401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29880341857802952411097069 11205128196676107154161401)
          ·
            refine ⟨8403846147507080365621051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11205128196676107154161401 8403846147507080365621051)
            ·
              refine ⟨12605769221260620548431577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403846147507080365621051 12605769221260620548431577)
              ·
                refine ⟨9454326915945465411323683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12605769221260620548431577 9454326915945465411323683)
                ·
                  refine ⟨14181490373918198116985525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9454326915945465411323683 14181490373918198116985525)
                  ·
                    refine ⟨1329514722554831073467393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14181490373918198116985525 1329514722554831073467393)
                    ·
                      rfl

theorem cell23_7767662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_7767662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767662 prefixEnd_7767662 := by exact prefixLift 7767662
  have htrace : WordTrace (prefixWord ++ tailWord_7767662) baseStart_7767662 baseEnd_7767662 := by
    simpa [prefixWord, tailWord_7767662, baseEnd_7767662] using wordTrace_append hprefix tailTrace_7767662
  have hstable : (prefixWord ++ tailWord_7767662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767662).length < 2 ^ (prefixWord ++ tailWord_7767662).sum := by decide
  have hdescent : baseEnd_7767662 < baseStart_7767662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767665 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_7767665 : Nat := 118140960795 + 7767665 * 2 ^ 59
def prefixEnd_7767665 : Nat := 4983230072969 + 3 ^ 40 * 7767665 * 2
def baseEnd_7767665 : Nat := 3988545708106456708664665

theorem tailTrace_7767665 : CollatzResearch.WordTrace tailWord_7767665 prefixEnd_7767665 3988545708106456708664665 := by
  unfold tailWord_7767665
  simp only [CollatzResearch.WordTrace]
  refine ⟨283310017404083791410168449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188873344936055860940112299 283310017404083791410168449)
  ·
    refine ⟨212482513053062843557626337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283310017404083791410168449 212482513053062843557626337)
    ·
      refine ⟨159361884789797132668219753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212482513053062843557626337 159361884789797132668219753)
      ·
        refine ⟨119521413592347849501164815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159361884789797132668219753 119521413592347849501164815)
        ·
          refine ⟨179282120388521774251747223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119521413592347849501164815 179282120388521774251747223)
          ·
            refine ⟨268923180582782661377620835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179282120388521774251747223 268923180582782661377620835)
            ·
              refine ⟨403384770874173992066431253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268923180582782661377620835 403384770874173992066431253)
              ·
                refine ⟨18908661134726905878113965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403384770874173992066431253 18908661134726905878113965)
                ·
                  refine ⟨7090747925522589704292737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18908661134726905878113965 7090747925522589704292737)
                  ·
                    refine ⟨5318060944141942278219553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7090747925522589704292737 5318060944141942278219553)
                    ·
                      refine ⟨3988545708106456708664665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318060944141942278219553 3988545708106456708664665)
                      ·
                        rfl

theorem cell23_7767665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_7767665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767665 prefixEnd_7767665 := by exact prefixLift 7767665
  have htrace : WordTrace (prefixWord ++ tailWord_7767665) baseStart_7767665 baseEnd_7767665 := by
    simpa [prefixWord, tailWord_7767665, baseEnd_7767665] using wordTrace_append hprefix tailTrace_7767665
  have hstable : (prefixWord ++ tailWord_7767665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767665).length < 2 ^ (prefixWord ++ tailWord_7767665).sum := by decide
  have hdescent : baseEnd_7767665 < baseStart_7767665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767688 : List Nat := [2, 1, 3, 5, 1, 11]
def baseStart_7767688 : Nat := 118140960795 + 7767688 * 2 ^ 59
def prefixEnd_7767688 : Nat := 4983230072969 + 3 ^ 40 * 7767688 * 2
def baseEnd_7767688 : Nat := 16413816947166708307313

theorem tailTrace_7767688 : CollatzResearch.WordTrace tailWord_7767688 prefixEnd_7767688 16413816947166708307313 := by
  unfold tailWord_7767688
  simp only [CollatzResearch.WordTrace]
  refine ⟨141655428141500233169127859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188873904188666977558837145 141655428141500233169127859)
  ·
    refine ⟨212483142212250349753691789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141655428141500233169127859 212483142212250349753691789)
    ·
      refine ⟨79681178329593881157634421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212483142212250349753691789 79681178329593881157634421)
      ·
        refine ⟨7470110468399426358528227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79681178329593881157634421 7470110468399426358528227)
        ·
          refine ⟨11205165702599139537792341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470110468399426358528227 11205165702599139537792341)
          ·
            refine ⟨16413816947166708307313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11205165702599139537792341 16413816947166708307313)
            ·
              rfl

theorem cell23_7767688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 11].length) (baseStart_7767688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767688 prefixEnd_7767688 := by exact prefixLift 7767688
  have htrace : WordTrace (prefixWord ++ tailWord_7767688) baseStart_7767688 baseEnd_7767688 := by
    simpa [prefixWord, tailWord_7767688, baseEnd_7767688] using wordTrace_append hprefix tailTrace_7767688
  have hstable : (prefixWord ++ tailWord_7767688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767688).length < 2 ^ (prefixWord ++ tailWord_7767688).sum := by decide
  have hdescent : baseEnd_7767688 < baseStart_7767688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767715 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 3]
def baseStart_7767715 : Nat := 118140960795 + 7767715 * 2 ^ 59
def prefixEnd_7767715 : Nat := 4983230072969 + 3 ^ 40 * 7767715 * 2
def baseEnd_7767715 : Nat := 3988571382139181513039435

theorem tailTrace_7767715 : CollatzResearch.WordTrace tailWord_7767715 prefixEnd_7767715 3988571382139181513039435 := by
  unfold tailWord_7767715
  simp only [CollatzResearch.WordTrace]
  refine ⟨283311841053902649949488599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188874560702601766632992399 283311841053902649949488599)
  ·
    refine ⟨424967761580853974924232899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283311841053902649949488599 424967761580853974924232899)
    ·
      refine ⟨637451642371280962386349349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424967761580853974924232899 637451642371280962386349349)
      ·
        refine ⟨119522182944615180447440503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637451642371280962386349349 119522182944615180447440503)
        ·
          refine ⟨179283274416922770671160755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119522182944615180447440503 179283274416922770671160755)
          ·
            refine ⟨268924911625384156006741133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179283274416922770671160755 268924911625384156006741133)
            ·
              refine ⟨100846841859519058502527925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268924911625384156006741133 100846841859519058502527925)
              ·
                refine ⟨9454391424329911734611993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100846841859519058502527925 9454391424329911734611993)
                ·
                  refine ⟨7090793568247433800958995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454391424329911734611993 7090793568247433800958995)
                  ·
                    refine ⟨10636190352371150701438493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090793568247433800958995 10636190352371150701438493)
                    ·
                      refine ⟨3988571382139181513039435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636190352371150701438493 3988571382139181513039435)
                      ·
                        rfl

theorem cell23_7767715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_7767715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767715 prefixEnd_7767715 := by exact prefixLift 7767715
  have htrace : WordTrace (prefixWord ++ tailWord_7767715) baseStart_7767715 baseEnd_7767715 := by
    simpa [prefixWord, tailWord_7767715, baseEnd_7767715] using wordTrace_append hprefix tailTrace_7767715
  have hstable : (prefixWord ++ tailWord_7767715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767715).length < 2 ^ (prefixWord ++ tailWord_7767715).sum := by decide
  have hdescent : baseEnd_7767715 < baseStart_7767715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767721 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_7767721 : Nat := 118140960795 + 7767721 * 2 ^ 59
def prefixEnd_7767721 : Nat := 4983230072969 + 3 ^ 40 * 7767721 * 2
def baseEnd_7767721 : Nat := 3988574463023108489564407

theorem tailTrace_7767721 : CollatzResearch.WordTrace tailWord_7767721 prefixEnd_7767721 3988574463023108489564407 := by
  unfold tailWord_7767721
  simp only [CollatzResearch.WordTrace]
  refine ⟨283312059891880912974207017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188874706594587275316138011 283312059891880912974207017)
  ·
    refine ⟨212484044918910684730655263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283312059891880912974207017 212484044918910684730655263)
    ·
      refine ⟨318726067378366027095982895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212484044918910684730655263 318726067378366027095982895)
      ·
        refine ⟨478089101067549040643974343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318726067378366027095982895 478089101067549040643974343)
        ·
          refine ⟨717133651601323560965961515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478089101067549040643974343 717133651601323560965961515)
          ·
            refine ⟨1075700477401985341448942273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717133651601323560965961515 1075700477401985341448942273)
            ·
              refine ⟨806775358051489006086706705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075700477401985341448942273 806775358051489006086706705)
              ·
                refine ⟨605081518538616754565030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806775358051489006086706705 605081518538616754565030029)
                ·
                  refine ⟨226905569451981282961886261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605081518538616754565030029 226905569451981282961886261)
                  ·
                    refine ⟨21272397136123245277676837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226905569451981282961886261 21272397136123245277676837)
                    ·
                      refine ⟨3988574463023108489564407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21272397136123245277676837 3988574463023108489564407)
                      ·
                        rfl

theorem cell23_7767721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_7767721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767721 prefixEnd_7767721 := by exact prefixLift 7767721
  have htrace : WordTrace (prefixWord ++ tailWord_7767721) baseStart_7767721 baseEnd_7767721 := by
    simpa [prefixWord, tailWord_7767721, baseEnd_7767721] using wordTrace_append hprefix tailTrace_7767721
  have hstable : (prefixWord ++ tailWord_7767721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767721).length < 2 ^ (prefixWord ++ tailWord_7767721).sum := by decide
  have hdescent : baseEnd_7767721 < baseStart_7767721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767731 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 8]
def baseStart_7767731 : Nat := 118140960795 + 7767731 * 2 ^ 59
def prefixEnd_7767731 : Nat := 4983230072969 + 3 ^ 40 * 7767731 * 2
def baseEnd_7767731 : Nat := 1329526532609884483479787

theorem tailTrace_7767731 : CollatzResearch.WordTrace tailWord_7767731 prefixEnd_7767731 1329526532609884483479787 := by
  unfold tailWord_7767731
  simp only [CollatzResearch.WordTrace]
  refine ⟨283312424621844684682071047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188874949747896456454714031 283312424621844684682071047)
  ·
    refine ⟨424968636932767027023106571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283312424621844684682071047 424968636932767027023106571)
    ·
      refine ⟨637452955399150540534659857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424968636932767027023106571 637452955399150540534659857)
      ·
        refine ⟨478089716549362905400994893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637452955399150540534659857 478089716549362905400994893)
        ·
          refine ⟨179283643706011089525373085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478089716549362905400994893 179283643706011089525373085)
          ·
            refine ⟨67231366389754158572014907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179283643706011089525373085 67231366389754158572014907)
            ·
              refine ⟨100847049584631237858022361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67231366389754158572014907 100847049584631237858022361)
              ·
                refine ⟨75635287188473428393516771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100847049584631237858022361 75635287188473428393516771)
                ·
                  refine ⟨113452930782710142590275157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75635287188473428393516771 113452930782710142590275157)
                  ·
                    refine ⟨1329526532609884483479787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113452930782710142590275157 1329526532609884483479787)
                    ·
                      rfl

theorem cell23_7767731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_7767731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767731 prefixEnd_7767731 := by exact prefixLift 7767731
  have htrace : WordTrace (prefixWord ++ tailWord_7767731) baseStart_7767731 baseEnd_7767731 := by
    simpa [prefixWord, tailWord_7767731, baseEnd_7767731] using wordTrace_append hprefix tailTrace_7767731
  have hstable : (prefixWord ++ tailWord_7767731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767731).length < 2 ^ (prefixWord ++ tailWord_7767731).sum := by decide
  have hdescent : baseEnd_7767731 < baseStart_7767731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767748 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7767748 : Nat := 118140960795 + 7767748 * 2 ^ 59
def prefixEnd_7767748 : Nat := 4983230072969 + 3 ^ 40 * 7767748 * 2
def baseEnd_7767748 : Nat := 1329529442333593294642261

theorem tailTrace_7767748 : CollatzResearch.WordTrace tailWord_7767748 prefixEnd_7767748 1329529442333593294642261 := by
  unfold tailWord_7767748
  simp only [CollatzResearch.WordTrace]
  refine ⟨141656522331391548292719949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188875363108522064390293265 141656522331391548292719949)
  ·
    refine ⟨53121195874271830609769981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141656522331391548292719949 53121195874271830609769981)
    ·
      refine ⟨19920448452851936478663743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53121195874271830609769981 19920448452851936478663743)
      ·
        refine ⟨29880672679277904717995615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19920448452851936478663743 29880672679277904717995615)
        ·
          refine ⟨44821009018916857076993423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29880672679277904717995615 44821009018916857076993423)
          ·
            refine ⟨67231513528375285615490135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44821009018916857076993423 67231513528375285615490135)
            ·
              refine ⟨100847270292562928423235203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67231513528375285615490135 100847270292562928423235203)
              ·
                refine ⟨151270905438844392634852805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100847270292562928423235203 151270905438844392634852805)
                ·
                  refine ⟨28363294769783323619034901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151270905438844392634852805 28363294769783323619034901)
                  ·
                    refine ⟨1329529442333593294642261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28363294769783323619034901 1329529442333593294642261)
                    ·
                      rfl

theorem cell23_7767748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7767748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767748 prefixEnd_7767748 := by exact prefixLift 7767748
  have htrace : WordTrace (prefixWord ++ tailWord_7767748) baseStart_7767748 baseEnd_7767748 := by
    simpa [prefixWord, tailWord_7767748, baseEnd_7767748] using wordTrace_append hprefix tailTrace_7767748
  have hstable : (prefixWord ++ tailWord_7767748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767748).length < 2 ^ (prefixWord ++ tailWord_7767748).sum := by decide
  have hdescent : baseEnd_7767748 < baseStart_7767748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767766 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7767766 : Nat := 118140960795 + 7767766 * 2 ^ 59
def prefixEnd_7767766 : Nat := 4983230072969 + 3 ^ 40 * 7767766 * 2
def baseEnd_7767766 : Nat := 3988597569652560813501701

theorem tailTrace_7767766 : CollatzResearch.WordTrace tailWord_7767766 prefixEnd_7767766 3988597569652560813501701 := by
  unfold tailWord_7767766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707106323544867853724697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188875800784478590439730101 17707106323544867853724697)
  ·
    refine ⟨13280329742658650890293523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17707106323544867853724697 13280329742658650890293523)
    ·
      refine ⟨19920494613987976335440285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280329742658650890293523 19920494613987976335440285)
      ·
        refine ⟨7470185480245491125790107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19920494613987976335440285 7470185480245491125790107)
        ·
          refine ⟨11205278220368236688685161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470185480245491125790107 11205278220368236688685161)
          ·
            refine ⟨8403958665276177516513871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11205278220368236688685161 8403958665276177516513871)
            ·
              refine ⟨12605937997914266274770807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8403958665276177516513871 12605937997914266274770807)
              ·
                refine ⟨18908906996871399412156211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12605937997914266274770807 18908906996871399412156211)
                ·
                  refine ⟨28363360495307099118234317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18908906996871399412156211 28363360495307099118234317)
                  ·
                    refine ⟨10636260185740162169337869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28363360495307099118234317 10636260185740162169337869)
                    ·
                      refine ⟨3988597569652560813501701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636260185740162169337869 3988597569652560813501701)
                      ·
                        rfl

theorem cell23_7767766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7767766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767766 prefixEnd_7767766 := by exact prefixLift 7767766
  have htrace : WordTrace (prefixWord ++ tailWord_7767766) baseStart_7767766 baseEnd_7767766 := by
    simpa [prefixWord, tailWord_7767766, baseEnd_7767766] using wordTrace_append hprefix tailTrace_7767766
  have hstable : (prefixWord ++ tailWord_7767766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767766).length < 2 ^ (prefixWord ++ tailWord_7767766).sum := by decide
  have hdescent : baseEnd_7767766 < baseStart_7767766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767768 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_7767768 : Nat := 118140960795 + 7767768 * 2 ^ 59
def prefixEnd_7767768 : Nat := 4983230072969 + 3 ^ 40 * 7767768 * 2
def baseEnd_7767768 : Nat := 3988598596613869805676691

theorem tailTrace_7767768 : CollatzResearch.WordTrace tailWord_7767768 prefixEnd_7767768 3988598596613869805676691 := by
  unfold tailWord_7767768
  simp only [CollatzResearch.WordTrace]
  refine ⟨141656887061355320000583979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188875849415140426667445305 141656887061355320000583979)
  ·
    refine ⟨212485330592032980000875969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141656887061355320000583979 212485330592032980000875969)
    ·
      refine ⟨159363997944024735000656977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212485330592032980000875969 159363997944024735000656977)
      ·
        refine ⟨119522998458018551250492733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159363997944024735000656977 119522998458018551250492733)
        ·
          refine ⟨44821124421756956718934775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119522998458018551250492733 44821124421756956718934775)
          ·
            refine ⟨67231686632635435078402163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44821124421756956718934775 67231686632635435078402163)
            ·
              refine ⟨100847529948953152617603245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67231686632635435078402163 100847529948953152617603245)
              ·
                refine ⟨37817823730857432231601217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100847529948953152617603245 37817823730857432231601217)
                ·
                  refine ⟨28363367798143074173700913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37817823730857432231601217 28363367798143074173700913)
                  ·
                    refine ⟨21272525848607305630275685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28363367798143074173700913 21272525848607305630275685)
                    ·
                      refine ⟨3988598596613869805676691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21272525848607305630275685 3988598596613869805676691)
                      ·
                        rfl

theorem cell23_7767768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_7767768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767768 prefixEnd_7767768 := by exact prefixLift 7767768
  have htrace : WordTrace (prefixWord ++ tailWord_7767768) baseStart_7767768 baseEnd_7767768 := by
    simpa [prefixWord, tailWord_7767768, baseEnd_7767768] using wordTrace_append hprefix tailTrace_7767768
  have hstable : (prefixWord ++ tailWord_7767768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767768).length < 2 ^ (prefixWord ++ tailWord_7767768).sum := by decide
  have hdescent : baseEnd_7767768 < baseStart_7767768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767788 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_7767788 : Nat := 118140960795 + 7767788 * 2 ^ 59
def prefixEnd_7767788 : Nat := 4983230072969 + 3 ^ 40 * 7767788 * 2
def baseEnd_7767788 : Nat := 3988608866226959727426599

theorem tailTrace_7767788 : CollatzResearch.WordTrace tailWord_7767788 prefixEnd_7767788 3988608866226959727426599 := by
  unfold tailWord_7767788
  simp only [CollatzResearch.WordTrace]
  refine ⟨141657251791319091708448009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188876335721758788944597345 141657251791319091708448009)
  ·
    refine ⟨106242938843489318781336007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141657251791319091708448009 106242938843489318781336007)
    ·
      refine ⟨159364408265233978172004011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106242938843489318781336007 159364408265233978172004011)
      ·
        refine ⟨239046612397850967258006017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159364408265233978172004011 239046612397850967258006017)
        ·
          refine ⟨179284959298388225443504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239046612397850967258006017 179284959298388225443504513)
          ·
            refine ⟨134463719473791169082628385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179284959298388225443504513 134463719473791169082628385)
            ·
              refine ⟨100847789605343376811971289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134463719473791169082628385 100847789605343376811971289)
              ·
                refine ⟨75635842204007532608978467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100847789605343376811971289 75635842204007532608978467)
                ·
                  refine ⟨113453763306011298913467701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75635842204007532608978467 113453763306011298913467701)
                  ·
                    refine ⟨10636290309938559273137597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113453763306011298913467701 10636290309938559273137597)
                    ·
                      refine ⟨3988608866226959727426599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636290309938559273137597 3988608866226959727426599)
                      ·
                        rfl

theorem cell23_7767788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_7767788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767788 prefixEnd_7767788 := by exact prefixLift 7767788
  have htrace : WordTrace (prefixWord ++ tailWord_7767788) baseStart_7767788 baseEnd_7767788 := by
    simpa [prefixWord, tailWord_7767788, baseEnd_7767788] using wordTrace_append hprefix tailTrace_7767788
  have hstable : (prefixWord ++ tailWord_7767788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767788).length < 2 ^ (prefixWord ++ tailWord_7767788).sum := by decide
  have hdescent : baseEnd_7767788 < baseStart_7767788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767795 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 5]
def baseStart_7767795 : Nat := 118140960795 + 7767795 * 2 ^ 59
def prefixEnd_7767795 : Nat := 4983230072969 + 3 ^ 40 * 7767795 * 2
def baseEnd_7767795 : Nat := 443179162287949022226563

theorem tailTrace_7767795 : CollatzResearch.WordTrace tailWord_7767795 prefixEnd_7767795 443179162287949022226563 := by
  unfold tailWord_7767795
  simp only [CollatzResearch.WordTrace]
  refine ⟨283314758893612823612400839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188876505929075215741600559 283314758893612823612400839)
  ·
    refine ⟨424972138340419235418601259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283314758893612823612400839 424972138340419235418601259)
    ·
      refine ⟨637458207510628853127901889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424972138340419235418601259 637458207510628853127901889)
      ·
        refine ⟨478093655632971639845926417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637458207510628853127901889 478093655632971639845926417)
        ·
          refine ⟨358570241724728729884444813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478093655632971639845926417 358570241724728729884444813)
          ·
            refine ⟨134463840646773273706666805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358570241724728729884444813 134463840646773273706666805)
            ·
              refine ⟨12605985060634994410000013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134463840646773273706666805 12605985060634994410000013)
              ·
                refine ⟨4727244397738122903750005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12605985060634994410000013 4727244397738122903750005)
                ·
                  refine ⟨443179162287949022226563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727244397738122903750005 443179162287949022226563)
                  ·
                    rfl

theorem cell23_7767795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 5].length) (baseStart_7767795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767795 prefixEnd_7767795 := by exact prefixLift 7767795
  have htrace : WordTrace (prefixWord ++ tailWord_7767795) baseStart_7767795 baseEnd_7767795 := by
    simpa [prefixWord, tailWord_7767795, baseEnd_7767795] using wordTrace_append hprefix tailTrace_7767795
  have hstable : (prefixWord ++ tailWord_7767795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767795).length < 2 ^ (prefixWord ++ tailWord_7767795).sum := by decide
  have hdescent : baseEnd_7767795 < baseStart_7767795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767808 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_7767808 : Nat := 118140960795 + 7767808 * 2 ^ 59
def prefixEnd_7767808 : Nat := 4983230072969 + 3 ^ 40 * 7767808 * 2
def baseEnd_7767808 : Nat := 1329539711946683216392169

theorem tailTrace_7767808 : CollatzResearch.WordTrace tailWord_7767808 prefixEnd_7767808 1329539711946683216392169 := by
  unfold tailWord_7767808
  simp only [CollatzResearch.WordTrace]
  refine ⟨141657616521282863416312039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188876822028377151221749385 141657616521282863416312039)
  ·
    refine ⟨212486424781924295124468059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141657616521282863416312039 212486424781924295124468059)
    ·
      refine ⟨318729637172886442686702089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212486424781924295124468059 318729637172886442686702089)
      ·
        refine ⟨239047227879664832015026567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318729637172886442686702089 239047227879664832015026567)
        ·
          refine ⟨358570841819497248022539851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239047227879664832015026567 358570841819497248022539851)
          ·
            refine ⟨537856262729245872033809777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358570841819497248022539851 537856262729245872033809777)
            ·
              refine ⟨403392197046934404025357333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537856262729245872033809777 403392197046934404025357333)
              ·
                refine ⟨18909009236575050188688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403392197046934404025357333 18909009236575050188688625)
                ·
                  refine ⟨14181756927431287641516469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18909009236575050188688625 14181756927431287641516469)
                  ·
                    refine ⟨1329539711946683216392169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14181756927431287641516469 1329539711946683216392169)
                    ·
                      rfl

theorem cell23_7767808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_7767808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767808 prefixEnd_7767808 := by exact prefixLift 7767808
  have htrace : WordTrace (prefixWord ++ tailWord_7767808) baseStart_7767808 baseEnd_7767808 := by
    simpa [prefixWord, tailWord_7767808, baseEnd_7767808] using wordTrace_append hprefix tailTrace_7767808
  have hstable : (prefixWord ++ tailWord_7767808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767808).length < 2 ^ (prefixWord ++ tailWord_7767808).sum := by decide
  have hdescent : baseEnd_7767808 < baseStart_7767808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767818 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7767818 : Nat := 118140960795 + 7767818 * 2 ^ 59
def prefixEnd_7767818 : Nat := 4983230072969 + 3 ^ 40 * 7767818 * 2
def baseEnd_7767818 : Nat := 3988624270646594610051461

theorem tailTrace_7767818 : CollatzResearch.WordTrace tailWord_7767818 prefixEnd_7767818 3988624270646594610051461 := by
  unfold tailWord_7767818
  simp only [CollatzResearch.WordTrace]
  refine ⟨70828899443132374635122027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188877065181686332360325405 70828899443132374635122027)
  ·
    refine ⟨106243349164698561952683041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70828899443132374635122027 106243349164698561952683041)
    ·
      refine ⟨79682511873523921464512281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106243349164698561952683041 79682511873523921464512281)
      ·
        refine ⟨59761883905142941098384211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79682511873523921464512281 59761883905142941098384211)
        ·
          refine ⟨89642825857714411647576317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59761883905142941098384211 89642825857714411647576317)
          ·
            refine ⟨33616059696642904367841119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89642825857714411647576317 33616059696642904367841119)
            ·
              refine ⟨50424089544964356551761679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616059696642904367841119 50424089544964356551761679)
              ·
                refine ⟨75636134317446534827642519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50424089544964356551761679 75636134317446534827642519)
                ·
                  refine ⟨113454201476169802241463779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75636134317446534827642519 113454201476169802241463779)
                  ·
                    refine ⟨170181302214254703362195669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113454201476169802241463779 170181302214254703362195669)
                    ·
                      refine ⟨3988624270646594610051461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170181302214254703362195669 3988624270646594610051461)
                      ·
                        rfl

theorem cell23_7767818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7767818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767818 prefixEnd_7767818 := by exact prefixLift 7767818
  have htrace : WordTrace (prefixWord ++ tailWord_7767818) baseStart_7767818 baseEnd_7767818 := by
    simpa [prefixWord, tailWord_7767818, baseEnd_7767818] using wordTrace_append hprefix tailTrace_7767818
  have hstable : (prefixWord ++ tailWord_7767818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767818).length < 2 ^ (prefixWord ++ tailWord_7767818).sum := by decide
  have hdescent : baseEnd_7767818 < baseStart_7767818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767845 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7767845 : Nat := 118140960795 + 7767845 * 2 ^ 59
def prefixEnd_7767845 : Nat := 4983230072969 + 3 ^ 40 * 7767845 * 2
def baseEnd_7767845 : Nat := 3988638134624266004413837

theorem tailTrace_7767845 : CollatzResearch.WordTrace tailWord_7767845 prefixEnd_7767845 3988638134624266004413837 := by
  unfold tailWord_7767845
  simp only [CollatzResearch.WordTrace]
  refine ⟨283316582543431682151720989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188877721695621121434480659 283316582543431682151720989)
  ·
    refine ⟨106243718453786880806895371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283316582543431682151720989 106243718453786880806895371)
    ·
      refine ⟨159365577680680321210343057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106243718453786880806895371 159365577680680321210343057)
      ·
        refine ⟨119524183260510240907757293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159365577680680321210343057 119524183260510240907757293)
        ·
          refine ⟨44821568722691340340408985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119524183260510240907757293 44821568722691340340408985)
          ·
            refine ⟨33616176542018505255306739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44821568722691340340408985 33616176542018505255306739)
            ·
              refine ⟨50424264813027757882960109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616176542018505255306739 50424264813027757882960109)
              ·
                refine ⟨18909099304885409206110041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50424264813027757882960109 18909099304885409206110041)
                ·
                  refine ⟨14181824478664056904582531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18909099304885409206110041 14181824478664056904582531)
                  ·
                    refine ⟨21272736717996085356873797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14181824478664056904582531 21272736717996085356873797)
                    ·
                      refine ⟨3988638134624266004413837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21272736717996085356873797 3988638134624266004413837)
                      ·
                        rfl

theorem cell23_7767845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7767845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767845 prefixEnd_7767845 := by exact prefixLift 7767845
  have htrace : WordTrace (prefixWord ++ tailWord_7767845) baseStart_7767845 baseEnd_7767845 := by
    simpa [prefixWord, tailWord_7767845, baseEnd_7767845] using wordTrace_append hprefix tailTrace_7767845
  have hstable : (prefixWord ++ tailWord_7767845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767845).length < 2 ^ (prefixWord ++ tailWord_7767845).sum := by decide
  have hdescent : baseEnd_7767845 < baseStart_7767845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767868 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 8]
def baseStart_7767868 : Nat := 118140960795 + 7767868 * 2 ^ 59
def prefixEnd_7767868 : Nat := 4983230072969 + 3 ^ 40 * 7767868 * 2
def baseEnd_7767868 : Nat := 443183327186591046047359

theorem tailTrace_7767868 : CollatzResearch.WordTrace tailWord_7767868 prefixEnd_7767868 443183327186591046047359 := by
  unfold tailWord_7767868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141658710711174178539904129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188878280948232238053205505 141658710711174178539904129)
  ·
    refine ⟨106244033033380633904928097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141658710711174178539904129 106244033033380633904928097)
    ·
      refine ⟨79683024775035475428696073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106244033033380633904928097 79683024775035475428696073)
      ·
        refine ⟨59762268581276606571522055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79683024775035475428696073 59762268581276606571522055)
        ·
          refine ⟨89643402871914909857283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59762268581276606571522055 89643402871914909857283083)
          ·
            refine ⟨134465104307872364785924625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89643402871914909857283083 134465104307872364785924625)
            ·
              refine ⟨100848828230904273589443469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134465104307872364785924625 100848828230904273589443469)
              ·
                refine ⟨37818310586589102596041301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100848828230904273589443469 37818310586589102596041301)
                ·
                  refine ⟨443183327186591046047359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37818310586589102596041301 443183327186591046047359)
                  ·
                    rfl

theorem cell23_7767868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_7767868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767868 prefixEnd_7767868 := by exact prefixLift 7767868
  have htrace : WordTrace (prefixWord ++ tailWord_7767868) baseStart_7767868 baseEnd_7767868 := by
    simpa [prefixWord, tailWord_7767868, baseEnd_7767868] using wordTrace_append hprefix tailTrace_7767868
  have hstable : (prefixWord ++ tailWord_7767868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767868).length < 2 ^ (prefixWord ++ tailWord_7767868).sum := by decide
  have hdescent : baseEnd_7767868 < baseStart_7767868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767906 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7767906 : Nat := 118140960795 + 7767906 * 2 ^ 59
def prefixEnd_7767906 : Nat := 4983230072969 + 3 ^ 40 * 7767906 * 2
def baseEnd_7767906 : Nat := 1329556485648063421917019

theorem tailTrace_7767906 : CollatzResearch.WordTrace tailWord_7767906 prefixEnd_7767906 1329556485648063421917019 := by
  unfold tailWord_7767906
  simp only [CollatzResearch.WordTrace]
  refine ⟨70829701849052672392422893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188879204930807126379794381 70829701849052672392422893)
  ·
    refine ⟨26561138193394752147158585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70829701849052672392422893 26561138193394752147158585)
    ·
      refine ⟨19920853645046064110368939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26561138193394752147158585 19920853645046064110368939)
      ·
        refine ⟨29881280467569096165553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19920853645046064110368939 29881280467569096165553409)
        ·
          refine ⟨22410960350676822124165057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29881280467569096165553409 22410960350676822124165057)
          ·
            refine ⟨16808220263007616593123793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22410960350676822124165057 16808220263007616593123793)
            ·
              refine ⟨12606165197255712444842845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808220263007616593123793 12606165197255712444842845)
              ·
                refine ⟨4727311948970892166816067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606165197255712444842845 4727311948970892166816067)
                ·
                  refine ⟨7090967923456338250224101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727311948970892166816067 7090967923456338250224101)
                  ·
                    refine ⟨1329556485648063421917019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7090967923456338250224101 1329556485648063421917019)
                    ·
                      rfl

theorem cell23_7767906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7767906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767906 prefixEnd_7767906 := by exact prefixLift 7767906
  have htrace : WordTrace (prefixWord ++ tailWord_7767906) baseStart_7767906 baseEnd_7767906 := by
    simpa [prefixWord, tailWord_7767906, baseEnd_7767906] using wordTrace_append hprefix tailTrace_7767906
  have hstable : (prefixWord ++ tailWord_7767906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767906).length < 2 ^ (prefixWord ++ tailWord_7767906).sum := by decide
  have hdescent : baseEnd_7767906 < baseStart_7767906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767912 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7767912 : Nat := 118140960795 + 7767912 * 2 ^ 59
def prefixEnd_7767912 : Nat := 4983230072969 + 3 ^ 40 * 7767912 * 2
def baseEnd_7767912 : Nat := 3988672537828117242276029

theorem tailTrace_7767912 : CollatzResearch.WordTrace tailWord_7767912 prefixEnd_7767912 3988672537828117242276029 := by
  unfold tailWord_7767912
  simp only [CollatzResearch.WordTrace]
  refine ⟨141659513117094476297204995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188879350822792635062939993 141659513117094476297204995)
  ·
    refine ⟨212489269675641714445807493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141659513117094476297204995 212489269675641714445807493)
    ·
      refine ⟨39841738064182821458588905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212489269675641714445807493 39841738064182821458588905)
      ·
        refine ⟨29881303548137116093941679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39841738064182821458588905 29881303548137116093941679)
        ·
          refine ⟨44821955322205674140912519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29881303548137116093941679 44821955322205674140912519)
          ·
            refine ⟨67232932983308511211368779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44821955322205674140912519 67232932983308511211368779)
            ·
              refine ⟨100849399474962766817053169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67232932983308511211368779 100849399474962766817053169)
              ·
                refine ⟨75637049606222075112789877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100849399474962766817053169 75637049606222075112789877)
                ·
                  refine ⟨7090973400583319541824051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75637049606222075112789877 7090973400583319541824051)
                  ·
                    refine ⟨10636460100874979312736077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090973400583319541824051 10636460100874979312736077)
                    ·
                      refine ⟨3988672537828117242276029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636460100874979312736077 3988672537828117242276029)
                      ·
                        rfl

theorem cell23_7767912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7767912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767912 prefixEnd_7767912 := by exact prefixLift 7767912
  have htrace : WordTrace (prefixWord ++ tailWord_7767912) baseStart_7767912 baseEnd_7767912 := by
    simpa [prefixWord, tailWord_7767912, baseEnd_7767912] using wordTrace_append hprefix tailTrace_7767912
  have hstable : (prefixWord ++ tailWord_7767912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767912).length < 2 ^ (prefixWord ++ tailWord_7767912).sum := by decide
  have hdescent : baseEnd_7767912 < baseStart_7767912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_7767922 : Nat := 118140960795 + 7767922 * 2 ^ 59
def prefixEnd_7767922 : Nat := 4983230072969 + 3 ^ 40 * 7767922 * 2
def baseEnd_7767922 : Nat := 3988677672634662203150983

theorem tailTrace_7767922 : CollatzResearch.WordTrace tailWord_7767922 prefixEnd_7767922 3988677672634662203150983 := by
  unfold tailWord_7767922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70829847741038181075568505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188879593976101816201516013 70829847741038181075568505)
  ·
    refine ⟨53122385805778635806676379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70829847741038181075568505 53122385805778635806676379)
    ·
      refine ⟨79683578708667953710014569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122385805778635806676379 79683578708667953710014569)
      ·
        refine ⟨59762684031500965282510927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79683578708667953710014569 59762684031500965282510927)
        ·
          refine ⟨89644026047251447923766391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59762684031500965282510927 89644026047251447923766391)
          ·
            refine ⟨134466039070877171885649587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89644026047251447923766391 134466039070877171885649587)
            ·
              refine ⟨201699058606315757828474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134466039070877171885649587 201699058606315757828474381)
              ·
                refine ⟨75637146977368409185677893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201699058606315757828474381 75637146977368409185677893)
                ·
                  refine ⟨14181965058256576722314605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75637146977368409185677893 14181965058256576722314605)
                  ·
                    refine ⟨5318236896846216270867977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14181965058256576722314605 5318236896846216270867977)
                    ·
                      refine ⟨3988677672634662203150983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318236896846216270867977 3988677672634662203150983)
                      ·
                        rfl

theorem cell23_7767922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_7767922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767922 prefixEnd_7767922 := by exact prefixLift 7767922
  have htrace : WordTrace (prefixWord ++ tailWord_7767922) baseStart_7767922 baseEnd_7767922 := by
    simpa [prefixWord, tailWord_7767922, baseEnd_7767922] using wordTrace_append hprefix tailTrace_7767922
  have hstable : (prefixWord ++ tailWord_7767922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767922).length < 2 ^ (prefixWord ++ tailWord_7767922).sum := by decide
  have hdescent : baseEnd_7767922 < baseStart_7767922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767929 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 1, 1, 3]
def baseStart_7767929 : Nat := 118140960795 + 7767929 * 2 ^ 59
def prefixEnd_7767929 : Nat := 4983230072969 + 3 ^ 40 * 7767929 * 2
def baseEnd_7767929 : Nat := 3988681266999243675763451

theorem tailTrace_7767929 : CollatzResearch.WordTrace tailWord_7767929 prefixEnd_7767929 3988681266999243675763451 := by
  unfold tailWord_7767929
  simp only [CollatzResearch.WordTrace]
  refine ⟨283319646275127364497778841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188879764183418242998519227 283319646275127364497778841)
  ·
    refine ⟨212489734706345523373334131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283319646275127364497778841 212489734706345523373334131)
    ·
      refine ⟨318734602059518285060001197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212489734706345523373334131 318734602059518285060001197)
      ·
        refine ⟨119525475772319356897500449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318734602059518285060001197 119525475772319356897500449)
        ·
          refine ⟨89644106829239517673125337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119525475772319356897500449 89644106829239517673125337)
          ·
            refine ⟨67233080121929638254844003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89644106829239517673125337 67233080121929638254844003)
            ·
              refine ⟨100849620182894457382266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67233080121929638254844003 100849620182894457382266005)
              ·
                refine ⟨4727325946073177689793719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100849620182894457382266005 4727325946073177689793719)
                ·
                  refine ⟨7090988919109766534690579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727325946073177689793719 7090988919109766534690579)
                  ·
                    refine ⟨10636483378664649802035869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7090988919109766534690579 10636483378664649802035869)
                    ·
                      refine ⟨3988681266999243675763451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636483378664649802035869 3988681266999243675763451)
                      ·
                        rfl

theorem cell23_7767929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_7767929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767929 prefixEnd_7767929 := by exact prefixLift 7767929
  have htrace : WordTrace (prefixWord ++ tailWord_7767929) baseStart_7767929 baseEnd_7767929 := by
    simpa [prefixWord, tailWord_7767929, baseEnd_7767929] using wordTrace_append hprefix tailTrace_7767929
  have hstable : (prefixWord ++ tailWord_7767929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767929).length < 2 ^ (prefixWord ++ tailWord_7767929).sum := by decide
  have hdescent : baseEnd_7767929 < baseStart_7767929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767955 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3]
def baseStart_7767955 : Nat := 118140960795 + 7767955 * 2 ^ 59
def prefixEnd_7767955 : Nat := 4983230072969 + 3 ^ 40 * 7767955 * 2
def baseEnd_7767955 : Nat := 3988694617496260574038331

theorem tailTrace_7767955 : CollatzResearch.WordTrace tailWord_7767955 prefixEnd_7767955 3988694617496260574038331 := by
  unfold tailWord_7767955
  simp only [CollatzResearch.WordTrace]
  refine ⟨283320594573033170938225319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188880396382022113958816879 283320594573033170938225319)
  ·
    refine ⟨424980891859549756407337979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283320594573033170938225319 424980891859549756407337979)
    ·
      refine ⟨637471337789324634611006969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424980891859549756407337979 637471337789324634611006969)
      ·
        refine ⟨478103503341993475958255227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637471337789324634611006969 478103503341993475958255227)
        ·
          refine ⟨717155255012990213937382841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478103503341993475958255227 717155255012990213937382841)
          ·
            refine ⟨537866441259742660453037131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717155255012990213937382841 537866441259742660453037131)
            ·
              refine ⟨806799661889613990679555697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537866441259742660453037131 806799661889613990679555697)
              ·
                refine ⟨605099746417210493009666773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806799661889613990679555697 605099746417210493009666773)
                ·
                  refine ⟨14182025306653370929914065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 605099746417210493009666773 14182025306653370929914065)
                  ·
                    refine ⟨10636518979990028197435549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14182025306653370929914065 10636518979990028197435549)
                    ·
                      refine ⟨3988694617496260574038331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636518979990028197435549 3988694617496260574038331)
                      ·
                        rfl

theorem cell23_7767955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_7767955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767955 prefixEnd_7767955 := by exact prefixLift 7767955
  have htrace : WordTrace (prefixWord ++ tailWord_7767955) baseStart_7767955 baseEnd_7767955 := by
    simpa [prefixWord, tailWord_7767955, baseEnd_7767955] using wordTrace_append hprefix tailTrace_7767955
  have hstable : (prefixWord ++ tailWord_7767955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767955).length < 2 ^ (prefixWord ++ tailWord_7767955).sum := by decide
  have hdescent : baseEnd_7767955 < baseStart_7767955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767962 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_7767962 : Nat := 118140960795 + 7767962 * 2 ^ 59
def prefixEnd_7767962 : Nat := 4983230072969 + 3 ^ 40 * 7767962 * 2
def baseEnd_7767962 : Nat := 1329566070620280682216933

theorem tailTrace_7767962 : CollatzResearch.WordTrace tailWord_7767962 prefixEnd_7767962 1329566070620280682216933 := by
  unfold tailWord_7767962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70830212471001952783432535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188880566589338540755820093 70830212471001952783432535)
  ·
    refine ⟨106245318706502929175148803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70830212471001952783432535 106245318706502929175148803)
    ·
      refine ⟨159367978059754393762723205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106245318706502929175148803 159367978059754393762723205)
      ·
        refine ⟨29881495886203948830510601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159367978059754393762723205 29881495886203948830510601)
        ·
          refine ⟨22411121914652961622882951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29881495886203948830510601 22411121914652961622882951)
          ·
            refine ⟨33616682871979442434324427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411121914652961622882951 33616682871979442434324427)
            ·
              refine ⟨50425024307969163651486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616682871979442434324427 50425024307969163651486641)
              ·
                refine ⟨37818768230976872738614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50425024307969163651486641 37818768230976872738614981)
                ·
                  refine ⟨7091019043308163638490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37818768230976872738614981 7091019043308163638490309)
                  ·
                    refine ⟨1329566070620280682216933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091019043308163638490309 1329566070620280682216933)
                    ·
                      rfl

theorem cell23_7767962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_7767962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767962 prefixEnd_7767962 := by exact prefixLift 7767962
  have htrace : WordTrace (prefixWord ++ tailWord_7767962) baseStart_7767962 baseEnd_7767962 := by
    simpa [prefixWord, tailWord_7767962, baseEnd_7767962] using wordTrace_append hprefix tailTrace_7767962
  have hstable : (prefixWord ++ tailWord_7767962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767962).length < 2 ^ (prefixWord ++ tailWord_7767962).sum := by decide
  have hdescent : baseEnd_7767962 < baseStart_7767962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767972 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_7767972 : Nat := 118140960795 + 7767972 * 2 ^ 59
def prefixEnd_7767972 : Nat := 4983230072969 + 3 ^ 40 * 7767972 * 2
def baseEnd_7767972 : Nat := 3988703346667387007525753

theorem tailTrace_7767972 : CollatzResearch.WordTrace tailWord_7767972 prefixEnd_7767972 3988703346667387007525753 := by
  unfold tailWord_7767972
  simp only [CollatzResearch.WordTrace]
  refine ⟨141660607306985791420797085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188880809742647721894396113 141660607306985791420797085)
  ·
    refine ⟨53122727740119671782798907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141660607306985791420797085 53122727740119671782798907)
    ·
      refine ⟨79684091610179507674198361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122727740119671782798907 79684091610179507674198361)
      ·
        refine ⟨59763068707634630755648771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79684091610179507674198361 59763068707634630755648771)
        ·
          refine ⟨89644603061451946133473157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59763068707634630755648771 89644603061451946133473157)
          ·
            refine ⟨16808363074022239900026217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89644603061451946133473157 16808363074022239900026217)
            ·
              refine ⟨12606272305516679925019663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808363074022239900026217 12606272305516679925019663)
              ·
                refine ⟨18909408458275019887529495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12606272305516679925019663 18909408458275019887529495)
                ·
                  refine ⟨28364112687412529831294243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18909408458275019887529495 28364112687412529831294243)
                  ·
                    refine ⟨42546169031118794746941365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28364112687412529831294243 42546169031118794746941365)
                    ·
                      refine ⟨3988703346667387007525753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42546169031118794746941365 3988703346667387007525753)
                      ·
                        rfl

theorem cell23_7767972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_7767972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767972 prefixEnd_7767972 := by exact prefixLift 7767972
  have htrace : WordTrace (prefixWord ++ tailWord_7767972) baseStart_7767972 baseEnd_7767972 := by
    simpa [prefixWord, tailWord_7767972, baseEnd_7767972] using wordTrace_append hprefix tailTrace_7767972
  have hstable : (prefixWord ++ tailWord_7767972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767972).length < 2 ^ (prefixWord ++ tailWord_7767972).sum := by decide
  have hdescent : baseEnd_7767972 < baseStart_7767972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767975 : List Nat := [1, 1, 6, 1, 2, 1, 11]
def baseStart_7767975 : Nat := 118140960795 + 7767975 * 2 ^ 59
def prefixEnd_7767975 : Nat := 4983230072969 + 3 ^ 40 * 7767975 * 2
def baseEnd_7767975 : Nat := 49243270211226549330719

theorem tailTrace_7767975 : CollatzResearch.WordTrace tailWord_7767975 prefixEnd_7767975 49243270211226549330719 := by
  unfold tailWord_7767975
  simp only [CollatzResearch.WordTrace]
  refine ⟨283321324032960714353953379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188880882688640476235968919 283321324032960714353953379)
  ·
    refine ⟨424981986049441071530930069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283321324032960714353953379 424981986049441071530930069)
    ·
      refine ⟨19921030596067550228012347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424981986049441071530930069 19921030596067550228012347)
      ·
        refine ⟨29881545894101325342018521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921030596067550228012347 29881545894101325342018521)
        ·
          refine ⟨22411159420575994006513891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29881545894101325342018521 22411159420575994006513891)
          ·
            refine ⟨33616739130863991009770837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411159420575994006513891 33616739130863991009770837)
            ·
              refine ⟨49243270211226549330719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33616739130863991009770837 49243270211226549330719)
              ·
                rfl

theorem cell23_7767975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 11].length) (baseStart_7767975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767975 prefixEnd_7767975 := by exact prefixLift 7767975
  have htrace : WordTrace (prefixWord ++ tailWord_7767975) baseStart_7767975 baseEnd_7767975 := by
    simpa [prefixWord, tailWord_7767975, baseEnd_7767975] using wordTrace_append hprefix tailTrace_7767975
  have hstable : (prefixWord ++ tailWord_7767975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767975).length < 2 ^ (prefixWord ++ tailWord_7767975).sum := by decide
  have hdescent : baseEnd_7767975 < baseStart_7767975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767986 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_7767986 : Nat := 118140960795 + 7767986 * 2 ^ 59
def prefixEnd_7767986 : Nat := 4983230072969 + 3 ^ 40 * 7767986 * 2
def baseEnd_7767986 : Nat := 3988710535396549952750689

theorem tailTrace_7767986 : CollatzResearch.WordTrace tailWord_7767986 prefixEnd_7767986 3988710535396549952750689 := by
  unfold tailWord_7767986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70830431308980215808150953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188881150157280575488402541 70830431308980215808150953)
  ·
    refine ⟨53122823481735161856113215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70830431308980215808150953 53122823481735161856113215)
    ·
      refine ⟨79684235222602742784169823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53122823481735161856113215 79684235222602742784169823)
      ·
        refine ⟨119526352833904114176254735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79684235222602742784169823 119526352833904114176254735)
        ·
          refine ⟨179289529250856171264382103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119526352833904114176254735 179289529250856171264382103)
          ·
            refine ⟨268934293876284256896573155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179289529250856171264382103 268934293876284256896573155)
            ·
              refine ⟨403401440814426385344859733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268934293876284256896573155 403401440814426385344859733)
              ·
                refine ⟨4727360634544059203260075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 403401440814426385344859733 4727360634544059203260075)
                ·
                  refine ⟨7091040951816088804890113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727360634544059203260075 7091040951816088804890113)
                  ·
                    refine ⟨5318280713862066603667585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091040951816088804890113 5318280713862066603667585)
                    ·
                      refine ⟨3988710535396549952750689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318280713862066603667585 3988710535396549952750689)
                      ·
                        rfl

theorem cell23_7767986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_7767986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767986 prefixEnd_7767986 := by exact prefixLift 7767986
  have htrace : WordTrace (prefixWord ++ tailWord_7767986) baseStart_7767986 baseEnd_7767986 := by
    simpa [prefixWord, tailWord_7767986, baseEnd_7767986] using wordTrace_append hprefix tailTrace_7767986
  have hstable : (prefixWord ++ tailWord_7767986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767986).length < 2 ^ (prefixWord ++ tailWord_7767986).sum := by decide
  have hdescent : baseEnd_7767986 < baseStart_7767986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7767996 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_7767996 : Nat := 118140960795 + 7767996 * 2 ^ 59
def prefixEnd_7767996 : Nat := 4983230072969 + 3 ^ 40 * 7767996 * 2
def baseEnd_7767996 : Nat := 1329571890067698304541881

theorem tailTrace_7767996 : CollatzResearch.WordTrace tailWord_7767996 prefixEnd_7767996 1329571890067698304541881 := by
  unfold tailWord_7767996
  simp only [CollatzResearch.WordTrace]
  refine ⟨141661044982942317470233921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188881393310589756626978561 141661044982942317470233921)
  ·
    refine ⟨106245783737206738102675441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141661044982942317470233921 106245783737206738102675441)
    ·
      refine ⟨79684337802905053577006581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106245783737206738102675441 79684337802905053577006581)
      ·
        refine ⟨7470406669022348772844367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79684337802905053577006581 7470406669022348772844367)
        ·
          refine ⟨11205610003533523159266551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470406669022348772844367 11205610003533523159266551)
          ·
            refine ⟨16808415005300284738899827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205610003533523159266551 16808415005300284738899827)
            ·
              refine ⟨25212622507950427108349741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16808415005300284738899827 25212622507950427108349741)
              ·
                refine ⟨9454733440481410165631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25212622507950427108349741 9454733440481410165631153)
                ·
                  refine ⟨7091050080361057624223365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454733440481410165631153 7091050080361057624223365)
                  ·
                    refine ⟨1329571890067698304541881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091050080361057624223365 1329571890067698304541881)
                    ·
                      rfl

theorem cell23_7767996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_7767996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7767996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7767996 prefixEnd_7767996 := by exact prefixLift 7767996
  have htrace : WordTrace (prefixWord ++ tailWord_7767996) baseStart_7767996 baseEnd_7767996 := by
    simpa [prefixWord, tailWord_7767996, baseEnd_7767996] using wordTrace_append hprefix tailTrace_7767996
  have hstable : (prefixWord ++ tailWord_7767996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7767996).length < 2 ^ (prefixWord ++ tailWord_7767996).sum := by decide
  have hdescent : baseEnd_7767996 < baseStart_7767996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7767996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768093 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7768093 : Nat := 118140960795 + 7768093 * 2 ^ 59
def prefixEnd_7768093 : Nat := 4983230072969 + 3 ^ 40 * 7768093 * 2
def baseEnd_7768093 : Nat := 3988765477826581034112697

theorem tailTrace_7768093 : CollatzResearch.WordTrace tailWord_7768093 prefixEnd_7768093 3988765477826581034112697 := by
  unfold tailWord_7768093
  simp only [CollatzResearch.WordTrace]
  refine ⟨283325627846533220506748933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188883751897688813671165955 283325627846533220506748933)
  ·
    refine ⟨53123555221224978845015425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283325627846533220506748933 53123555221224978845015425)
    ·
      refine ⟨39842666415918734133761569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53123555221224978845015425 39842666415918734133761569)
      ·
        refine ⟨29881999811939050600321177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39842666415918734133761569 29881999811939050600321177)
        ·
          refine ⟨22411499858954287950240883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29881999811939050600321177 22411499858954287950240883)
          ·
            refine ⟨33617249788431431925361325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411499858954287950240883 33617249788431431925361325)
            ·
              refine ⟨12606468670661786972010497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33617249788431431925361325 12606468670661786972010497)
              ·
                refine ⟨9454851502996340229007873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12606468670661786972010497 9454851502996340229007873)
                ·
                  refine ⟨7091138627247255171755905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454851502996340229007873 7091138627247255171755905)
                  ·
                    refine ⟨5318353970435441378816929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091138627247255171755905 5318353970435441378816929)
                    ·
                      refine ⟨3988765477826581034112697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318353970435441378816929 3988765477826581034112697)
                      ·
                        rfl

theorem cell23_7768093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7768093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768093 prefixEnd_7768093 := by exact prefixLift 7768093
  have htrace : WordTrace (prefixWord ++ tailWord_7768093) baseStart_7768093 baseEnd_7768093 := by
    simpa [prefixWord, tailWord_7768093, baseEnd_7768093] using wordTrace_append hprefix tailTrace_7768093
  have hstable : (prefixWord ++ tailWord_7768093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768093).length < 2 ^ (prefixWord ++ tailWord_7768093).sum := by decide
  have hdescent : baseEnd_7768093 < baseStart_7768093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_7768105 : Nat := 118140960795 + 7768105 * 2 ^ 59
def prefixEnd_7768105 : Nat := 4983230072969 + 3 ^ 40 * 7768105 * 2
def baseEnd_7768105 : Nat := 3988771639594434987162641

theorem tailTrace_7768105 : CollatzResearch.WordTrace tailWord_7768105 prefixEnd_7768105 3988771639594434987162641 := by
  unfold tailWord_7768105
  simp only [CollatzResearch.WordTrace]
  refine ⟨283326065522489746556185769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188884043681659831037457179 283326065522489746556185769)
  ·
    refine ⟨212494549141867309917139327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283326065522489746556185769 212494549141867309917139327)
    ·
      refine ⟨318741823712800964875708991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212494549141867309917139327 318741823712800964875708991)
      ·
        refine ⟨478112735569201447313563487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318741823712800964875708991 478112735569201447313563487)
        ·
          refine ⟨717169103353802170970345231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478112735569201447313563487 717169103353802170970345231)
          ·
            refine ⟨1075753655030703256455517847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717169103353802170970345231 1075753655030703256455517847)
            ·
              refine ⟨1613630482546054884683276771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075753655030703256455517847 1613630482546054884683276771)
              ·
                refine ⟨2420445723819082327024915157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613630482546054884683276771 2420445723819082327024915157)
                ·
                  refine ⟨56729196652009742039646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2420445723819082327024915157 56729196652009742039646449)
                  ·
                    refine ⟨42546897489007306529734837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56729196652009742039646449 42546897489007306529734837)
                    ·
                      refine ⟨3988771639594434987162641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42546897489007306529734837 3988771639594434987162641)
                      ·
                        rfl

theorem cell23_7768105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_7768105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768105 prefixEnd_7768105 := by exact prefixLift 7768105
  have htrace : WordTrace (prefixWord ++ tailWord_7768105) baseStart_7768105 baseEnd_7768105 := by
    simpa [prefixWord, tailWord_7768105, baseEnd_7768105] using wordTrace_append hprefix tailTrace_7768105
  have hstable : (prefixWord ++ tailWord_7768105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768105).length < 2 ^ (prefixWord ++ tailWord_7768105).sum := by decide
  have hdescent : baseEnd_7768105 < baseStart_7768105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768110 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7768110 : Nat := 118140960795 + 7768110 * 2 ^ 59
def prefixEnd_7768110 : Nat := 4983230072969 + 3 ^ 40 * 7768110 * 2
def baseEnd_7768110 : Nat := 3988774206997707467600119

theorem tailTrace_7768110 : CollatzResearch.WordTrace tailWord_7768110 prefixEnd_7768110 3988774206997707467600119 := by
  unfold tailWord_7768110
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415780985933954051264723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188884165258314421606745189 35415780985933954051264723)
  ·
    refine ⟨53123671478900931076897085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35415780985933954051264723 53123671478900931076897085)
    ·
      refine ⟨19921376804587849153836407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53123671478900931076897085 19921376804587849153836407)
      ·
        refine ⟨29882065206881773730754611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921376804587849153836407 29882065206881773730754611)
        ·
          refine ⟨44823097810322660596131917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29882065206881773730754611 44823097810322660596131917)
          ·
            refine ⟨16808661678870997723549469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44823097810322660596131917 16808661678870997723549469)
            ·
              refine ⟨6303248129576624146331051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16808661678870997723549469 6303248129576624146331051)
              ·
                refine ⟨9454872194364936219496577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303248129576624146331051 9454872194364936219496577)
                ·
                  refine ⟨7091154145773702164622433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9454872194364936219496577 7091154145773702164622433)
                  ·
                    refine ⟨5318365609330276623466825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091154145773702164622433 5318365609330276623466825)
                    ·
                      refine ⟨3988774206997707467600119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318365609330276623466825 3988774206997707467600119)
                      ·
                        rfl

theorem cell23_7768110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7768110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768110 prefixEnd_7768110 := by exact prefixLift 7768110
  have htrace : WordTrace (prefixWord ++ tailWord_7768110) baseStart_7768110 baseEnd_7768110 := by
    simpa [prefixWord, tailWord_7768110, baseEnd_7768110] using wordTrace_append hprefix tailTrace_7768110
  have hstable : (prefixWord ++ tailWord_7768110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768110).length < 2 ^ (prefixWord ++ tailWord_7768110).sum := by decide
  have hdescent : baseEnd_7768110 < baseStart_7768110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768149 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7768149 : Nat := 118140960795 + 7768149 * 2 ^ 59
def prefixEnd_7768149 : Nat := 4983230072969 + 3 ^ 40 * 7768149 * 2
def baseEnd_7768149 : Nat := 3988794232743232815012439

theorem tailTrace_7768149 : CollatzResearch.WordTrace tailWord_7768149 prefixEnd_7768149 3988794232743232815012439 := by
  unfold tailWord_7768149
  simp only [CollatzResearch.WordTrace]
  refine ⟨283327670334330342070787501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188885113556220228047191667 283327670334330342070787501)
  ·
    refine ⟨106247876375373878276545313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283327670334330342070787501 106247876375373878276545313)
    ·
      refine ⟨79685907281530408707408985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106247876375373878276545313 79685907281530408707408985)
      ·
        refine ⟨59764430461147806530556739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79685907281530408707408985 59764430461147806530556739)
        ·
          refine ⟨89646645691721709795835109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59764430461147806530556739 89646645691721709795835109)
          ·
            refine ⟨16808746067197820586719083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89646645691721709795835109 16808746067197820586719083)
            ·
              refine ⟨25213119100796730880078625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16808746067197820586719083 25213119100796730880078625)
              ·
                refine ⟨18909839325597548160058969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25213119100796730880078625 18909839325597548160058969)
                ·
                  refine ⟨14182379494198161120044227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18909839325597548160058969 14182379494198161120044227)
                  ·
                    refine ⟨21273569241297241680066341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14182379494198161120044227 21273569241297241680066341)
                    ·
                      refine ⟨3988794232743232815012439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21273569241297241680066341 3988794232743232815012439)
                      ·
                        rfl

theorem cell23_7768149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7768149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768149 prefixEnd_7768149 := by exact prefixLift 7768149
  have htrace : WordTrace (prefixWord ++ tailWord_7768149) baseStart_7768149 baseEnd_7768149 := by
    simpa [prefixWord, tailWord_7768149, baseEnd_7768149] using wordTrace_append hprefix tailTrace_7768149
  have hstable : (prefixWord ++ tailWord_7768149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768149).length < 2 ^ (prefixWord ++ tailWord_7768149).sum := by decide
  have hdescent : baseEnd_7768149 < baseStart_7768149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768150 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_7768150 : Nat := 118140960795 + 7768150 * 2 ^ 59
def prefixEnd_7768150 : Nat := 4983230072969 + 3 ^ 40 * 7768150 * 2
def baseEnd_7768150 : Nat := 443199416247098590122215

theorem tailTrace_7768150 : CollatzResearch.WordTrace tailWord_7768150 prefixEnd_7768150 443199416247098590122215 := by
  unfold tailWord_7768150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707981675457919952598369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188885137871551146161049269 17707981675457919952598369)
  ·
    refine ⟨13280986256593439964448777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17707981675457919952598369 13280986256593439964448777)
    ·
      refine ⟨9960739692445079973336583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13280986256593439964448777 9960739692445079973336583)
      ·
        refine ⟨14941109538667619960004875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960739692445079973336583 14941109538667619960004875)
        ·
          refine ⟨22411664308001429940007313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14941109538667619960004875 22411664308001429940007313)
          ·
            refine ⟨16808748231001072455005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22411664308001429940007313 16808748231001072455005485)
            ·
              refine ⟨6303280586625402170627057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16808748231001072455005485 6303280586625402170627057)
              ·
                refine ⟨4727460439969051627970293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303280586625402170627057 4727460439969051627970293)
                ·
                  refine ⟨443199416247098590122215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727460439969051627970293 443199416247098590122215)
                  ·
                    rfl

theorem cell23_7768150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_7768150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768150 prefixEnd_7768150 := by exact prefixLift 7768150
  have htrace : WordTrace (prefixWord ++ tailWord_7768150) baseStart_7768150 baseEnd_7768150 := by
    simpa [prefixWord, tailWord_7768150, baseEnd_7768150] using wordTrace_append hprefix tailTrace_7768150
  have hstable : (prefixWord ++ tailWord_7768150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768150).length < 2 ^ (prefixWord ++ tailWord_7768150).sum := by decide
  have hdescent : baseEnd_7768150 < baseStart_7768150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768206 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_7768206 : Nat := 118140960795 + 7768206 * 2 ^ 59
def prefixEnd_7768206 : Nat := 4983230072969 + 3 ^ 40 * 7768206 * 2
def baseEnd_7768206 : Nat := 443202611237837676888853

theorem tailTrace_7768206 : CollatzResearch.WordTrace tailWord_7768206 prefixEnd_7768206 443202611237837676888853 := by
  unfold tailWord_7768206
  simp only [CollatzResearch.WordTrace]
  refine ⟨35416218661890480100701559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188886499530082560537074981 35416218661890480100701559)
  ·
    refine ⟨53124327992835720151052339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35416218661890480100701559 53124327992835720151052339)
    ·
      refine ⟨79686491989253580226578509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53124327992835720151052339 79686491989253580226578509)
      ·
        refine ⟨29882434495970092584966941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79686491989253580226578509 29882434495970092584966941)
        ·
          refine ⟨11205912935988784719362603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29882434495970092584966941 11205912935988784719362603)
          ·
            refine ⟨16808869403983177079043905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205912935988784719362603 16808869403983177079043905)
            ·
              refine ⟨12606652052987382809282929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808869403983177079043905 12606652052987382809282929)
              ·
                refine ⟨9454989039740537106962197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12606652052987382809282929 9454989039740537106962197)
                ·
                  refine ⟨443202611237837676888853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9454989039740537106962197 443202611237837676888853)
                  ·
                    rfl

theorem cell23_7768206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_7768206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768206 prefixEnd_7768206 := by exact prefixLift 7768206
  have htrace : WordTrace (prefixWord ++ tailWord_7768206) baseStart_7768206 baseEnd_7768206 := by
    simpa [prefixWord, tailWord_7768206, baseEnd_7768206] using wordTrace_append hprefix tailTrace_7768206
  have hstable : (prefixWord ++ tailWord_7768206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768206).length < 2 ^ (prefixWord ++ tailWord_7768206).sum := by decide
  have hdescent : baseEnd_7768206 < baseStart_7768206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_7768239 : Nat := 118140960795 + 7768239 * 2 ^ 59
def prefixEnd_7768239 : Nat := 4983230072969 + 3 ^ 40 * 7768239 * 2
def baseEnd_7768239 : Nat := 3988840446002137462887025

theorem tailTrace_7768239 : CollatzResearch.WordTrace tailWord_7768239 prefixEnd_7768239 3988840446002137462887025 := by
  unfold tailWord_7768239
  simp only [CollatzResearch.WordTrace]
  refine ⟨283330952904004287441563771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188887301936002858294375847 283330952904004287441563771)
  ·
    refine ⟨424996429356006431162345657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283330952904004287441563771 424996429356006431162345657)
    ·
      refine ⟨318747322017004823371759243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424996429356006431162345657 318747322017004823371759243)
      ·
        refine ⟨478120983025507235057638865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318747322017004823371759243 478120983025507235057638865)
        ·
          refine ⟨358590737269130426293229149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478120983025507235057638865 358590737269130426293229149)
          ·
            refine ⟨134471526475923909859960931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358590737269130426293229149 134471526475923909859960931)
            ·
              refine ⟨201707289713885864789941397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134471526475923909859960931 201707289713885864789941397)
              ·
                refine ⟨9455029205338399912028503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201707289713885864789941397 9455029205338399912028503)
                ·
                  refine ⟨14182543808007599868042755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455029205338399912028503 14182543808007599868042755)
                  ·
                    refine ⟨21273815712011399802064133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14182543808007599868042755 21273815712011399802064133)
                    ·
                      refine ⟨3988840446002137462887025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21273815712011399802064133 3988840446002137462887025)
                      ·
                        rfl

theorem cell23_7768239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_7768239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768239 prefixEnd_7768239 := by exact prefixLift 7768239
  have htrace : WordTrace (prefixWord ++ tailWord_7768239) baseStart_7768239 baseEnd_7768239 := by
    simpa [prefixWord, tailWord_7768239, baseEnd_7768239] using wordTrace_append hprefix tailTrace_7768239
  have hstable : (prefixWord ++ tailWord_7768239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768239).length < 2 ^ (prefixWord ++ tailWord_7768239).sum := by decide
  have hdescent : baseEnd_7768239 < baseStart_7768239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768244 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7768244 : Nat := 118140960795 + 7768244 * 2 ^ 59
def prefixEnd_7768244 : Nat := 4983230072969 + 3 ^ 40 * 7768244 * 2
def baseEnd_7768244 : Nat := 1329614337801803314441501

theorem tailTrace_7768244 : CollatzResearch.WordTrace tailWord_7768244 prefixEnd_7768244 1329614337801803314441501 := by
  unfold tailWord_7768244
  simp only [CollatzResearch.WordTrace]
  refine ⟨141665567634493086647747893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188887423512657448863663857 141665567634493086647747893)
  ·
    refine ⟨13281146965733726873226365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141665567634493086647747893 13281146965733726873226365)
    ·
      refine ⟨4980430112150147577459887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13281146965733726873226365 4980430112150147577459887)
      ·
        refine ⟨7470645168225221366189831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980430112150147577459887 7470645168225221366189831)
        ·
          refine ⟨11205967752337832049284747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470645168225221366189831 11205967752337832049284747)
          ·
            refine ⟨16808951628506748073927121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205967752337832049284747 16808951628506748073927121)
            ·
              refine ⟨12606713721380061055445341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16808951628506748073927121 12606713721380061055445341)
              ·
                refine ⟨4727517645517522895792003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12606713721380061055445341 4727517645517522895792003)
                ·
                  refine ⟨7091276468276284343688005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727517645517522895792003 7091276468276284343688005)
                  ·
                    refine ⟨1329614337801803314441501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091276468276284343688005 1329614337801803314441501)
                    ·
                      rfl

theorem cell23_7768244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7768244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768244 prefixEnd_7768244 := by exact prefixLift 7768244
  have htrace : WordTrace (prefixWord ++ tailWord_7768244) baseStart_7768244 baseEnd_7768244 := by
    simpa [prefixWord, tailWord_7768244, baseEnd_7768244] using wordTrace_append hprefix tailTrace_7768244
  have hstable : (prefixWord ++ tailWord_7768244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768244).length < 2 ^ (prefixWord ++ tailWord_7768244).sum := by decide
  have hdescent : baseEnd_7768244 < baseStart_7768244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768249 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_7768249 : Nat := 118140960795 + 7768249 * 2 ^ 59
def prefixEnd_7768249 : Nat := 4983230072969 + 3 ^ 40 * 7768249 * 2
def baseEnd_7768249 : Nat := 1329615193602894141253993

theorem tailTrace_7768249 : CollatzResearch.WordTrace tailWord_7768249 prefixEnd_7768249 1329615193602894141253993 := by
  unfold tailWord_7768249
  simp only [CollatzResearch.WordTrace]
  refine ⟨283331317633968059149427801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188887545089312039432951867 283331317633968059149427801)
  ·
    refine ⟨212498488225476044362070851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283331317633968059149427801 212498488225476044362070851)
    ·
      refine ⟨318747732338214066543106277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212498488225476044362070851 318747732338214066543106277)
      ·
        refine ⟨59765199813415137476832427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318747732338214066543106277 59765199813415137476832427)
        ·
          refine ⟨89647799720122706215248641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59765199813415137476832427 89647799720122706215248641)
          ·
            refine ⟨67235849790092029661436481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89647799720122706215248641 67235849790092029661436481)
            ·
              refine ⟨50426887342569022246077361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67235849790092029661436481 50426887342569022246077361)
              ·
                refine ⟨37820165506926766684558021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50426887342569022246077361 37820165506926766684558021)
                ·
                  refine ⟨7091281032548768753354629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37820165506926766684558021 7091281032548768753354629)
                  ·
                    refine ⟨1329615193602894141253993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091281032548768753354629 1329615193602894141253993)
                    ·
                      rfl

theorem cell23_7768249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_7768249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768249 prefixEnd_7768249 := by exact prefixLift 7768249
  have htrace : WordTrace (prefixWord ++ tailWord_7768249) baseStart_7768249 baseEnd_7768249 := by
    simpa [prefixWord, tailWord_7768249, baseEnd_7768249] using wordTrace_append hprefix tailTrace_7768249
  have hstable : (prefixWord ++ tailWord_7768249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768249).length < 2 ^ (prefixWord ++ tailWord_7768249).sum := by decide
  have hdescent : baseEnd_7768249 < baseStart_7768249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768256 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_7768256 : Nat := 118140960795 + 7768256 * 2 ^ 59
def prefixEnd_7768256 : Nat := 4983230072969 + 3 ^ 40 * 7768256 * 2
def baseEnd_7768256 : Nat := 3988849175173263896374447

theorem tailTrace_7768256 : CollatzResearch.WordTrace tailWord_7768256 prefixEnd_7768256 3988849175173263896374447 := by
  unfold tailWord_7768256
  simp only [CollatzResearch.WordTrace]
  refine ⟨141665786472471349672466311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188887715296628466229955081 141665786472471349672466311)
  ·
    refine ⟨212498679708707024508699467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141665786472471349672466311 212498679708707024508699467)
    ·
      refine ⟨318748019563060536763049201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212498679708707024508699467 318748019563060536763049201)
      ·
        refine ⟨239061014672295402572286901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318748019563060536763049201 239061014672295402572286901)
        ·
          refine ⟨22411970125527693991151897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239061014672295402572286901 22411970125527693991151897)
          ·
            refine ⟨16808977594145770493363923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22411970125527693991151897 16808977594145770493363923)
            ·
              refine ⟨25213466391218655740045885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16808977594145770493363923 25213466391218655740045885)
              ·
                refine ⟨9455049896706995902517207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25213466391218655740045885 9455049896706995902517207)
                ·
                  refine ⟨14182574845060493853775811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455049896706995902517207 14182574845060493853775811)
                  ·
                    refine ⟨21273862267590740780663717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14182574845060493853775811 21273862267590740780663717)
                    ·
                      refine ⟨3988849175173263896374447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21273862267590740780663717 3988849175173263896374447)
                      ·
                        rfl

theorem cell23_7768256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_7768256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768256 prefixEnd_7768256 := by exact prefixLift 7768256
  have htrace : WordTrace (prefixWord ++ tailWord_7768256) baseStart_7768256 baseEnd_7768256 := by
    simpa [prefixWord, tailWord_7768256, baseEnd_7768256] using wordTrace_append hprefix tailTrace_7768256
  have hstable : (prefixWord ++ tailWord_7768256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768256).length < 2 ^ (prefixWord ++ tailWord_7768256).sum := by decide
  have hdescent : baseEnd_7768256 < baseStart_7768256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768293 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7768293 : Nat := 118140960795 + 7768293 * 2 ^ 59
def prefixEnd_7768293 : Nat := 4983230072969 + 3 ^ 40 * 7768293 * 2
def baseEnd_7768293 : Nat := 3988868173957480251611777

theorem tailTrace_7768293 : CollatzResearch.WordTrace tailWord_7768293 prefixEnd_7768293 3988868173957480251611777 := by
  unfold tailWord_7768293
  simp only [CollatzResearch.WordTrace]
  refine ⟨283332922445808654664029533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188888614963872436442686355 283332922445808654664029533)
  ·
    refine ⟨106249845917178245499011075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283332922445808654664029533 106249845917178245499011075)
    ·
      refine ⟨159374768875767368248516613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106249845917178245499011075 159374768875767368248516613)
      ·
        refine ⟨29882769164206381546596865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159374768875767368248516613 29882769164206381546596865)
        ·
          refine ⟨22412076873154786159947649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29882769164206381546596865 22412076873154786159947649)
          ·
            refine ⟨16809057654866089619960737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412076873154786159947649 16809057654866089619960737)
            ·
              refine ⟨12606793241149567214970553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809057654866089619960737 12606793241149567214970553)
              ·
                refine ⟨9455094930862175411227915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12606793241149567214970553 9455094930862175411227915)
                ·
                  refine ⟨14182642396293263116841873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455094930862175411227915 14182642396293263116841873)
                  ·
                    refine ⟨10636981797219947337631405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14182642396293263116841873 10636981797219947337631405)
                    ·
                      refine ⟨3988868173957480251611777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10636981797219947337631405 3988868173957480251611777)
                      ·
                        rfl

theorem cell23_7768293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7768293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768293 prefixEnd_7768293 := by exact prefixLift 7768293
  have htrace : WordTrace (prefixWord ++ tailWord_7768293) baseStart_7768293 baseEnd_7768293 := by
    simpa [prefixWord, tailWord_7768293, baseEnd_7768293] using wordTrace_append hprefix tailTrace_7768293
  have hstable : (prefixWord ++ tailWord_7768293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768293).length < 2 ^ (prefixWord ++ tailWord_7768293).sum := by decide
  have hdescent : baseEnd_7768293 < baseStart_7768293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768296 : List Nat := [2, 1, 4, 1, 2, 4, 2, 7]
def baseStart_7768296 : Nat := 118140960795 + 7768296 * 2 ^ 59
def prefixEnd_7768296 : Nat := 4983230072969 + 3 ^ 40 * 7768296 * 2
def baseEnd_7768296 : Nat := 147735915348127545921269

theorem tailTrace_7768296 : CollatzResearch.WordTrace tailWord_7768296 prefixEnd_7768296 147735915348127545921269 := by
  unfold tailWord_7768296
  simp only [CollatzResearch.WordTrace]
  refine ⟨141666515932398893088194371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188888687909865190784259161 141666515932398893088194371)
  ·
    refine ⟨212499773898598339632291557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141666515932398893088194371 212499773898598339632291557)
    ·
      refine ⟨39843707605987188681054667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212499773898598339632291557 39843707605987188681054667)
      ·
        refine ⟨59765561408980783021582001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39843707605987188681054667 59765561408980783021582001)
        ·
          refine ⟨44824171056735587266186501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59765561408980783021582001 44824171056735587266186501)
          ·
            refine ⟨8404532073137922612409969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44824171056735587266186501 8404532073137922612409969)
            ·
              refine ⟨6303399054853441959307477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404532073137922612409969 6303399054853441959307477)
              ·
                refine ⟨147735915348127545921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6303399054853441959307477 147735915348127545921269)
                ·
                  rfl

theorem cell23_7768296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 7].length) (baseStart_7768296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768296 prefixEnd_7768296 := by exact prefixLift 7768296
  have htrace : WordTrace (prefixWord ++ tailWord_7768296) baseStart_7768296 baseEnd_7768296 := by
    simpa [prefixWord, tailWord_7768296, baseEnd_7768296] using wordTrace_append hprefix tailTrace_7768296
  have hstable : (prefixWord ++ tailWord_7768296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768296).length < 2 ^ (prefixWord ++ tailWord_7768296).sum := by decide
  have hdescent : baseEnd_7768296 < baseStart_7768296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768312 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_7768312 : Nat := 118140960795 + 7768312 * 2 ^ 59
def prefixEnd_7768312 : Nat := 4983230072969 + 3 ^ 40 * 7768312 * 2
def baseEnd_7768312 : Nat := 3988877930089915677274189

theorem tailTrace_7768312 : CollatzResearch.WordTrace tailWord_7768312 prefixEnd_7768312 3988877930089915677274189 := by
  unfold tailWord_7768312
  simp only [CollatzResearch.WordTrace]
  refine ⟨141666807716369910454485595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188889076955159880605980793 141666807716369910454485595)
  ·
    refine ⟨212500211574554865681728393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141666807716369910454485595 212500211574554865681728393)
    ·
      refine ⟨159375158680916149261296295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212500211574554865681728393 159375158680916149261296295)
      ·
        refine ⟨239062738021374223891944443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159375158680916149261296295 239062738021374223891944443)
        ·
          refine ⟨358594107032061335837916665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239062738021374223891944443 358594107032061335837916665)
          ·
            refine ⟨268945580274046001878437499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358594107032061335837916665 268945580274046001878437499)
            ·
              refine ⟨403418370411069002817656249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268945580274046001878437499 403418370411069002817656249)
              ·
                refine ⟨302563777808301752113242187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403418370411069002817656249 302563777808301752113242187)
                ·
                  refine ⟨453845666712452628169863281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302563777808301752113242187 453845666712452628169863281)
                  ·
                    refine ⟨340384250034339471127397461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453845666712452628169863281 340384250034339471127397461)
                    ·
                      refine ⟨3988877930089915677274189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340384250034339471127397461 3988877930089915677274189)
                      ·
                        rfl

theorem cell23_7768312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_7768312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768312 prefixEnd_7768312 := by exact prefixLift 7768312
  have htrace : WordTrace (prefixWord ++ tailWord_7768312) baseStart_7768312 baseEnd_7768312 := by
    simpa [prefixWord, tailWord_7768312, baseEnd_7768312] using wordTrace_append hprefix tailTrace_7768312
  have hstable : (prefixWord ++ tailWord_7768312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768312).length < 2 ^ (prefixWord ++ tailWord_7768312).sum := by decide
  have hdescent : baseEnd_7768312 < baseStart_7768312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768324 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7768324 : Nat := 118140960795 + 7768324 * 2 ^ 59
def prefixEnd_7768324 : Nat := 4983230072969 + 3 ^ 40 * 7768324 * 2
def baseEnd_7768324 : Nat := 3988884091857769630324135

theorem tailTrace_7768324 : CollatzResearch.WordTrace tailWord_7768324 prefixEnd_7768324 3988884091857769630324135 := by
  unfold tailWord_7768324
  simp only [CollatzResearch.WordTrace]
  refine ⟨141667026554348173479204013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188889368739130897972272017 141667026554348173479204013)
  ·
    refine ⟨53125134957880565054701505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141667026554348173479204013 53125134957880565054701505)
    ·
      refine ⟨39843851218410423791026129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53125134957880565054701505 39843851218410423791026129)
      ·
        refine ⟨29882888413807817843269597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39843851218410423791026129 29882888413807817843269597)
        ·
          refine ⟨11206083155177931691226099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29882888413807817843269597 11206083155177931691226099)
          ·
            refine ⟨16809124732766897536839149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206083155177931691226099 16809124732766897536839149)
            ·
              refine ⟨6303421774787586576314681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16809124732766897536839149 6303421774787586576314681)
              ·
                refine ⟨4727566331090689932236011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303421774787586576314681 4727566331090689932236011)
                ·
                  refine ⟨7091349496636034898354017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727566331090689932236011 7091349496636034898354017)
                  ·
                    refine ⟨5318512122477026173765513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091349496636034898354017 5318512122477026173765513)
                    ·
                      refine ⟨3988884091857769630324135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318512122477026173765513 3988884091857769630324135)
                      ·
                        rfl

theorem cell23_7768324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7768324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768324 prefixEnd_7768324 := by exact prefixLift 7768324
  have htrace : WordTrace (prefixWord ++ tailWord_7768324) baseStart_7768324 baseEnd_7768324 := by
    simpa [prefixWord, tailWord_7768324, baseEnd_7768324] using wordTrace_append hprefix tailTrace_7768324
  have hstable : (prefixWord ++ tailWord_7768324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768324).length < 2 ^ (prefixWord ++ tailWord_7768324).sum := by decide
  have hdescent : baseEnd_7768324 < baseStart_7768324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768380 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_7768380 : Nat := 118140960795 + 7768380 * 2 ^ 59
def prefixEnd_7768380 : Nat := 4983230072969 + 3 ^ 40 * 7768380 * 2
def baseEnd_7768380 : Nat := 3988912846774421411223877

theorem tailTrace_7768380 : CollatzResearch.WordTrace tailWord_7768380 prefixEnd_7768380 3988912846774421411223877 := by
  unfold tailWord_7768380
  simp only [CollatzResearch.WordTrace]
  refine ⟨141668047798246734261223297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188890730397662312348297729 141668047798246734261223297)
  ·
    refine ⟨106251035848685050695917473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141668047798246734261223297 106251035848685050695917473)
    ·
      refine ⟨79688276886513788021938105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106251035848685050695917473 79688276886513788021938105)
      ·
        refine ⟨59766207664885341016453579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79688276886513788021938105 59766207664885341016453579)
        ·
          refine ⟨89649311497328011524680369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59766207664885341016453579 89649311497328011524680369)
          ·
            refine ⟨67236983622996008643510277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89649311497328011524680369 67236983622996008643510277)
            ·
              refine ⟨12606934429311751620658177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67236983622996008643510277 12606934429311751620658177)
              ·
                refine ⟨9455200821983813715493633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12606934429311751620658177 9455200821983813715493633)
                ·
                  refine ⟨7091400616487860286620225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455200821983813715493633 7091400616487860286620225)
                  ·
                    refine ⟨5318550462365895214965169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091400616487860286620225 5318550462365895214965169)
                    ·
                      refine ⟨3988912846774421411223877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318550462365895214965169 3988912846774421411223877)
                      ·
                        rfl

theorem cell23_7768380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_7768380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768380 prefixEnd_7768380 := by exact prefixLift 7768380
  have htrace : WordTrace (prefixWord ++ tailWord_7768380) baseStart_7768380 baseEnd_7768380 := by
    simpa [prefixWord, tailWord_7768380, baseEnd_7768380] using wordTrace_append hprefix tailTrace_7768380
  have hstable : (prefixWord ++ tailWord_7768380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768380).length < 2 ^ (prefixWord ++ tailWord_7768380).sum := by decide
  have hdescent : baseEnd_7768380 < baseStart_7768380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768396 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_7768396 : Nat := 118140960795 + 7768396 * 2 ^ 59
def prefixEnd_7768396 : Nat := 4983230072969 + 3 ^ 40 * 7768396 * 2
def baseEnd_7768396 : Nat := 3988921062464893348623803

theorem tailTrace_7768396 : CollatzResearch.WordTrace tailWord_7768396 prefixEnd_7768396 3988921062464893348623803 := by
  unfold tailWord_7768396
  simp only [CollatzResearch.WordTrace]
  refine ⟨141668339582217751627514521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188891119442957002170019361 141668339582217751627514521)
  ·
    refine ⟨106251254686663313720635891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141668339582217751627514521 106251254686663313720635891)
    ·
      refine ⟨159376882029994970580953837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106251254686663313720635891 159376882029994970580953837)
      ·
        refine ⟨59766330761248113967857689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159376882029994970580953837 59766330761248113967857689)
        ·
          refine ⟨44824748070936085475893267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59766330761248113967857689 44824748070936085475893267)
          ·
            refine ⟨67237122106404128213839901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44824748070936085475893267 67237122106404128213839901)
            ·
              refine ⟨25213920789901548080189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67237122106404128213839901 25213920789901548080189963)
              ·
                refine ⟨37820881184852322120284945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25213920789901548080189963 37820881184852322120284945)
                ·
                  refine ⟨28365660888639241590213709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37820881184852322120284945 28365660888639241590213709)
                  ·
                    refine ⟨10637122833239715596330141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28365660888639241590213709 10637122833239715596330141)
                    ·
                      refine ⟨3988921062464893348623803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637122833239715596330141 3988921062464893348623803)
                      ·
                        rfl

theorem cell23_7768396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_7768396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768396 prefixEnd_7768396 := by exact prefixLift 7768396
  have htrace : WordTrace (prefixWord ++ tailWord_7768396) baseStart_7768396 baseEnd_7768396 := by
    simpa [prefixWord, tailWord_7768396, baseEnd_7768396] using wordTrace_append hprefix tailTrace_7768396
  have hstable : (prefixWord ++ tailWord_7768396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768396).length < 2 ^ (prefixWord ++ tailWord_7768396).sum := by decide
  have hdescent : baseEnd_7768396 < baseStart_7768396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768416 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_7768416 : Nat := 118140960795 + 7768416 * 2 ^ 59
def prefixEnd_7768416 : Nat := 4983230072969 + 3 ^ 40 * 7768416 * 2
def baseEnd_7768416 : Nat := 1329643777359327756791237

theorem tailTrace_7768416 : CollatzResearch.WordTrace tailWord_7768416 prefixEnd_7768416 1329643777359327756791237 := by
  unfold tailWord_7768416
  simp only [CollatzResearch.WordTrace]
  refine ⟨141668704312181523335378551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188891605749575364447171401 141668704312181523335378551)
  ·
    refine ⟨212503056468272285003067827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141668704312181523335378551 212503056468272285003067827)
    ·
      refine ⟨318754584702408427504601741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212503056468272285003067827 318754584702408427504601741)
      ·
        refine ⟨119532969263403160314225653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318754584702408427504601741 119532969263403160314225653)
        ·
          refine ⟨11206215868444046279458655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119532969263403160314225653 11206215868444046279458655)
          ·
            refine ⟨16809323802666069419187983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206215868444046279458655 16809323802666069419187983)
            ·
              refine ⟨25213985703999104128781975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16809323802666069419187983 25213985703999104128781975)
              ·
                refine ⟨37820978555998656193172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25213985703999104128781975 37820978555998656193172963)
                ·
                  refine ⟨56731467833997984289759445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37820978555998656193172963 56731467833997984289759445)
                  ·
                    refine ⟨1329643777359327756791237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56731467833997984289759445 1329643777359327756791237)
                    ·
                      rfl

theorem cell23_7768416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_7768416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768416 prefixEnd_7768416 := by exact prefixLift 7768416
  have htrace : WordTrace (prefixWord ++ tailWord_7768416) baseStart_7768416 baseEnd_7768416 := by
    simpa [prefixWord, tailWord_7768416, baseEnd_7768416] using wordTrace_append hprefix tailTrace_7768416
  have hstable : (prefixWord ++ tailWord_7768416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768416).length < 2 ^ (prefixWord ++ tailWord_7768416).sum := by decide
  have hdescent : baseEnd_7768416 < baseStart_7768416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768456 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7768456 : Nat := 118140960795 + 7768456 * 2 ^ 59
def prefixEnd_7768456 : Nat := 4983230072969 + 3 ^ 40 * 7768456 * 2
def baseEnd_7768456 : Nat := 3988951871304163113873527

theorem tailTrace_7768456 : CollatzResearch.WordTrace tailWord_7768456 prefixEnd_7768456 3988951871304163113873527 := by
  unfold tailWord_7768456
  simp only [CollatzResearch.WordTrace]
  refine ⟨141669433772109066751106611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188892578362812089001475481 141669433772109066751106611)
  ·
    refine ⟨212504150658163600126659917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141669433772109066751106611 212504150658163600126659917)
    ·
      refine ⟨79689056496811350047497469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212504150658163600126659917 79689056496811350047497469)
      ·
        refine ⟨29883396186304256267811551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79689056496811350047497469 29883396186304256267811551)
        ·
          refine ⟨44825094279456384401717327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29883396186304256267811551 44825094279456384401717327)
          ·
            refine ⟨67237641419184576602575991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44825094279456384401717327 67237641419184576602575991)
            ·
              refine ⟨100856462128776864903863987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67237641419184576602575991 100856462128776864903863987)
              ·
                refine ⟨151284693193165297355795981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100856462128776864903863987 151284693193165297355795981)
                ·
                  refine ⟨56731759947436986508423493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151284693193165297355795981 56731759947436986508423493)
                  ·
                    refine ⟨10637204990144434970329405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56731759947436986508423493 10637204990144434970329405)
                    ·
                      refine ⟨3988951871304163113873527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637204990144434970329405 3988951871304163113873527)
                      ·
                        rfl

theorem cell23_7768456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7768456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768456 prefixEnd_7768456 := by exact prefixLift 7768456
  have htrace : WordTrace (prefixWord ++ tailWord_7768456) baseStart_7768456 baseEnd_7768456 := by
    simpa [prefixWord, tailWord_7768456, baseEnd_7768456] using wordTrace_append hprefix tailTrace_7768456
  have hstable : (prefixWord ++ tailWord_7768456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768456).length < 2 ^ (prefixWord ++ tailWord_7768456).sum := by decide
  have hdescent : baseEnd_7768456 < baseStart_7768456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768480 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 1, 4]
def baseStart_7768480 : Nat := 118140960795 + 7768480 * 2 ^ 59
def prefixEnd_7768480 : Nat := 4983230072969 + 3 ^ 40 * 7768480 * 2
def baseEnd_7768480 : Nat := 1329654731613290339991139

theorem tailTrace_7768480 : CollatzResearch.WordTrace tailWord_7768480 prefixEnd_7768480 1329654731613290339991139 := by
  unfold tailWord_7768480
  simp only [CollatzResearch.WordTrace]
  refine ⟨141669871448065592800543447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188893161930754123734057929 141669871448065592800543447)
  ·
    refine ⟨212504807172098389200815171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141669871448065592800543447 212504807172098389200815171)
    ·
      refine ⟨318757210758147583801222757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212504807172098389200815171 318757210758147583801222757)
      ·
        refine ⟨59766977017152671962729267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318757210758147583801222757 59766977017152671962729267)
        ·
          refine ⟨89650465525729007944093901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59766977017152671962729267 89650465525729007944093901)
          ·
            refine ⟨33618924572148377979035213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89650465525729007944093901 33618924572148377979035213)
            ·
              refine ⟨12607096714555641742138205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33618924572148377979035213 12607096714555641742138205)
              ·
                refine ⟨4727661267958365653301827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12607096714555641742138205 4727661267958365653301827)
                ·
                  refine ⟨7091491901937548479952741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727661267958365653301827 7091491901937548479952741)
                  ·
                    refine ⟨1329654731613290339991139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091491901937548479952741 1329654731613290339991139)
                    ·
                      rfl

theorem cell23_7768480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_7768480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768480 prefixEnd_7768480 := by exact prefixLift 7768480
  have htrace : WordTrace (prefixWord ++ tailWord_7768480) baseStart_7768480 baseEnd_7768480 := by
    simpa [prefixWord, tailWord_7768480, baseEnd_7768480] using wordTrace_append hprefix tailTrace_7768480
  have hstable : (prefixWord ++ tailWord_7768480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768480).length < 2 ^ (prefixWord ++ tailWord_7768480).sum := by decide
  have hdescent : baseEnd_7768480 < baseStart_7768480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768497 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 1, 4]
def baseStart_7768497 : Nat := 118140960795 + 7768497 * 2 ^ 59
def prefixEnd_7768497 : Nat := 4983230072969 + 3 ^ 40 * 7768497 * 2
def baseEnd_7768497 : Nat := 1329657641336999151153613

theorem tailTrace_7768497 : CollatzResearch.WordTrace tailWord_7768497 prefixEnd_7768497 1329657641336999151153613 := by
  unfold tailWord_7768497
  simp only [CollatzResearch.WordTrace]
  refine ⟨283340362937069597504455745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188893575291379731669637163 283340362937069597504455745)
  ·
    refine ⟨212505272202802198128341809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283340362937069597504455745 212505272202802198128341809)
    ·
      refine ⟨159378954152101648596256357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212505272202802198128341809 159378954152101648596256357)
      ·
        refine ⟨29883553903519059111798067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159378954152101648596256357 29883553903519059111798067)
        ·
          refine ⟨44825330855278588667697101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29883553903519059111798067 44825330855278588667697101)
          ·
            refine ⟨16809499070729470750386413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44825330855278588667697101 16809499070729470750386413)
            ·
              refine ⟨6303562151523551531394905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16809499070729470750386413 6303562151523551531394905)
              ·
                refine ⟨4727671613642663648546179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303562151523551531394905 4727671613642663648546179)
                ·
                  refine ⟨7091507420463995472819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727671613642663648546179 7091507420463995472819269)
                  ·
                    refine ⟨1329657641336999151153613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091507420463995472819269 1329657641336999151153613)
                    ·
                      rfl

theorem cell23_7768497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_7768497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768497 prefixEnd_7768497 := by exact prefixLift 7768497
  have htrace : WordTrace (prefixWord ++ tailWord_7768497) baseStart_7768497 baseEnd_7768497 := by
    simpa [prefixWord, tailWord_7768497, baseEnd_7768497] using wordTrace_append hprefix tailTrace_7768497
  have hstable : (prefixWord ++ tailWord_7768497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768497).length < 2 ^ (prefixWord ++ tailWord_7768497).sum := by decide
  have hdescent : baseEnd_7768497 < baseStart_7768497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768499 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_7768499 : Nat := 118140960795 + 7768499 * 2 ^ 59
def prefixEnd_7768499 : Nat := 4983230072969 + 3 ^ 40 * 7768499 * 2
def baseEnd_7768499 : Nat := 3988973950972306445635829

theorem tailTrace_7768499 : CollatzResearch.WordTrace tailWord_7768499 prefixEnd_7768499 3988973950972306445635829 := by
  unfold tailWord_7768499
  simp only [CollatzResearch.WordTrace]
  refine ⟨283340435883062351846028551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188893623922041567897352367 283340435883062351846028551)
  ·
    refine ⟨425010653824593527769042827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283340435883062351846028551 425010653824593527769042827)
    ·
      refine ⟨637515980736890291653564241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425010653824593527769042827 637515980736890291653564241)
      ·
        refine ⟨478136985552667718740173181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637515980736890291653564241 478136985552667718740173181)
        ·
          refine ⟨179301369582250394527564943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478136985552667718740173181 179301369582250394527564943)
          ·
            refine ⟨268952054373375591791347415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179301369582250394527564943 268952054373375591791347415)
            ·
              refine ⟨403428081560063387687021123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268952054373375591791347415 403428081560063387687021123)
              ·
                refine ⟨605142122340095081530531685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403428081560063387687021123 605142122340095081530531685)
                ·
                  refine ⟨113464147938767827786974691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605142122340095081530531685 113464147938767827786974691)
                  ·
                    refine ⟨170196221908151741680462037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113464147938767827786974691 170196221908151741680462037)
                    ·
                      refine ⟨3988973950972306445635829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170196221908151741680462037 3988973950972306445635829)
                      ·
                        rfl

theorem cell23_7768499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_7768499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768499 prefixEnd_7768499 := by exact prefixLift 7768499
  have htrace : WordTrace (prefixWord ++ tailWord_7768499) baseStart_7768499 baseEnd_7768499 := by
    simpa [prefixWord, tailWord_7768499, baseEnd_7768499] using wordTrace_append hprefix tailTrace_7768499
  have hstable : (prefixWord ++ tailWord_7768499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768499).length < 2 ^ (prefixWord ++ tailWord_7768499).sum := by decide
  have hdescent : baseEnd_7768499 < baseStart_7768499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768554 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_7768554 : Nat := 118140960795 + 7768554 * 2 ^ 59
def prefixEnd_7768554 : Nat := 4983230072969 + 3 ^ 40 * 7768554 * 2
def baseEnd_7768554 : Nat := 3989002192408303730448077

theorem tailTrace_7768554 : CollatzResearch.WordTrace tailWord_7768554 prefixEnd_7768554 3989002192408303730448077 := by
  unfold tailWord_7768554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70835610474465774059820179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188894961265242064159520477 70835610474465774059820179)
  ·
    refine ⟨106253415711698661089730269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70835610474465774059820179 106253415711698661089730269)
    ·
      refine ⟨39845030891886997908648851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106253415711698661089730269 39845030891886997908648851)
      ·
        refine ⟨59767546337830496862973277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39845030891886997908648851 59767546337830496862973277)
        ·
          refine ⟨22412829876686436323614979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59767546337830496862973277 22412829876686436323614979)
          ·
            refine ⟨33619244815029654485422469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22412829876686436323614979 33619244815029654485422469)
            ·
              refine ⟨6303608402818060216016713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33619244815029654485422469 6303608402818060216016713)
              ·
                refine ⟨4727706302113545162012535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303608402818060216016713 4727706302113545162012535)
                ·
                  refine ⟨7091559453170317743018803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727706302113545162012535 7091559453170317743018803)
                  ·
                    refine ⟨10637339179755476614528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7091559453170317743018803 10637339179755476614528205)
                    ·
                      refine ⟨3989002192408303730448077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637339179755476614528205 3989002192408303730448077)
                      ·
                        rfl

theorem cell23_7768554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_7768554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768554 prefixEnd_7768554 := by exact prefixLift 7768554
  have htrace : WordTrace (prefixWord ++ tailWord_7768554) baseStart_7768554 baseEnd_7768554 := by
    simpa [prefixWord, tailWord_7768554, baseEnd_7768554] using wordTrace_append hprefix tailTrace_7768554
  have hstable : (prefixWord ++ tailWord_7768554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768554).length < 2 ^ (prefixWord ++ tailWord_7768554).sum := by decide
  have hdescent : baseEnd_7768554 < baseStart_7768554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768556 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_7768556 : Nat := 118140960795 + 7768556 * 2 ^ 59
def prefixEnd_7768556 : Nat := 4983230072969 + 3 ^ 40 * 7768556 * 2
def baseEnd_7768556 : Nat := 3989003219369612722623067

theorem tailTrace_7768556 : CollatzResearch.WordTrace tailWord_7768556 prefixEnd_7768556 3989003219369612722623067 := by
  unfold tailWord_7768556
  simp only [CollatzResearch.WordTrace]
  refine ⟨141671257421927925290426761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188895009895903900387235681 141671257421927925290426761)
  ·
    refine ⟨106253443066445943967820071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141671257421927925290426761 106253443066445943967820071)
    ·
      refine ⟨159380164599668915951730107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106253443066445943967820071 159380164599668915951730107)
      ·
        refine ⟨239070246899503373927595161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159380164599668915951730107 239070246899503373927595161)
        ·
          refine ⟨179302685174627530445696371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239070246899503373927595161 179302685174627530445696371)
          ·
            refine ⟨268954027761941295668544557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179302685174627530445696371 268954027761941295668544557)
            ·
              refine ⟨100857760410727985875704209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268954027761941295668544557 100857760410727985875704209)
              ·
                refine ⟨75643320308045989406778157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100857760410727985875704209 75643320308045989406778157)
                ·
                  refine ⟨28366245115517246027541809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75643320308045989406778157 28366245115517246027541809)
                  ·
                    refine ⟨21274683836637934520656357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28366245115517246027541809 21274683836637934520656357)
                    ·
                      refine ⟨3989003219369612722623067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21274683836637934520656357 3989003219369612722623067)
                      ·
                        rfl

theorem cell23_7768556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_7768556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768556 prefixEnd_7768556 := by exact prefixLift 7768556
  have htrace : WordTrace (prefixWord ++ tailWord_7768556) baseStart_7768556 baseEnd_7768556 := by
    simpa [prefixWord, tailWord_7768556, baseEnd_7768556] using wordTrace_append hprefix tailTrace_7768556
  have hstable : (prefixWord ++ tailWord_7768556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768556).length < 2 ^ (prefixWord ++ tailWord_7768556).sum := by decide
  have hdescent : baseEnd_7768556 < baseStart_7768556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768560 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2]
def baseStart_7768560 : Nat := 118140960795 + 7768560 * 2 ^ 59
def prefixEnd_7768560 : Nat := 4983230072969 + 3 ^ 40 * 7768560 * 2
def baseEnd_7768560 : Nat := 3989005273292230706973049

theorem tailTrace_7768560 : CollatzResearch.WordTrace tailWord_7768560 prefixEnd_7768560 3989005273292230706973049 := by
  unfold tailWord_7768560
  simp only [CollatzResearch.WordTrace]
  refine ⟨141671330367920679631999567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188895107157227572842666089 141671330367920679631999567)
  ·
    refine ⟨212506995551881019447999351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141671330367920679631999567 212506995551881019447999351)
    ·
      refine ⟨318760493327821529171999027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212506995551881019447999351 318760493327821529171999027)
      ·
        refine ⟨478140739991732293757998541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318760493327821529171999027 478140739991732293757998541)
        ·
          refine ⟨179302777496899610159249453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478140739991732293757998541 179302777496899610159249453)
          ·
            refine ⟨67238541561337353809718545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179302777496899610159249453 67238541561337353809718545)
            ·
              refine ⟨50428906171003015357288909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67238541561337353809718545 50428906171003015357288909)
              ·
                refine ⟨18910839814126130758983341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50428906171003015357288909 18910839814126130758983341)
                ·
                  refine ⟨7091564930297299034618753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18910839814126130758983341 7091564930297299034618753)
                  ·
                    refine ⟨5318673697722974275964065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091564930297299034618753 5318673697722974275964065)
                    ·
                      refine ⟨3989005273292230706973049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318673697722974275964065 3989005273292230706973049)
                      ·
                        rfl

theorem cell23_7768560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2].length) (baseStart_7768560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768560 prefixEnd_7768560 := by exact prefixLift 7768560
  have htrace : WordTrace (prefixWord ++ tailWord_7768560) baseStart_7768560 baseEnd_7768560 := by
    simpa [prefixWord, tailWord_7768560, baseEnd_7768560] using wordTrace_append hprefix tailTrace_7768560
  have hstable : (prefixWord ++ tailWord_7768560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768560).length < 2 ^ (prefixWord ++ tailWord_7768560).sum := by decide
  have hdescent : baseEnd_7768560 < baseStart_7768560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768573 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_7768573 : Nat := 118140960795 + 7768573 * 2 ^ 59
def prefixEnd_7768573 : Nat := 4983230072969 + 3 ^ 40 * 7768573 * 2
def baseEnd_7768573 : Nat := 3989011948540739156110489

theorem tailTrace_7768573 : CollatzResearch.WordTrace tailWord_7768573 prefixEnd_7768573 3989011948540739156110489 := by
  unfold tailWord_7768573
  simp only [CollatzResearch.WordTrace]
  refine ⟨283343134884794262484222373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188895423256529508322814915 283343134884794262484222373)
  ·
    refine ⟨53126837790898924215791695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283343134884794262484222373 53126837790898924215791695)
    ·
      refine ⟨79690256686348386323687543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53126837790898924215791695 79690256686348386323687543)
      ·
        refine ⟨119535385029522579485531315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79690256686348386323687543 119535385029522579485531315)
        ·
          refine ⟨179303077544283869228296973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119535385029522579485531315 179303077544283869228296973)
          ·
            refine ⟨67238654079106450960611365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179303077544283869228296973 67238654079106450960611365)
            ·
              refine ⟨12607247639832459555114631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67238654079106450960611365 12607247639832459555114631)
              ·
                refine ⟨18910871459748689332671947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607247639832459555114631 18910871459748689332671947)
                ·
                  refine ⟨28366307189623033999007921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18910871459748689332671947 28366307189623033999007921)
                  ·
                    refine ⟨21274730392217275499255941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28366307189623033999007921 21274730392217275499255941)
                    ·
                      refine ⟨3989011948540739156110489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21274730392217275499255941 3989011948540739156110489)
                      ·
                        rfl

theorem cell23_7768573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_7768573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768573 prefixEnd_7768573 := by exact prefixLift 7768573
  have htrace : WordTrace (prefixWord ++ tailWord_7768573) baseStart_7768573 baseEnd_7768573 := by
    simpa [prefixWord, tailWord_7768573, baseEnd_7768573] using wordTrace_append hprefix tailTrace_7768573
  have hstable : (prefixWord ++ tailWord_7768573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768573).length < 2 ^ (prefixWord ++ tailWord_7768573).sum := by decide
  have hdescent : baseEnd_7768573 < baseStart_7768573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768577 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_7768577 : Nat := 118140960795 + 7768577 * 2 ^ 59
def prefixEnd_7768577 : Nat := 4983230072969 + 3 ^ 40 * 7768577 * 2
def baseEnd_7768577 : Nat := 3989014002463357140460471

theorem tailTrace_7768577 : CollatzResearch.WordTrace tailWord_7768577 prefixEnd_7768577 3989014002463357140460471 := by
  unfold tailWord_7768577
  simp only [CollatzResearch.WordTrace]
  refine ⟨283343280776779771167367985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188895520517853180778245323 283343280776779771167367985)
  ·
    refine ⟨212507460582584828375525989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283343280776779771167367985 212507460582584828375525989)
    ·
      refine ⟨39845148859234655320411123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212507460582584828375525989 39845148859234655320411123)
      ·
        refine ⟨59767723288851982980616685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39845148859234655320411123 59767723288851982980616685)
        ·
          refine ⟨22412896233319493617731257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59767723288851982980616685 22412896233319493617731257)
          ·
            refine ⟨16809672174989620213298443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412896233319493617731257 16809672174989620213298443)
            ·
              refine ⟨25214508262484430319947665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16809672174989620213298443 25214508262484430319947665)
              ·
                refine ⟨18910881196863322739960749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25214508262484430319947665 18910881196863322739960749)
                ·
                  refine ⟨7091580448823746027485281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18910881196863322739960749 7091580448823746027485281)
                  ·
                    refine ⟨5318685336617809520613961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091580448823746027485281 5318685336617809520613961)
                    ·
                      refine ⟨3989014002463357140460471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318685336617809520613961 3989014002463357140460471)
                      ·
                        rfl

theorem cell23_7768577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_7768577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768577 prefixEnd_7768577 := by exact prefixLift 7768577
  have htrace : WordTrace (prefixWord ++ tailWord_7768577) baseStart_7768577 baseEnd_7768577 := by
    simpa [prefixWord, tailWord_7768577, baseEnd_7768577] using wordTrace_append hprefix tailTrace_7768577
  have hstable : (prefixWord ++ tailWord_7768577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768577).length < 2 ^ (prefixWord ++ tailWord_7768577).sum := by decide
  have hdescent : baseEnd_7768577 < baseStart_7768577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768580 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7768580 : Nat := 118140960795 + 7768580 * 2 ^ 59
def prefixEnd_7768580 : Nat := 4983230072969 + 3 ^ 40 * 7768580 * 2
def baseEnd_7768580 : Nat := 3989015542905320628722957

theorem tailTrace_7768580 : CollatzResearch.WordTrace tailWord_7768580 prefixEnd_7768580 3989015542905320628722957 := by
  unfold tailWord_7768580
  simp only [CollatzResearch.WordTrace]
  refine ⟨141671695097884451339863597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188895593463845935119818129 141671695097884451339863597)
  ·
    refine ⟨53126885661706669252448849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141671695097884451339863597 53126885661706669252448849)
    ·
      refine ⟨39845164246280001939336637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53126885661706669252448849 39845164246280001939336637)
      ·
        refine ⟨14941936592355000727251239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39845164246280001939336637 14941936592355000727251239)
        ·
          refine ⟨22412904888532501090876859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14941936592355000727251239 22412904888532501090876859)
          ·
            refine ⟨33619357332798751636315289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22412904888532501090876859 33619357332798751636315289)
            ·
              refine ⟨25214517999599063727236467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33619357332798751636315289 25214517999599063727236467)
              ·
                refine ⟨37821776999398595590854701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25214517999599063727236467 37821776999398595590854701)
                ·
                  refine ⟨14183166374774473346570513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37821776999398595590854701 14183166374774473346570513)
                  ·
                    refine ⟨10637374781080855009927885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14183166374774473346570513 10637374781080855009927885)
                    ·
                      refine ⟨3989015542905320628722957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637374781080855009927885 3989015542905320628722957)
                      ·
                        rfl

theorem cell23_7768580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7768580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768580 prefixEnd_7768580 := by exact prefixLift 7768580
  have htrace : WordTrace (prefixWord ++ tailWord_7768580) baseStart_7768580 baseEnd_7768580 := by
    simpa [prefixWord, tailWord_7768580, baseEnd_7768580] using wordTrace_append hprefix tailTrace_7768580
  have hstable : (prefixWord ++ tailWord_7768580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768580).length < 2 ^ (prefixWord ++ tailWord_7768580).sum := by decide
  have hdescent : baseEnd_7768580 < baseStart_7768580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768621 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7768621 : Nat := 118140960795 + 7768621 * 2 ^ 59
def prefixEnd_7768621 : Nat := 4983230072969 + 3 ^ 40 * 7768621 * 2
def baseEnd_7768621 : Nat := 1329678865204051656103423

theorem tailTrace_7768621 : CollatzResearch.WordTrace tailWord_7768621 prefixEnd_7768621 1329678865204051656103423 := by
  unfold tailWord_7768621
  simp only [CollatzResearch.WordTrace]
  refine ⟨283344885588620366681969717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188896590392413577787979811 283344885588620366681969717)
  ·
    refine ⟨26563583023933159376434661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283344885588620366681969717 26563583023933159376434661)
    ·
      refine ⟨4980671816987467383081499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26563583023933159376434661 4980671816987467383081499)
      ·
        refine ⟨7471007725481201074622249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980671816987467383081499 7471007725481201074622249)
        ·
          refine ⟨5603255794110900805966687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7471007725481201074622249 5603255794110900805966687)
          ·
            refine ⟨8404883691166351208950031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603255794110900805966687 8404883691166351208950031)
            ·
              refine ⟨12607325536749526813425047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404883691166351208950031 12607325536749526813425047)
              ·
                refine ⟨18910988305124290220137571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607325536749526813425047 18910988305124290220137571)
                ·
                  refine ⟨28366482457686435330206357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18910988305124290220137571 28366482457686435330206357)
                  ·
                    refine ⟨1329678865204051656103423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28366482457686435330206357 1329678865204051656103423)
                    ·
                      rfl

theorem cell23_7768621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7768621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768621 prefixEnd_7768621 := by exact prefixLift 7768621
  have htrace : WordTrace (prefixWord ++ tailWord_7768621) baseStart_7768621 baseEnd_7768621 := by
    simpa [prefixWord, tailWord_7768621, baseEnd_7768621] using wordTrace_append hprefix tailTrace_7768621
  have hstable : (prefixWord ++ tailWord_7768621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768621).length < 2 ^ (prefixWord ++ tailWord_7768621).sum := by decide
  have hdescent : baseEnd_7768621 < baseStart_7768621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768627 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 2, 1, 3]
def baseStart_7768627 : Nat := 118140960795 + 7768627 * 2 ^ 59
def prefixEnd_7768627 : Nat := 4983230072969 + 3 ^ 40 * 7768627 * 2
def baseEnd_7768627 : Nat := 3989039676496081944835241

theorem tailTrace_7768627 : CollatzResearch.WordTrace tailWord_7768627 prefixEnd_7768627 3989039676496081944835241 := by
  unfold tailWord_7768627
  simp only [CollatzResearch.WordTrace]
  refine ⟨283345104426598629706688135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188896736284399086471125423 283345104426598629706688135)
  ·
    refine ⟨425017656639897944560032203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283345104426598629706688135 425017656639897944560032203)
    ·
      refine ⟨637526484959846916840048305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425017656639897944560032203 637526484959846916840048305)
      ·
        refine ⟨478144863719885187630036229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637526484959846916840048305 478144863719885187630036229)
        ·
          refine ⟨89652161947478472680631793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478144863719885187630036229 89652161947478472680631793)
          ·
            refine ⟨67239121460608854510473845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89652161947478472680631793 67239121460608854510473845)
            ·
              refine ⟨6303667636932080110356923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67239121460608854510473845 6303667636932080110356923)
              ·
                refine ⟨9455501455398120165535385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303667636932080110356923 9455501455398120165535385)
                ·
                  refine ⟨7091626091548590124151539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455501455398120165535385 7091626091548590124151539)
                  ·
                    refine ⟨10637439137322885186227309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7091626091548590124151539 10637439137322885186227309)
                    ·
                      refine ⟨3989039676496081944835241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637439137322885186227309 3989039676496081944835241)
                      ·
                        rfl

theorem cell23_7768627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 1, 3].length) (baseStart_7768627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768627 prefixEnd_7768627 := by exact prefixLift 7768627
  have htrace : WordTrace (prefixWord ++ tailWord_7768627) baseStart_7768627 baseEnd_7768627 := by
    simpa [prefixWord, tailWord_7768627, baseEnd_7768627] using wordTrace_append hprefix tailTrace_7768627
  have hstable : (prefixWord ++ tailWord_7768627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768627).length < 2 ^ (prefixWord ++ tailWord_7768627).sum := by decide
  have hdescent : baseEnd_7768627 < baseStart_7768627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768637 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7768637 : Nat := 118140960795 + 7768637 * 2 ^ 59
def prefixEnd_7768637 : Nat := 4983230072969 + 3 ^ 40 * 7768637 * 2
def baseEnd_7768637 : Nat := 3989044811302626905710195

theorem tailTrace_7768637 : CollatzResearch.WordTrace tailWord_7768637 prefixEnd_7768637 3989044811302626905710195 := by
  unfold tailWord_7768637
  simp only [CollatzResearch.WordTrace]
  refine ⟨283345469156562401414552165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188896979437708267609701443 283345469156562401414552165)
  ·
    refine ⟨53127275466855450265228531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283345469156562401414552165 53127275466855450265228531)
    ·
      refine ⟨79690913200283175397842797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53127275466855450265228531 79690913200283175397842797)
      ·
        refine ⟨29884092450106190774191049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79690913200283175397842797 29884092450106190774191049)
        ·
          refine ⟨22413069337579643080643287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29884092450106190774191049 22413069337579643080643287)
          ·
            refine ⟨33619604006369464620964931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22413069337579643080643287 33619604006369464620964931)
            ·
              refine ⟨50429406009554196931447397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33619604006369464620964931 50429406009554196931447397)
              ·
                refine ⟨9455513626791411924646387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50429406009554196931447397 9455513626791411924646387)
                ·
                  refine ⟨14183270440187117886969581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455513626791411924646387 14183270440187117886969581)
                  ·
                    refine ⟨5318726415070169207613593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14183270440187117886969581 5318726415070169207613593)
                    ·
                      refine ⟨3989044811302626905710195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318726415070169207613593 3989044811302626905710195)
                      ·
                        rfl

theorem cell23_7768637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7768637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768637 prefixEnd_7768637 := by exact prefixLift 7768637
  have htrace : WordTrace (prefixWord ++ tailWord_7768637) baseStart_7768637 baseEnd_7768637 := by
    simpa [prefixWord, tailWord_7768637, baseEnd_7768637] using wordTrace_append hprefix tailTrace_7768637
  have hstable : (prefixWord ++ tailWord_7768637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768637).length < 2 ^ (prefixWord ++ tailWord_7768637).sum := by decide
  have hdescent : baseEnd_7768637 < baseStart_7768637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768673 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 7]
def baseStart_7768673 : Nat := 118140960795 + 7768673 * 2 ^ 59
def prefixEnd_7768673 : Nat := 4983230072969 + 3 ^ 40 * 7768673 * 2
def baseEnd_7768673 : Nat := 443229255178465418317781

theorem tailTrace_7768673 : CollatzResearch.WordTrace tailWord_7768673 prefixEnd_7768673 443229255178465418317781 := by
  unfold tailWord_7768673
  simp only [CollatzResearch.WordTrace]
  refine ⟨283346782184431979562862673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188897854789621319708575115 283346782184431979562862673)
  ·
    refine ⟨212510086638323984672147005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283346782184431979562862673 212510086638323984672147005)
    ·
      refine ⟨79691282489371494252055127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212510086638323984672147005 79691282489371494252055127)
      ·
        refine ⟨119536923734057241378082691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79691282489371494252055127 119536923734057241378082691)
        ·
          refine ⟨179305385601085862067124037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119536923734057241378082691 179305385601085862067124037)
          ·
            refine ⟨33619759800203599137585757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179305385601085862067124037 33619759800203599137585757)
            ·
              refine ⟨12607409925076349676594659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33619759800203599137585757 12607409925076349676594659)
              ·
                refine ⟨18911114887614524514891989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607409925076349676594659 18911114887614524514891989)
                ·
                  refine ⟨443229255178465418317781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18911114887614524514891989 443229255178465418317781)
                  ·
                    rfl

theorem cell23_7768673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_7768673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768673 prefixEnd_7768673 := by exact prefixLift 7768673
  have htrace : WordTrace (prefixWord ++ tailWord_7768673) baseStart_7768673 baseEnd_7768673 := by
    simpa [prefixWord, tailWord_7768673, baseEnd_7768673] using wordTrace_append hprefix tailTrace_7768673
  have hstable : (prefixWord ++ tailWord_7768673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768673).length < 2 ^ (prefixWord ++ tailWord_7768673).sum := by decide
  have hdescent : baseEnd_7768673 < baseStart_7768673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768684 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_7768684 : Nat := 118140960795 + 7768684 * 2 ^ 59
def prefixEnd_7768684 : Nat := 4983230072969 + 3 ^ 40 * 7768684 * 2
def baseEnd_7768684 : Nat := 3989068944893388221822479

theorem tailTrace_7768684 : CollatzResearch.WordTrace tailWord_7768684 prefixEnd_7768684 3989068944893388221822479 := by
  unfold tailWord_7768684
  simp only [CollatzResearch.WordTrace]
  refine ⟨141673591693696064220756553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188898122258261418961008737 141673591693696064220756553)
  ·
    refine ⟨106255193770272048165567415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141673591693696064220756553 106255193770272048165567415)
    ·
      refine ⟨159382790655408072248351123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106255193770272048165567415 159382790655408072248351123)
      ·
        refine ⟨239074185983112108372526685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159382790655408072248351123 239074185983112108372526685)
        ·
          refine ⟨89652819743667040639697507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239074185983112108372526685 89652819743667040639697507)
          ·
            refine ⟨134479229615500560959546261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89652819743667040639697507 134479229615500560959546261)
            ·
              refine ⟨6303713888226588794978731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134479229615500560959546261 6303713888226588794978731)
              ·
                refine ⟨9455570832339883192468097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303713888226588794978731 9455570832339883192468097)
                ·
                  refine ⟨7091678124254912394351073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455570832339883192468097 7091678124254912394351073)
                  ·
                    refine ⟨5318758593191184295763305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091678124254912394351073 5318758593191184295763305)
                    ·
                      refine ⟨3989068944893388221822479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318758593191184295763305 3989068944893388221822479)
                      ·
                        rfl

theorem cell23_7768684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_7768684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768684 prefixEnd_7768684 := by exact prefixLift 7768684
  have htrace : WordTrace (prefixWord ++ tailWord_7768684) baseStart_7768684 baseEnd_7768684 := by
    simpa [prefixWord, tailWord_7768684, baseEnd_7768684] using wordTrace_append hprefix tailTrace_7768684
  have hstable : (prefixWord ++ tailWord_7768684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768684).length < 2 ^ (prefixWord ++ tailWord_7768684).sum := by decide
  have hdescent : baseEnd_7768684 < baseStart_7768684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768724 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 5]
def baseStart_7768724 : Nat := 118140960795 + 7768724 * 2 ^ 59
def prefixEnd_7768724 : Nat := 4983230072969 + 3 ^ 40 * 7768724 * 2
def baseEnd_7768724 : Nat := 443232164902174229480255

theorem tailTrace_7768724 : CollatzResearch.WordTrace tailWord_7768724 prefixEnd_7768724 443232164902174229480255 := by
  unfold tailWord_7768724
  simp only [CollatzResearch.WordTrace]
  refine ⟨141674321153623607636484613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188899094871498143515312817 141674321153623607636484613)
  ·
    refine ⟨26563935216304426431840865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141674321153623607636484613 26563935216304426431840865)
    ·
      refine ⟨19922951412228319823880649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26563935216304426431840865 19922951412228319823880649)
      ·
        refine ⟨14942213559171239867910487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19922951412228319823880649 14942213559171239867910487)
        ·
          refine ⟨22413320338756859801865731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942213559171239867910487 22413320338756859801865731)
          ·
            refine ⟨33619980508135289702798597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22413320338756859801865731 33619980508135289702798597)
            ·
              refine ⟨6303746345275366819274737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33619980508135289702798597 6303746345275366819274737)
              ·
                refine ⟨4727809758956525114456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6303746345275366819274737 4727809758956525114456053)
                ·
                  refine ⟨443232164902174229480255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727809758956525114456053 443232164902174229480255)
                  ·
                    rfl

theorem cell23_7768724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_7768724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768724 prefixEnd_7768724 := by exact prefixLift 7768724
  have htrace : WordTrace (prefixWord ++ tailWord_7768724) baseStart_7768724 baseEnd_7768724 := by
    simpa [prefixWord, tailWord_7768724, baseEnd_7768724] using wordTrace_append hprefix tailTrace_7768724
  have hstable : (prefixWord ++ tailWord_7768724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768724).length < 2 ^ (prefixWord ++ tailWord_7768724).sum := by decide
  have hdescent : baseEnd_7768724 < baseStart_7768724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768757 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7768757 : Nat := 118140960795 + 7768757 * 2 ^ 59
def prefixEnd_7768757 : Nat := 4983230072969 + 3 ^ 40 * 7768757 * 2
def baseEnd_7768757 : Nat := 3989106428981166436209643

theorem tailTrace_7768757 : CollatzResearch.WordTrace tailWord_7768757 prefixEnd_7768757 3989106428981166436209643 := by
  unfold tailWord_7768757
  simp only [CollatzResearch.WordTrace]
  refine ⟨283349845916127661908920525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188899897277418441272613683 283349845916127661908920525)
  ·
    refine ⟨106256192218547873215845197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283349845916127661908920525 106256192218547873215845197)
    ·
      refine ⟨39846072081955452455941949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106256192218547873215845197 39846072081955452455941949)
      ·
        refine ⟨14942277030733294670978231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39846072081955452455941949 14942277030733294670978231)
        ·
          refine ⟨22413415546099942006467347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942277030733294670978231 22413415546099942006467347)
          ·
            refine ⟨33620123319149913009701021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22413415546099942006467347 33620123319149913009701021)
            ·
              refine ⟨12607546244681217378637883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33620123319149913009701021 12607546244681217378637883)
              ·
                refine ⟨18911319367021826067956825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607546244681217378637883 18911319367021826067956825)
                ·
                  refine ⟨14183489525266369550967619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911319367021826067956825 14183489525266369550967619)
                  ·
                    refine ⟨21275234287899554326451429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14183489525266369550967619 21275234287899554326451429)
                    ·
                      refine ⟨3989106428981166436209643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21275234287899554326451429 3989106428981166436209643)
                      ·
                        rfl

theorem cell23_7768757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7768757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768757 prefixEnd_7768757 := by exact prefixLift 7768757
  have htrace : WordTrace (prefixWord ++ tailWord_7768757) baseStart_7768757 baseEnd_7768757 := by
    simpa [prefixWord, tailWord_7768757, baseEnd_7768757] using wordTrace_append hprefix tailTrace_7768757
  have hstable : (prefixWord ++ tailWord_7768757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768757).length < 2 ^ (prefixWord ++ tailWord_7768757).sum := by decide
  have hdescent : baseEnd_7768757 < baseStart_7768757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768767 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 1, 4]
def baseStart_7768767 : Nat := 118140960795 + 7768767 * 2 ^ 59
def prefixEnd_7768767 : Nat := 4983230072969 + 3 ^ 40 * 7768767 * 2
def baseEnd_7768767 : Nat := 1329703854595903799028199

theorem tailTrace_7768767 : CollatzResearch.WordTrace tailWord_7768767 prefixEnd_7768767 1329703854595903799028199 := by
  unfold tailWord_7768767
  simp only [CollatzResearch.WordTrace]
  refine ⟨283350210646091433616784555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188900140430727622411189703 283350210646091433616784555)
  ·
    refine ⟨425025315969137150425176833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283350210646091433616784555 425025315969137150425176833)
    ·
      refine ⟨318768986976852862818882625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425025315969137150425176833 318768986976852862818882625)
      ·
        refine ⟨239076740232639647114161969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318768986976852862818882625 239076740232639647114161969)
        ·
          refine ⟨179307555174479735335621477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239076740232639647114161969 179307555174479735335621477)
          ·
            refine ⟨33620166595214950375429027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179307555174479735335621477 33620166595214950375429027)
            ·
              refine ⟨50430249892822425563143541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33620166595214950375429027 50430249892822425563143541)
              ·
                refine ⟨4727835927452102396544707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50430249892822425563143541 4727835927452102396544707)
                ·
                  refine ⟨7091753891178153594817061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727835927452102396544707 7091753891178153594817061)
                  ·
                    refine ⟨1329703854595903799028199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7091753891178153594817061 1329703854595903799028199)
                    ·
                      rfl

theorem cell23_7768767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_7768767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768767 prefixEnd_7768767 := by exact prefixLift 7768767
  have htrace : WordTrace (prefixWord ++ tailWord_7768767) baseStart_7768767 baseEnd_7768767 := by
    simpa [prefixWord, tailWord_7768767, baseEnd_7768767] using wordTrace_append hprefix tailTrace_7768767
  have hstable : (prefixWord ++ tailWord_7768767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768767).length < 2 ^ (prefixWord ++ tailWord_7768767).sum := by decide
  have hdescent : baseEnd_7768767 < baseStart_7768767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768780 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 8]
def baseStart_7768780 : Nat := 118140960795 + 7768780 * 2 ^ 59
def prefixEnd_7768780 : Nat := 4983230072969 + 3 ^ 40 * 7768780 * 2
def baseEnd_7768780 : Nat := 443235359892913316246893

theorem tailTrace_7768780 : CollatzResearch.WordTrace tailWord_7768780 prefixEnd_7768780 443235359892913316246893 := by
  unfold tailWord_7768780
  simp only [CollatzResearch.WordTrace]
  refine ⟨141675342397522168418503897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188900456530029557891338529 141675342397522168418503897)
  ·
    refine ⟨106256506798141626313877923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141675342397522168418503897 106256506798141626313877923)
    ·
      refine ⟨159384760197212439470816885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106256506798141626313877923 159384760197212439470816885)
      ·
        refine ⟨14942321268488666200389083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159384760197212439470816885 14942321268488666200389083)
        ·
          refine ⟨22413481902732999300583625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942321268488666200389083 22413481902732999300583625)
          ·
            refine ⟨16810111427049749475437719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22413481902732999300583625 16810111427049749475437719)
            ·
              refine ⟨25215167140574624213156579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16810111427049749475437719 25215167140574624213156579)
              ·
                refine ⟨37822750710861936319734869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25215167140574624213156579 37822750710861936319734869)
                ·
                  refine ⟨443235359892913316246893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37822750710861936319734869 443235359892913316246893)
                  ·
                    rfl

theorem cell23_7768780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_7768780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768780 prefixEnd_7768780 := by exact prefixLift 7768780
  have htrace : WordTrace (prefixWord ++ tailWord_7768780) baseStart_7768780 baseEnd_7768780 := by
    simpa [prefixWord, tailWord_7768780, baseEnd_7768780] using wordTrace_append hprefix tailTrace_7768780
  have hstable : (prefixWord ++ tailWord_7768780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768780).length < 2 ^ (prefixWord ++ tailWord_7768780).sum := by decide
  have hdescent : baseEnd_7768780 < baseStart_7768780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768817 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_7768817 : Nat := 118140960795 + 7768817 * 2 ^ 59
def prefixEnd_7768817 : Nat := 4983230072969 + 3 ^ 40 * 7768817 * 2
def baseEnd_7768817 : Nat := 3989137237820436201459367

theorem tailTrace_7768817 : CollatzResearch.WordTrace tailWord_7768817 prefixEnd_7768817 3989137237820436201459367 := by
  unfold tailWord_7768817
  simp only [CollatzResearch.WordTrace]
  refine ⟨283352034295910292156104705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188901356197273528104069803 283352034295910292156104705)
  ·
    refine ⟨212514025721932719117078529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283352034295910292156104705 212514025721932719117078529)
    ·
      refine ⟨159385519291449539337808897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212514025721932719117078529 159385519291449539337808897)
      ·
        refine ⟨119539139468587154503356673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159385519291449539337808897 119539139468587154503356673)
        ·
          refine ⟨89654354601440365877517505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119539139468587154503356673 89654354601440365877517505)
          ·
            refine ⟨67240765951080274408138129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89654354601440365877517505 67240765951080274408138129)
            ·
              refine ⟨50430574463310205806103597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67240765951080274408138129 50430574463310205806103597)
              ·
                refine ⟨18911465423741327177288849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50430574463310205806103597 18911465423741327177288849)
                ·
                  refine ⟨14183599067805995382966637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18911465423741327177288849 14183599067805995382966637)
                  ·
                    refine ⟨5318849650427248268612489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14183599067805995382966637 5318849650427248268612489)
                    ·
                      refine ⟨3989137237820436201459367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318849650427248268612489 3989137237820436201459367)
                      ·
                        rfl

theorem cell23_7768817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_7768817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768817 prefixEnd_7768817 := by exact prefixLift 7768817
  have htrace : WordTrace (prefixWord ++ tailWord_7768817) baseStart_7768817 baseEnd_7768817 := by
    simpa [prefixWord, tailWord_7768817, baseEnd_7768817] using wordTrace_append hprefix tailTrace_7768817
  have hstable : (prefixWord ++ tailWord_7768817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768817).length < 2 ^ (prefixWord ++ tailWord_7768817).sum := by decide
  have hdescent : baseEnd_7768817 < baseStart_7768817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768823 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 6]
def baseStart_7768823 : Nat := 118140960795 + 7768823 * 2 ^ 59
def prefixEnd_7768823 : Nat := 4983230072969 + 3 ^ 40 * 7768823 * 2
def baseEnd_7768823 : Nat := 1329713439568121059328113

theorem tailTrace_7768823 : CollatzResearch.WordTrace tailWord_7768823 prefixEnd_7768823 1329713439568121059328113 := by
  unfold tailWord_7768823
  simp only [CollatzResearch.WordTrace]
  refine ⟨283352253133888555180823123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188901502089259036787215415 283352253133888555180823123)
  ·
    refine ⟨425028379700832832771234685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283352253133888555180823123 425028379700832832771234685)
    ·
      refine ⟨159385642387812312289213007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425028379700832832771234685 159385642387812312289213007)
      ·
        refine ⟨239078463581718468433819511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159385642387812312289213007 239078463581718468433819511)
        ·
          refine ⟨358617695372577702650729267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239078463581718468433819511 358617695372577702650729267)
          ·
            refine ⟨537926543058866553976093901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358617695372577702650729267 537926543058866553976093901)
            ·
              refine ⟨201722453647074957741035213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537926543058866553976093901 201722453647074957741035213)
              ·
                refine ⟨75645920117653109152888205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201722453647074957741035213 75645920117653109152888205)
                ·
                  refine ⟨28367220044119915932333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75645920117653109152888205 28367220044119915932333077)
                  ·
                    refine ⟨1329713439568121059328113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28367220044119915932333077 1329713439568121059328113)
                    ·
                      rfl

theorem cell23_7768823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_7768823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768823 prefixEnd_7768823 := by exact prefixLift 7768823
  have htrace : WordTrace (prefixWord ++ tailWord_7768823) baseStart_7768823 baseEnd_7768823 := by
    simpa [prefixWord, tailWord_7768823, baseEnd_7768823] using wordTrace_append hprefix tailTrace_7768823
  have hstable : (prefixWord ++ tailWord_7768823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768823).length < 2 ^ (prefixWord ++ tailWord_7768823).sum := by decide
  have hdescent : baseEnd_7768823 < baseStart_7768823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768834 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_7768834 : Nat := 118140960795 + 7768834 * 2 ^ 59
def prefixEnd_7768834 : Nat := 4983230072969 + 3 ^ 40 * 7768834 * 2
def baseEnd_7768834 : Nat := 3989145966991562634946789

theorem tailTrace_7768834 : CollatzResearch.WordTrace tailWord_7768834 prefixEnd_7768834 3989145966991562634946789 := by
  unfold tailWord_7768834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70838163584212176014868389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188901769557899136039649037 70838163584212176014868389)
  ·
    refine ⟨13282155672039783002787823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70838163584212176014868389 13282155672039783002787823)
    ·
      refine ⟨19923233508059674504181735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13282155672039783002787823 19923233508059674504181735)
      ·
        refine ⟨29884850262089511756272603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19923233508059674504181735 29884850262089511756272603)
        ·
          refine ⟨44827275393134267634408905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29884850262089511756272603 44827275393134267634408905)
          ·
            refine ⟨33620456544850700725806679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44827275393134267634408905 33620456544850700725806679)
            ·
              refine ⟨50430684817276051088710019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33620456544850700725806679 50430684817276051088710019)
              ·
                refine ⟨75646027225914076633065029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50430684817276051088710019 75646027225914076633065029)
                ·
                  refine ⟨14183630104858889368699693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75646027225914076633065029 14183630104858889368699693)
                  ·
                    refine ⟨5318861289322083513262385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14183630104858889368699693 5318861289322083513262385)
                    ·
                      refine ⟨3989145966991562634946789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318861289322083513262385 3989145966991562634946789)
                      ·
                        rfl

theorem cell23_7768834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_7768834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768834 prefixEnd_7768834 := by exact prefixLift 7768834
  have htrace : WordTrace (prefixWord ++ tailWord_7768834) baseStart_7768834 baseEnd_7768834 := by
    simpa [prefixWord, tailWord_7768834, baseEnd_7768834] using wordTrace_append hprefix tailTrace_7768834
  have hstable : (prefixWord ++ tailWord_7768834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768834).length < 2 ^ (prefixWord ++ tailWord_7768834).sum := by decide
  have hdescent : baseEnd_7768834 < baseStart_7768834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768860 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7768860 : Nat := 118140960795 + 7768860 * 2 ^ 59
def prefixEnd_7768860 : Nat := 4983230072969 + 3 ^ 40 * 7768860 * 2
def baseEnd_7768860 : Nat := 3989159317488579533221669

theorem tailTrace_7768860 : CollatzResearch.WordTrace tailWord_7768860 prefixEnd_7768860 3989159317488579533221669 := by
  unfold tailWord_7768860
  simp only [CollatzResearch.WordTrace]
  refine ⟨141676801317377255249960017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188902401756503006999946689 141676801317377255249960017)
  ·
    refine ⟨106257600988032941437470013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141676801317377255249960017 106257600988032941437470013)
    ·
      refine ⟨39846600370512353039051255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106257600988032941437470013 39846600370512353039051255)
      ·
        refine ⟨59769900555768529558576883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39846600370512353039051255 59769900555768529558576883)
        ·
          refine ⟨89654850833652794337865325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59769900555768529558576883 89654850833652794337865325)
          ·
            refine ⟨33620569062619797876699497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89654850833652794337865325 33620569062619797876699497)
            ·
              refine ⟨25215426796964848407524623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33620569062619797876699497 25215426796964848407524623)
              ·
                refine ⟨37823140195447272611286935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25215426796964848407524623 37823140195447272611286935)
                ·
                  refine ⟨56734710293170908916930403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37823140195447272611286935 56734710293170908916930403)
                  ·
                    refine ⟨85102065439756363375395605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56734710293170908916930403 85102065439756363375395605)
                    ·
                      refine ⟨3989159317488579533221669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85102065439756363375395605 3989159317488579533221669)
                      ·
                        rfl

theorem cell23_7768860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7768860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768860 prefixEnd_7768860 := by exact prefixLift 7768860
  have htrace : WordTrace (prefixWord ++ tailWord_7768860) baseStart_7768860 baseEnd_7768860 := by
    simpa [prefixWord, tailWord_7768860, baseEnd_7768860] using wordTrace_append hprefix tailTrace_7768860
  have hstable : (prefixWord ++ tailWord_7768860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768860).length < 2 ^ (prefixWord ++ tailWord_7768860).sum := by decide
  have hdescent : baseEnd_7768860 < baseStart_7768860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768861 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7768861 : Nat := 118140960795 + 7768861 * 2 ^ 59
def prefixEnd_7768861 : Nat := 4983230072969 + 3 ^ 40 * 7768861 * 2
def baseEnd_7768861 : Nat := 1329719943656411343103055

theorem tailTrace_7768861 : CollatzResearch.WordTrace tailWord_7768861 prefixEnd_7768861 1329719943656411343103055 := by
  unfold tailWord_7768861
  simp only [CollatzResearch.WordTrace]
  refine ⟨283353639107750887670706437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188902426071833925113804291 283353639107750887670706437)
  ·
    refine ⟨53128807332703291438257457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283353639107750887670706437 53128807332703291438257457)
    ·
      refine ⟨39846605499527468578693093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53128807332703291438257457 39846605499527468578693093)
      ·
        refine ⟨7471238531161400358504955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39846605499527468578693093 7471238531161400358504955)
        ·
          refine ⟨11206857796742100537757433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471238531161400358504955 11206857796742100537757433)
          ·
            refine ⟨8405143347556575403318075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11206857796742100537757433 8405143347556575403318075)
            ·
              refine ⟨12607715021334863104977113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405143347556575403318075 12607715021334863104977113)
              ·
                refine ⟨9455786266001147328732835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12607715021334863104977113 9455786266001147328732835)
                ·
                  refine ⟨14183679399001720993099253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455786266001147328732835 14183679399001720993099253)
                  ·
                    refine ⟨1329719943656411343103055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14183679399001720993099253 1329719943656411343103055)
                    ·
                      rfl

theorem cell23_7768861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7768861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768861 prefixEnd_7768861 := by exact prefixLift 7768861
  have htrace : WordTrace (prefixWord ++ tailWord_7768861) baseStart_7768861 baseEnd_7768861 := by
    simpa [prefixWord, tailWord_7768861, baseEnd_7768861] using wordTrace_append hprefix tailTrace_7768861
  have hstable : (prefixWord ++ tailWord_7768861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768861).length < 2 ^ (prefixWord ++ tailWord_7768861).sum := by decide
  have hdescent : baseEnd_7768861 < baseStart_7768861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768864 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7768864 : Nat := 118140960795 + 7768864 * 2 ^ 59
def prefixEnd_7768864 : Nat := 4983230072969 + 3 ^ 40 * 7768864 * 2
def baseEnd_7768864 : Nat := 3989161371411197517571651

theorem tailTrace_7768864 : CollatzResearch.WordTrace tailWord_7768864 prefixEnd_7768864 3989161371411197517571651 := by
  unfold tailWord_7768864
  simp only [CollatzResearch.WordTrace]
  refine ⟨141676874263370009591532823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188902499017826679455377097 141676874263370009591532823)
  ·
    refine ⟨212515311395055014387299235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141676874263370009591532823 212515311395055014387299235)
    ·
      refine ⟨318772967092582521580948853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212515311395055014387299235 318772967092582521580948853)
      ·
        refine ⟨29884965664929611398213955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318772967092582521580948853 29884965664929611398213955)
        ·
          refine ⟨44827448497394417097320933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29884965664929611398213955 44827448497394417097320933)
          ·
            refine ⟨8405146593261453205747675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44827448497394417097320933 8405146593261453205747675)
            ·
              refine ⟨12607719889892179808621513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405146593261453205747675 12607719889892179808621513)
              ·
                refine ⟨9455789917419134856466135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12607719889892179808621513 9455789917419134856466135)
                ·
                  refine ⟨14183684876128702284699203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9455789917419134856466135 14183684876128702284699203)
                  ·
                    refine ⟨21275527314193053427048805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14183684876128702284699203 21275527314193053427048805)
                    ·
                      refine ⟨3989161371411197517571651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21275527314193053427048805 3989161371411197517571651)
                      ·
                        rfl

theorem cell23_7768864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7768864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768864 prefixEnd_7768864 := by exact prefixLift 7768864
  have htrace : WordTrace (prefixWord ++ tailWord_7768864) baseStart_7768864 baseEnd_7768864 := by
    simpa [prefixWord, tailWord_7768864, baseEnd_7768864] using wordTrace_append hprefix tailTrace_7768864
  have hstable : (prefixWord ++ tailWord_7768864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768864).length < 2 ^ (prefixWord ++ tailWord_7768864).sum := by decide
  have hdescent : baseEnd_7768864 < baseStart_7768864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_7768873 : Nat := 118140960795 + 7768873 * 2 ^ 59
def prefixEnd_7768873 : Nat := 4983230072969 + 3 ^ 40 * 7768873 * 2
def baseEnd_7768873 : Nat := 3989165992737087982359109

theorem tailTrace_7768873 : CollatzResearch.WordTrace tailWord_7768873 prefixEnd_7768873 3989165992737087982359109 := by
  unfold tailWord_7768873
  simp only [CollatzResearch.WordTrace]
  refine ⟨283354076783707413720143273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188902717855804942480095515 283354076783707413720143273)
  ·
    refine ⟨212515557587780560290107455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283354076783707413720143273 212515557587780560290107455)
    ·
      refine ⟨318773336381670840435161183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212515557587780560290107455 318773336381670840435161183)
      ·
        refine ⟨478160004572506260652741775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318773336381670840435161183 478160004572506260652741775)
        ·
          refine ⟨717240006858759390979112663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478160004572506260652741775 717240006858759390979112663)
          ·
            refine ⟨1075860010288139086468668995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717240006858759390979112663 1075860010288139086468668995)
            ·
              refine ⟨1613790015432208629703003493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075860010288139086468668995 1613790015432208629703003493)
              ·
                refine ⟨302585627893539118069313155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1613790015432208629703003493 302585627893539118069313155)
                ·
                  refine ⟨453878441840308677103969733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302585627893539118069313155 453878441840308677103969733)
                  ·
                    refine ⟨85102207845057876956994325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453878441840308677103969733 85102207845057876956994325)
                    ·
                      refine ⟨3989165992737087982359109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85102207845057876956994325 3989165992737087982359109)
                      ·
                        rfl

theorem cell23_7768873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_7768873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768873 prefixEnd_7768873 := by exact prefixLift 7768873
  have htrace : WordTrace (prefixWord ++ tailWord_7768873) baseStart_7768873 baseEnd_7768873 := by
    simpa [prefixWord, tailWord_7768873, baseEnd_7768873] using wordTrace_append hprefix tailTrace_7768873
  have hstable : (prefixWord ++ tailWord_7768873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768873).length < 2 ^ (prefixWord ++ tailWord_7768873).sum := by decide
  have hdescent : baseEnd_7768873 < baseStart_7768873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768874 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7768874 : Nat := 118140960795 + 7768874 * 2 ^ 59
def prefixEnd_7768874 : Nat := 4983230072969 + 3 ^ 40 * 7768874 * 2
def baseEnd_7768874 : Nat := 1329722168739247492815535

theorem tailTrace_7768874 : CollatzResearch.WordTrace tailWord_7768874 prefixEnd_7768874 1329722168739247492815535 := by
  unfold tailWord_7768874
  simp only [CollatzResearch.WordTrace]
  refine ⟨70838528314175947722732419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188902742171135860593953117 70838528314175947722732419)
  ·
    refine ⟨106257792471263921584098629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70838528314175947722732419 106257792471263921584098629)
    ·
      refine ⟨19923336088361985297018493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106257792471263921584098629 19923336088361985297018493)
      ·
        refine ⟨7471251033135744486381935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19923336088361985297018493 7471251033135744486381935)
        ·
          refine ⟨11206876549703616729572903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471251033135744486381935 11206876549703616729572903)
          ·
            refine ⟨16810314824555425094359355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206876549703616729572903 16810314824555425094359355)
            ·
              refine ⟨25215472236833137641539033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16810314824555425094359355 25215472236833137641539033)
              ·
                refine ⟨18911604177624853231154275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25215472236833137641539033 18911604177624853231154275)
                ·
                  refine ⟨28367406266437279846731413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18911604177624853231154275 28367406266437279846731413)
                  ·
                    refine ⟨1329722168739247492815535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28367406266437279846731413 1329722168739247492815535)
                    ·
                      rfl

theorem cell23_7768874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7768874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768874 prefixEnd_7768874 := by exact prefixLift 7768874
  have htrace : WordTrace (prefixWord ++ tailWord_7768874) baseStart_7768874 baseEnd_7768874 := by
    simpa [prefixWord, tailWord_7768874, baseEnd_7768874] using wordTrace_append hprefix tailTrace_7768874
  have hstable : (prefixWord ++ tailWord_7768874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768874).length < 2 ^ (prefixWord ++ tailWord_7768874).sum := by decide
  have hdescent : baseEnd_7768874 < baseStart_7768874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768881 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_7768881 : Nat := 118140960795 + 7768881 * 2 ^ 59
def prefixEnd_7768881 : Nat := 4983230072969 + 3 ^ 40 * 7768881 * 2
def baseEnd_7768881 : Nat := 3989170100582323951059073

theorem tailTrace_7768881 : CollatzResearch.WordTrace tailWord_7768881 prefixEnd_7768881 3989170100582323951059073 := by
  unfold tailWord_7768881
  simp only [CollatzResearch.WordTrace]
  refine ⟨283354368567678431086434497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188902912378452287390956331 283354368567678431086434497)
  ·
    refine ⟨212515776425758823314825873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283354368567678431086434497 212515776425758823314825873)
    ·
      refine ⟨159386832319319117486119405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212515776425758823314825873 159386832319319117486119405)
      ·
        refine ⟨59770062119744669057294777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159386832319319117486119405 59770062119744669057294777)
        ·
          refine ⟨44827546589808501792971083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59770062119744669057294777 44827546589808501792971083)
          ·
            refine ⟨67241319884712752689456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44827546589808501792971083 67241319884712752689456625)
            ·
              refine ⟨50430989913534564517092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67241319884712752689456625 50430989913534564517092469)
              ·
                refine ⟨4727905304393865423477419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50430989913534564517092469 4727905304393865423477419)
                ·
                  refine ⟨7091857956590798135216129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4727905304393865423477419 7091857956590798135216129)
                  ·
                    refine ⟨5318893467443098601412097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7091857956590798135216129 5318893467443098601412097)
                    ·
                      refine ⟨3989170100582323951059073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318893467443098601412097 3989170100582323951059073)
                      ·
                        rfl

theorem cell23_7768881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_7768881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768881 prefixEnd_7768881 := by exact prefixLift 7768881
  have htrace : WordTrace (prefixWord ++ tailWord_7768881) baseStart_7768881 baseEnd_7768881 := by
    simpa [prefixWord, tailWord_7768881, baseEnd_7768881] using wordTrace_append hprefix tailTrace_7768881
  have hstable : (prefixWord ++ tailWord_7768881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768881).length < 2 ^ (prefixWord ++ tailWord_7768881).sum := by decide
  have hdescent : baseEnd_7768881 < baseStart_7768881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768914 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_7768914 : Nat := 118140960795 + 7768914 * 2 ^ 59
def prefixEnd_7768914 : Nat := 4983230072969 + 3 ^ 40 * 7768914 * 2
def baseEnd_7768914 : Nat := 3989187045443922321946421

theorem tailTrace_7768914 : CollatzResearch.WordTrace tailWord_7768914 prefixEnd_7768914 3989187045443922321946421 := by
  unfold tailWord_7768914
  simp only [CollatzResearch.WordTrace]
  refine ⟨70838893044139719430596449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188903714784372585148257197 70838893044139719430596449)
  ·
    refine ⟨53129169783104789572947337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70838893044139719430596449 53129169783104789572947337)
    ·
      refine ⟨39846877337328592179710503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53129169783104789572947337 39846877337328592179710503)
      ·
        refine ⟨59770316005992888269565755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39846877337328592179710503 59770316005992888269565755)
        ·
          refine ⟨89655474008989332404348633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59770316005992888269565755 89655474008989332404348633)
          ·
            refine ⟨67241605506741999303261475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89655474008989332404348633 67241605506741999303261475)
            ·
              refine ⟨100862408260112998954892213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67241605506741999303261475 100862408260112998954892213)
              ·
                refine ⟨9455850774385593652021145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100862408260112998954892213 9455850774385593652021145)
                ·
                  refine ⟨7091888080789195239015859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455850774385593652021145 7091888080789195239015859)
                  ·
                    refine ⟨10637832121183792858523789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7091888080789195239015859 10637832121183792858523789)
                    ·
                      refine ⟨3989187045443922321946421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10637832121183792858523789 3989187045443922321946421)
                      ·
                        rfl

theorem cell23_7768914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_7768914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768914 prefixEnd_7768914 := by exact prefixLift 7768914
  have htrace : WordTrace (prefixWord ++ tailWord_7768914) baseStart_7768914 baseEnd_7768914 := by
    simpa [prefixWord, tailWord_7768914, baseEnd_7768914] using wordTrace_append hprefix tailTrace_7768914
  have hstable : (prefixWord ++ tailWord_7768914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768914).length < 2 ^ (prefixWord ++ tailWord_7768914).sum := by decide
  have hdescent : baseEnd_7768914 < baseStart_7768914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768940 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_7768940 : Nat := 118140960795 + 7768940 * 2 ^ 59
def prefixEnd_7768940 : Nat := 4983230072969 + 3 ^ 40 * 7768940 * 2
def baseEnd_7768940 : Nat := 3989200395940939220221301

theorem tailTrace_7768940 : CollatzResearch.WordTrace tailWord_7768940 prefixEnd_7768940 3989200395940939220221301 := by
  unfold tailWord_7768940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141678260237232342081416137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188904346982976456108554849 141678260237232342081416137)
  ·
    refine ⟨106258695177924256561062103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141678260237232342081416137 106258695177924256561062103)
    ·
      refine ⟨159388042766886384841593155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106258695177924256561062103 159388042766886384841593155)
      ·
        refine ⟨239082064150329577262389733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159388042766886384841593155 239082064150329577262389733)
        ·
          refine ⟨44827887028186795736698075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239082064150329577262389733 44827887028186795736698075)
          ·
            refine ⟨67241830542280193605047113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44827887028186795736698075 67241830542280193605047113)
            ·
              refine ⟨50431372906710145203785335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67241830542280193605047113 50431372906710145203785335)
              ·
                refine ⟨75647059360065217805678003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50431372906710145203785335 75647059360065217805678003)
                ·
                  refine ⟨113470589040097826708517005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75647059360065217805678003 113470589040097826708517005)
                  ·
                    refine ⟨42551470890036685015693877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113470589040097826708517005 42551470890036685015693877)
                    ·
                      refine ⟨3989200395940939220221301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42551470890036685015693877 3989200395940939220221301)
                      ·
                        rfl

theorem cell23_7768940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_7768940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768940 prefixEnd_7768940 := by exact prefixLift 7768940
  have htrace : WordTrace (prefixWord ++ tailWord_7768940) baseStart_7768940 baseEnd_7768940 := by
    simpa [prefixWord, tailWord_7768940, baseEnd_7768940] using wordTrace_append hprefix tailTrace_7768940
  have hstable : (prefixWord ++ tailWord_7768940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768940).length < 2 ^ (prefixWord ++ tailWord_7768940).sum := by decide
  have hdescent : baseEnd_7768940 < baseStart_7768940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768967 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7768967 : Nat := 118140960795 + 7768967 * 2 ^ 59
def prefixEnd_7768967 : Nat := 4983230072969 + 3 ^ 40 * 7768967 * 2
def baseEnd_7768967 : Nat := 3989214259918610614583677

theorem tailTrace_7768967 : CollatzResearch.WordTrace tailWord_7768967 prefixEnd_7768967 3989214259918610614583677 := by
  unfold tailWord_7768967
  simp only [CollatzResearch.WordTrace]
  refine ⟨283357505245366867774065155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188905003496911245182710103 283357505245366867774065155)
  ·
    refine ⟨425036257868050301661097733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283357505245366867774065155 425036257868050301661097733)
    ·
      refine ⟨79694298350259431561455825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425036257868050301661097733 79694298350259431561455825)
      ·
        refine ⟨59770723762694573671091869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79694298350259431561455825 59770723762694573671091869)
        ·
          refine ⟨22414021411010465126659451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59770723762694573671091869 22414021411010465126659451)
          ·
            refine ⟨33621032116515697689989177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414021411010465126659451 33621032116515697689989177)
            ·
              refine ⟨25215774087386773267491883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33621032116515697689989177 25215774087386773267491883)
              ·
                refine ⟨37823661131080159901237825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25215774087386773267491883 37823661131080159901237825)
                ·
                  refine ⟨28367745848310119925928369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37823661131080159901237825 28367745848310119925928369)
                  ·
                    refine ⟨21275809386232589944446277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28367745848310119925928369 21275809386232589944446277)
                    ·
                      refine ⟨3989214259918610614583677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21275809386232589944446277 3989214259918610614583677)
                      ·
                        rfl

theorem cell23_7768967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7768967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768967 prefixEnd_7768967 := by exact prefixLift 7768967
  have htrace : WordTrace (prefixWord ++ tailWord_7768967) baseStart_7768967 baseEnd_7768967 := by
    simpa [prefixWord, tailWord_7768967, baseEnd_7768967] using wordTrace_append hprefix tailTrace_7768967
  have hstable : (prefixWord ++ tailWord_7768967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768967).length < 2 ^ (prefixWord ++ tailWord_7768967).sum := by decide
  have hdescent : baseEnd_7768967 < baseStart_7768967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7768997 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_7768997 : Nat := 118140960795 + 7768997 * 2 ^ 59
def prefixEnd_7768997 : Nat := 4983230072969 + 3 ^ 40 * 7768997 * 2
def baseEnd_7768997 : Nat := 3989229664338245497208539

theorem tailTrace_7768997 : CollatzResearch.WordTrace tailWord_7768997 prefixEnd_7768997 3989229664338245497208539 := by
  unfold tailWord_7768997
  simp only [CollatzResearch.WordTrace]
  refine ⟨283358599435258182897657245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188905732956838788598438163 283358599435258182897657245)
  ·
    refine ⟨106259474788221818586621467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283358599435258182897657245 106259474788221818586621467)
    ·
      refine ⟨159389212182332727879932201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106259474788221818586621467 159389212182332727879932201)
      ·
        refine ⟨119541909136749545909949151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159389212182332727879932201 119541909136749545909949151)
        ·
          refine ⟨179312863705124318864923727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119541909136749545909949151 179312863705124318864923727)
          ·
            refine ⟨268969295557686478297385591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179312863705124318864923727 268969295557686478297385591)
            ·
              refine ⟨403453943336529717446078387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268969295557686478297385591 403453943336529717446078387)
              ·
                refine ⟨605180915004794576169117581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403453943336529717446078387 605180915004794576169117581)
                ·
                  refine ⟨226942843126797966063419093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605180915004794576169117581 226942843126797966063419093)
                  ·
                    refine ⟨5318972885784327329611385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226942843126797966063419093 5318972885784327329611385)
                    ·
                      refine ⟨3989229664338245497208539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5318972885784327329611385 3989229664338245497208539)
                      ·
                        rfl

theorem cell23_7768997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_7768997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7768997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7768997 prefixEnd_7768997 := by exact prefixLift 7768997
  have htrace : WordTrace (prefixWord ++ tailWord_7768997) baseStart_7768997 baseEnd_7768997 := by
    simpa [prefixWord, tailWord_7768997, baseEnd_7768997] using wordTrace_append hprefix tailTrace_7768997
  have hstable : (prefixWord ++ tailWord_7768997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7768997).length < 2 ^ (prefixWord ++ tailWord_7768997).sum := by decide
  have hdescent : baseEnd_7768997 < baseStart_7768997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7768997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769010 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_7769010 : Nat := 118140960795 + 7769010 * 2 ^ 59
def prefixEnd_7769010 : Nat := 4983230072969 + 3 ^ 40 * 7769010 * 2
def baseEnd_7769010 : Nat := 3989236339586753946345979

theorem tailTrace_7769010 : CollatzResearch.WordTrace tailWord_7769010 prefixEnd_7769010 3989236339586753946345979 := by
  unfold tailWord_7769010
  simp only [CollatzResearch.WordTrace]
  refine ⟨70839768396052771529470121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188906049056140724078586989 70839768396052771529470121)
  ·
    refine ⟨53129826297039578647102591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70839768396052771529470121 53129826297039578647102591)
    ·
      refine ⟨79694739445559367970653887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53129826297039578647102591 79694739445559367970653887)
      ·
        refine ⟨119542109168339051955980831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79694739445559367970653887 119542109168339051955980831)
        ·
          refine ⟨179313163752508577933971247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119542109168339051955980831 179313163752508577933971247)
          ·
            refine ⟨268969745628762866900956871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179313163752508577933971247 268969745628762866900956871)
            ·
              refine ⟨403454618443144300351435307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268969745628762866900956871 403454618443144300351435307)
              ·
                refine ⟨605181927664716450527152961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403454618443144300351435307 605181927664716450527152961)
                ·
                  refine ⟨453886445748537337895364721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605181927664716450527152961 453886445748537337895364721)
                  ·
                    refine ⟨340414834311403003421523541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453886445748537337895364721 340414834311403003421523541)
                    ·
                      refine ⟨3989236339586753946345979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340414834311403003421523541 3989236339586753946345979)
                      ·
                        rfl

theorem cell23_7769010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_7769010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769010 prefixEnd_7769010 := by exact prefixLift 7769010
  have htrace : WordTrace (prefixWord ++ tailWord_7769010) baseStart_7769010 baseEnd_7769010 := by
    simpa [prefixWord, tailWord_7769010, baseEnd_7769010] using wordTrace_append hprefix tailTrace_7769010
  have hstable : (prefixWord ++ tailWord_7769010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769010).length < 2 ^ (prefixWord ++ tailWord_7769010).sum := by decide
  have hdescent : baseEnd_7769010 < baseStart_7769010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769017 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7769017 : Nat := 118140960795 + 7769017 * 2 ^ 59
def prefixEnd_7769017 : Nat := 4983230072969 + 3 ^ 40 * 7769017 * 2
def baseEnd_7769017 : Nat := 3989239933951335418958447

theorem tailTrace_7769017 : CollatzResearch.WordTrace tailWord_7769017 prefixEnd_7769017 3989239933951335418958447 := by
  unfold tailWord_7769017
  simp only [CollatzResearch.WordTrace]
  refine ⟨283359328895185726313385305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188906219263457150875590203 283359328895185726313385305)
  ·
    refine ⟨212519496671389294735038979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283359328895185726313385305 212519496671389294735038979)
    ·
      refine ⟨318779245007083942102558469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212519496671389294735038979 318779245007083942102558469)
      ·
        refine ⟨59771108438828239144229713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318779245007083942102558469 59771108438828239144229713)
        ·
          refine ⟨44828331329121179358172285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59771108438828239144229713 44828331329121179358172285)
          ·
            refine ⟨16810624248420442259314607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44828331329121179358172285 16810624248420442259314607)
            ·
              refine ⟨25215936372630663388971911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16810624248420442259314607 25215936372630663388971911)
              ·
                refine ⟨37823904558945995083457867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25215936372630663388971911 37823904558945995083457867)
                ·
                  refine ⟨56735856838418992625186801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37823904558945995083457867 56735856838418992625186801)
                  ·
                    refine ⟨42551892628814244468890101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56735856838418992625186801 42551892628814244468890101)
                    ·
                      refine ⟨3989239933951335418958447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42551892628814244468890101 3989239933951335418958447)
                      ·
                        rfl

theorem cell23_7769017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7769017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769017 prefixEnd_7769017 := by exact prefixLift 7769017
  have htrace : WordTrace (prefixWord ++ tailWord_7769017) baseStart_7769017 baseEnd_7769017 := by
    simpa [prefixWord, tailWord_7769017, baseEnd_7769017] using wordTrace_append hprefix tailTrace_7769017
  have hstable : (prefixWord ++ tailWord_7769017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769017).length < 2 ^ (prefixWord ++ tailWord_7769017).sum := by decide
  have hdescent : baseEnd_7769017 < baseStart_7769017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769040 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_7769040 : Nat := 118140960795 + 7769040 * 2 ^ 59
def prefixEnd_7769040 : Nat := 4983230072969 + 3 ^ 40 * 7769040 * 2
def baseEnd_7769040 : Nat := 3989251744006388828970841

theorem tailTrace_7769040 : CollatzResearch.WordTrace tailWord_7769040 prefixEnd_7769040 3989251744006388828970841 := by
  unfold tailWord_7769040
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680083887051200620736287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188906778516068267494315049 141680083887051200620736287)
  ·
    refine ⟨212520125830576800931104431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141680083887051200620736287 212520125830576800931104431)
    ·
      refine ⟨318780188745865201396656647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212520125830576800931104431 318780188745865201396656647)
      ·
        refine ⟨478170283118797802094984971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318780188745865201396656647 478170283118797802094984971)
        ·
          refine ⟨717255424678196703142477457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478170283118797802094984971 717255424678196703142477457)
          ·
            refine ⟨537941568508647527356858093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717255424678196703142477457 537941568508647527356858093)
            ·
              refine ⟨201728088190742822758821785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537941568508647527356858093 201728088190742822758821785)
              ·
                refine ⟨151296066143057117069116339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201728088190742822758821785 151296066143057117069116339)
                ·
                  refine ⟨226944099214585675603674509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151296066143057117069116339 226944099214585675603674509)
                  ·
                    refine ⟨85104037205469628351377941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226944099214585675603674509 85104037205469628351377941)
                    ·
                      refine ⟨3989251744006388828970841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85104037205469628351377941 3989251744006388828970841)
                      ·
                        rfl

theorem cell23_7769040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_7769040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769040 prefixEnd_7769040 := by exact prefixLift 7769040
  have htrace : WordTrace (prefixWord ++ tailWord_7769040) baseStart_7769040 baseEnd_7769040 := by
    simpa [prefixWord, tailWord_7769040, baseEnd_7769040] using wordTrace_append hprefix tailTrace_7769040
  have hstable : (prefixWord ++ tailWord_7769040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769040).length < 2 ^ (prefixWord ++ tailWord_7769040).sum := by decide
  have hdescent : baseEnd_7769040 < baseStart_7769040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769044 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7769044 : Nat := 118140960795 + 7769044 * 2 ^ 59
def prefixEnd_7769044 : Nat := 4983230072969 + 3 ^ 40 * 7769044 * 2
def baseEnd_7769044 : Nat := 3989253797929006813320823

theorem tailTrace_7769044 : CollatzResearch.WordTrace tailWord_7769044 prefixEnd_7769044 3989253797929006813320823 := by
  unfold tailWord_7769044
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680156833043954962309093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188906875777391939949745457 141680156833043954962309093)
  ·
    refine ⟨26565029406195741555432955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141680156833043954962309093 26565029406195741555432955)
    ·
      refine ⟨39847544109293612333149433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26565029406195741555432955 39847544109293612333149433)
      ·
        refine ⟨29885658081970209249862075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39847544109293612333149433 29885658081970209249862075)
        ·
          refine ⟨44828487122955313874793113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29885658081970209249862075 44828487122955313874793113)
          ·
            refine ⟨33621365342216485406094835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44828487122955313874793113 33621365342216485406094835)
            ·
              refine ⟨50432048013324728109142253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33621365342216485406094835 50432048013324728109142253)
              ·
                refine ⟨18912018004996773040928345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50432048013324728109142253 18912018004996773040928345)
                ·
                  refine ⟨14184013503747579780696259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18912018004996773040928345 14184013503747579780696259)
                  ·
                    refine ⟨21276020255621369671044389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14184013503747579780696259 21276020255621369671044389)
                    ·
                      refine ⟨3989253797929006813320823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21276020255621369671044389 3989253797929006813320823)
                      ·
                        rfl

theorem cell23_7769044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7769044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769044 prefixEnd_7769044 := by exact prefixLift 7769044
  have htrace : WordTrace (prefixWord ++ tailWord_7769044) baseStart_7769044 baseEnd_7769044 := by
    simpa [prefixWord, tailWord_7769044, baseEnd_7769044] using wordTrace_append hprefix tailTrace_7769044
  have hstable : (prefixWord ++ tailWord_7769044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769044).length < 2 ^ (prefixWord ++ tailWord_7769044).sum := by decide
  have hdescent : baseEnd_7769044 < baseStart_7769044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769064 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7769064 : Nat := 118140960795 + 7769064 * 2 ^ 59
def prefixEnd_7769064 : Nat := 4983230072969 + 3 ^ 40 * 7769064 * 2
def baseEnd_7769064 : Nat := 3989264067542096735070731

theorem tailTrace_7769064 : CollatzResearch.WordTrace tailWord_7769064 prefixEnd_7769064 3989264067542096735070731 := by
  unfold tailWord_7769064
  simp only [CollatzResearch.WordTrace]
  refine ⟨141680521563007726670173123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188907362084010302226897497 141680521563007726670173123)
  ·
    refine ⟨212520782344511590005259685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141680521563007726670173123 212520782344511590005259685)
    ·
      refine ⟨39847646689595923125986191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212520782344511590005259685 39847646689595923125986191)
      ·
        refine ⟨59771470034393884688979287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39847646689595923125986191 59771470034393884688979287)
        ·
          refine ⟨89657205051590827033468931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59771470034393884688979287 89657205051590827033468931)
          ·
            refine ⟨134485807577386240550203397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89657205051590827033468931 134485807577386240550203397)
            ·
              refine ⟨25216088920759920103163137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134485807577386240550203397 25216088920759920103163137)
              ·
                refine ⟨18912066690569940077372353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25216088920759920103163137 18912066690569940077372353)
                ·
                  refine ⟨14184050017927455058029265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18912066690569940077372353 14184050017927455058029265)
                  ·
                    refine ⟨10638037513445591293521949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14184050017927455058029265 10638037513445591293521949)
                    ·
                      refine ⟨3989264067542096735070731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10638037513445591293521949 3989264067542096735070731)
                      ·
                        rfl

theorem cell23_7769064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7769064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769064 prefixEnd_7769064 := by exact prefixLift 7769064
  have htrace : WordTrace (prefixWord ++ tailWord_7769064) baseStart_7769064 baseEnd_7769064 := by
    simpa [prefixWord, tailWord_7769064, baseEnd_7769064] using wordTrace_append hprefix tailTrace_7769064
  have hstable : (prefixWord ++ tailWord_7769064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769064).length < 2 ^ (prefixWord ++ tailWord_7769064).sum := by decide
  have hdescent : baseEnd_7769064 < baseStart_7769064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769071 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 1, 4]
def baseStart_7769071 : Nat := 118140960795 + 7769071 * 2 ^ 59
def prefixEnd_7769071 : Nat := 4983230072969 + 3 ^ 40 * 7769071 * 2
def baseEnd_7769071 : Nat := 1329755887302226069227733

theorem tailTrace_7769071 : CollatzResearch.WordTrace tailWord_7769071 prefixEnd_7769071 1329755887302226069227733 := by
  unfold tailWord_7769071
  simp only [CollatzResearch.WordTrace]
  refine ⟨283361298436990093535851067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188907532291326729023900711 283361298436990093535851067)
  ·
    refine ⟨425041947655485140303776601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283361298436990093535851067 425041947655485140303776601)
    ·
      refine ⟨318781460741613855227832451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425041947655485140303776601 318781460741613855227832451)
      ·
        refine ⟨478172191112420782841748677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318781460741613855227832451 478172191112420782841748677)
        ·
          refine ⟨89657285833578896782827877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478172191112420782841748677 89657285833578896782827877)
          ·
            refine ⟨16810741093796043146780227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89657285833578896782827877 16810741093796043146780227)
            ·
              refine ⟨25216111640694064720170341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16810741093796043146780227 25216111640694064720170341)
              ·
                refine ⟨4728020932630137135031939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25216111640694064720170341 4728020932630137135031939)
                ·
                  refine ⟨7092031398945205702547909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728020932630137135031939 7092031398945205702547909)
                  ·
                    refine ⟨1329755887302226069227733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092031398945205702547909 1329755887302226069227733)
                    ·
                      rfl

theorem cell23_7769071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_7769071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769071 prefixEnd_7769071 := by exact prefixLift 7769071
  have htrace : WordTrace (prefixWord ++ tailWord_7769071) baseStart_7769071 baseEnd_7769071 := by
    simpa [prefixWord, tailWord_7769071, baseEnd_7769071] using wordTrace_append hprefix tailTrace_7769071
  have hstable : (prefixWord ++ tailWord_7769071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769071).length < 2 ^ (prefixWord ++ tailWord_7769071).sum := by decide
  have hdescent : baseEnd_7769071 < baseStart_7769071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769114 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_7769114 : Nat := 118140960795 + 7769114 * 2 ^ 59
def prefixEnd_7769114 : Nat := 4983230072969 + 3 ^ 40 * 7769114 * 2
def baseEnd_7769114 : Nat := 1329763247191607179815167

theorem tailTrace_7769114 : CollatzResearch.WordTrace tailWord_7769114 prefixEnd_7769114 1329763247191607179815167 := by
  unfold tailWord_7769114
  simp only [CollatzResearch.WordTrace]
  refine ⟨70840716693958577969916599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188908577850556207919777597 70840716693958577969916599)
  ·
    refine ⟨106261075040937866954874899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70840716693958577969916599 106261075040937866954874899)
    ·
      refine ⟨159391612561406800432312349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106261075040937866954874899 159391612561406800432312349)
      ·
        refine ⟨59771854710527550162117131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159391612561406800432312349 59771854710527550162117131)
        ·
          refine ⟨89657782065791325243175697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59771854710527550162117131 89657782065791325243175697)
          ·
            refine ⟨67243336549343493932381773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89657782065791325243175697 67243336549343493932381773)
            ·
              refine ⟨25216251206003810224643165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67243336549343493932381773 25216251206003810224643165)
              ·
                refine ⟨9456094202251428834241187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25216251206003810224643165 9456094202251428834241187)
                ·
                  refine ⟨14184141303377143251361781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456094202251428834241187 14184141303377143251361781)
                  ·
                    refine ⟨1329763247191607179815167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14184141303377143251361781 1329763247191607179815167)
                    ·
                      rfl

theorem cell23_7769114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_7769114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769114 prefixEnd_7769114 := by exact prefixLift 7769114
  have htrace : WordTrace (prefixWord ++ tailWord_7769114) baseStart_7769114 baseEnd_7769114 := by
    simpa [prefixWord, tailWord_7769114, baseEnd_7769114] using wordTrace_append hprefix tailTrace_7769114
  have hstable : (prefixWord ++ tailWord_7769114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769114).length < 2 ^ (prefixWord ++ tailWord_7769114).sum := by decide
  have hdescent : baseEnd_7769114 < baseStart_7769114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769144 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_7769144 : Nat := 118140960795 + 7769144 * 2 ^ 59
def prefixEnd_7769144 : Nat := 4983230072969 + 3 ^ 40 * 7769144 * 2
def baseEnd_7769144 : Nat := 1329768381998152140690121

theorem tailTrace_7769144 : CollatzResearch.WordTrace tailWord_7769144 prefixEnd_7769144 1329768381998152140690121 := by
  unfold tailWord_7769144
  simp only [CollatzResearch.WordTrace]
  refine ⟨141681980482862813501629243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188909307310483751335505657 141681980482862813501629243)
  ·
    refine ⟨212522970724294220252443865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141681980482862813501629243 212522970724294220252443865)
    ·
      refine ⟨159392228043220665189332899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212522970724294220252443865 159392228043220665189332899)
      ·
        refine ⟨239088342064830997783999349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159392228043220665189332899 239088342064830997783999349)
        ·
          refine ⟨22414532068577906042249939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239088342064830997783999349 22414532068577906042249939)
          ·
            refine ⟨33621798102866859063374909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414532068577906042249939 33621798102866859063374909)
            ·
              refine ⟨12608174288575072148765591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33621798102866859063374909 12608174288575072148765591)
              ·
                refine ⟨18912261432862608223148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608174288575072148765591 18912261432862608223148387)
                ·
                  refine ⟨28368392149293912334722581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18912261432862608223148387 28368392149293912334722581)
                  ·
                    refine ⟨1329768381998152140690121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28368392149293912334722581 1329768381998152140690121)
                    ·
                      rfl

theorem cell23_7769144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_7769144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769144 prefixEnd_7769144 := by exact prefixLift 7769144
  have htrace : WordTrace (prefixWord ++ tailWord_7769144) baseStart_7769144 baseEnd_7769144 := by
    simpa [prefixWord, tailWord_7769144, baseEnd_7769144] using wordTrace_append hprefix tailTrace_7769144
  have hstable : (prefixWord ++ tailWord_7769144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769144).length < 2 ^ (prefixWord ++ tailWord_7769144).sum := by decide
  have hdescent : baseEnd_7769144 < baseStart_7769144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769187 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 7]
def baseStart_7769187 : Nat := 118140960795 + 7769187 * 2 ^ 59
def prefixEnd_7769187 : Nat := 4983230072969 + 3 ^ 40 * 7769187 * 2
def baseEnd_7769187 : Nat := 1329775741887533251277555

theorem tailTrace_7769187 : CollatzResearch.WordTrace tailWord_7769187 prefixEnd_7769187 1329775741887533251277555 := by
  unfold tailWord_7769187
  simp only [CollatzResearch.WordTrace]
  refine ⟨283365529304569845347073815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188910352869713230231382543 283365529304569845347073815)
  ·
    refine ⟨425048293956854768020610723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283365529304569845347073815 425048293956854768020610723)
    ·
      refine ⟨637572440935282152030916085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425048293956854768020610723 637572440935282152030916085)
      ·
        refine ⟨59772416337682701752898383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 637572440935282152030916085 59772416337682701752898383)
        ·
          refine ⟨89658624506524052629347575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59772416337682701752898383 89658624506524052629347575)
          ·
            refine ⟨134487936759786078944021363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89658624506524052629347575 134487936759786078944021363)
            ·
              refine ⟨201731905139679118416032045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134487936759786078944021363 201731905139679118416032045)
              ·
                refine ⟨75649464427379669406012017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201731905139679118416032045 75649464427379669406012017)
                ·
                  refine ⟨56737098320534752054509013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75649464427379669406012017 56737098320534752054509013)
                  ·
                    refine ⟨1329775741887533251277555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56737098320534752054509013 1329775741887533251277555)
                    ·
                      rfl

theorem cell23_7769187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_7769187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769187 prefixEnd_7769187 := by exact prefixLift 7769187
  have htrace : WordTrace (prefixWord ++ tailWord_7769187) baseStart_7769187 baseEnd_7769187 := by
    simpa [prefixWord, tailWord_7769187, baseEnd_7769187] using wordTrace_append hprefix tailTrace_7769187
  have hstable : (prefixWord ++ tailWord_7769187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769187).length < 2 ^ (prefixWord ++ tailWord_7769187).sum := by decide
  have hdescent : baseEnd_7769187 < baseStart_7769187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769257 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_7769257 : Nat := 118140960795 + 7769257 * 2 ^ 59
def prefixEnd_7769257 : Nat := 4983230072969 + 3 ^ 40 * 7769257 * 2
def baseEnd_7769257 : Nat := 3989363169308414479957343

theorem tailTrace_7769257 : CollatzResearch.WordTrace tailWord_7769257 prefixEnd_7769257 3989363169308414479957343 := by
  unfold tailWord_7769257
  simp only [CollatzResearch.WordTrace]
  refine ⟨283368082414316247302122025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188912054942877498201414683 283368082414316247302122025)
  ·
    refine ⟨212526061810737185476591519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283368082414316247302122025 212526061810737185476591519)
    ·
      refine ⟨318789092716105778214887279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212526061810737185476591519 318789092716105778214887279)
      ·
        refine ⟨478183639074158667322330919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318789092716105778214887279 478183639074158667322330919)
        ·
          refine ⟨717275458611238000983496379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478183639074158667322330919 717275458611238000983496379)
          ·
            refine ⟨1075913187916857001475244569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717275458611238000983496379 1075913187916857001475244569)
            ·
              refine ⟨806934890937642751106433427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075913187916857001475244569 806934890937642751106433427)
              ·
                refine ⟨1210402336406464126659650141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806934890937642751106433427 1210402336406464126659650141)
                ·
                  refine ⟨453900876152424047497368803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210402336406464126659650141 453900876152424047497368803)
                  ·
                    refine ⟨680851314228636071246053205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 453900876152424047497368803 680851314228636071246053205)
                    ·
                      refine ⟨3989363169308414479957343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 680851314228636071246053205 3989363169308414479957343)
                      ·
                        rfl

theorem cell23_7769257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_7769257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769257 prefixEnd_7769257 := by exact prefixLift 7769257
  have htrace : WordTrace (prefixWord ++ tailWord_7769257) baseStart_7769257 baseEnd_7769257 := by
    simpa [prefixWord, tailWord_7769257, baseEnd_7769257] using wordTrace_append hprefix tailTrace_7769257
  have hstable : (prefixWord ++ tailWord_7769257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769257).length < 2 ^ (prefixWord ++ tailWord_7769257).sum := by decide
  have hdescent : baseEnd_7769257 < baseStart_7769257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769274 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_7769274 : Nat := 118140960795 + 7769274 * 2 ^ 59
def prefixEnd_7769274 : Nat := 4983230072969 + 3 ^ 40 * 7769274 * 2
def baseEnd_7769274 : Nat := 3989371898479540913444765

theorem tailTrace_7769274 : CollatzResearch.WordTrace tailWord_7769274 prefixEnd_7769274 3989371898479540913444765 := by
  unfold tailWord_7769274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70842175613813664801372719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188912468303503106136993917 70842175613813664801372719)
  ·
    refine ⟨106263263420720497202059079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70842175613813664801372719 106263263420720497202059079)
    ·
      refine ⟨159394895131080745803088619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106263263420720497202059079 159394895131080745803088619)
      ·
        refine ⟨239092342696621118704632929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159394895131080745803088619 239092342696621118704632929)
        ·
          refine ⟨179319257022465839028474697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239092342696621118704632929 179319257022465839028474697)
          ·
            refine ⟨134489442766849379271356023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179319257022465839028474697 134489442766849379271356023)
            ·
              refine ⟨201734164150274068907034035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134489442766849379271356023 201734164150274068907034035)
              ·
                refine ⟨302601246225411103360551053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201734164150274068907034035 302601246225411103360551053)
                ·
                  refine ⟨113475467334529163760206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302601246225411103360551053 113475467334529163760206645)
                  ·
                    refine ⟨10638325062612109102519373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113475467334529163760206645 10638325062612109102519373)
                    ·
                      refine ⟨3989371898479540913444765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10638325062612109102519373 3989371898479540913444765)
                      ·
                        rfl

theorem cell23_7769274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_7769274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769274 prefixEnd_7769274 := by exact prefixLift 7769274
  have htrace : WordTrace (prefixWord ++ tailWord_7769274) baseStart_7769274 baseEnd_7769274 := by
    simpa [prefixWord, tailWord_7769274, baseEnd_7769274] using wordTrace_append hprefix tailTrace_7769274
  have hstable : (prefixWord ++ tailWord_7769274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769274).length < 2 ^ (prefixWord ++ tailWord_7769274).sum := by decide
  have hdescent : baseEnd_7769274 < baseStart_7769274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769286 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7769286 : Nat := 118140960795 + 7769286 * 2 ^ 59
def prefixEnd_7769286 : Nat := 4983230072969 + 3 ^ 40 * 7769286 * 2
def baseEnd_7769286 : Nat := 3989378060247394866494711

theorem tailTrace_7769286 : CollatzResearch.WordTrace tailWord_7769286 prefixEnd_7769286 3989378060247394866494711 := by
  unfold tailWord_7769286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855285629100349539216491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188912760087474123503285141 8855285629100349539216491)
  ·
    refine ⟨13282928443650524308824737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855285629100349539216491 13282928443650524308824737)
    ·
      refine ⟨9962196332737893231618553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13282928443650524308824737 9962196332737893231618553)
      ·
        refine ⟨7471647249553419923713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9962196332737893231618553 7471647249553419923713915)
        ·
          refine ⟨11207470874330129885570873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471647249553419923713915 11207470874330129885570873)
          ·
            refine ⟨8405603155747597414178155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207470874330129885570873 8405603155747597414178155)
            ·
              refine ⟨12608404733621396121267233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405603155747597414178155 12608404733621396121267233)
              ·
                refine ⟨9456303550216047090950425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608404733621396121267233 9456303550216047090950425)
                ·
                  refine ⟨7092227662662035318212819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456303550216047090950425 7092227662662035318212819)
                  ·
                    refine ⟨10638341493993052977319229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092227662662035318212819 10638341493993052977319229)
                    ·
                      refine ⟨3989378060247394866494711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10638341493993052977319229 3989378060247394866494711)
                      ·
                        rfl

theorem cell23_7769286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7769286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769286 prefixEnd_7769286 := by exact prefixLift 7769286
  have htrace : WordTrace (prefixWord ++ tailWord_7769286) baseStart_7769286 baseEnd_7769286 := by
    simpa [prefixWord, tailWord_7769286, baseEnd_7769286] using wordTrace_append hprefix tailTrace_7769286
  have hstable : (prefixWord ++ tailWord_7769286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769286).length < 2 ^ (prefixWord ++ tailWord_7769286).sum := by decide
  have hdescent : baseEnd_7769286 < baseStart_7769286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769309 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7769309 : Nat := 118140960795 + 7769309 * 2 ^ 59
def prefixEnd_7769309 : Nat := 4983230072969 + 3 ^ 40 * 7769309 * 2
def baseEnd_7769309 : Nat := 3989389870302448276507105

theorem tailTrace_7769309 : CollatzResearch.WordTrace tailWord_7769309 prefixEnd_7769309 3989389870302448276507105 := by
  unfold tailWord_7769309
  simp only [CollatzResearch.WordTrace]
  refine ⟨283369979010127860183014981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188913319340085240122009987 283369979010127860183014981)
  ·
    refine ⟨53131871064398973784315309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283369979010127860183014981 53131871064398973784315309)
    ·
      refine ⟨19924451649149615169118241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53131871064398973784315309 19924451649149615169118241)
      ·
        refine ⟨14943338736862211376838681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19924451649149615169118241 14943338736862211376838681)
        ·
          refine ⟨11207504052646658532629011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14943338736862211376838681 11207504052646658532629011)
          ·
            refine ⟨16811256078969987798943517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207504052646658532629011 16811256078969987798943517)
            ·
              refine ⟨6304221029613745424603819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16811256078969987798943517 6304221029613745424603819)
              ·
                refine ⟨9456331544420618136905729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304221029613745424603819 9456331544420618136905729)
                ·
                  refine ⟨7092248658315463602679297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456331544420618136905729 7092248658315463602679297)
                  ·
                    refine ⟨5319186493736597702009473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092248658315463602679297 5319186493736597702009473)
                    ·
                      refine ⟨3989389870302448276507105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319186493736597702009473 3989389870302448276507105)
                      ·
                        rfl

theorem cell23_7769309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7769309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769309 prefixEnd_7769309 := by exact prefixLift 7769309
  have htrace : WordTrace (prefixWord ++ tailWord_7769309) baseStart_7769309 baseEnd_7769309 := by
    simpa [prefixWord, tailWord_7769309, baseEnd_7769309] using wordTrace_append hprefix tailTrace_7769309
  have hstable : (prefixWord ++ tailWord_7769309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769309).length < 2 ^ (prefixWord ++ tailWord_7769309).sum := by decide
  have hdescent : baseEnd_7769309 < baseStart_7769309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769348 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7769348 : Nat := 118140960795 + 7769348 * 2 ^ 59
def prefixEnd_7769348 : Nat := 4983230072969 + 3 ^ 40 * 7769348 * 2
def baseEnd_7769348 : Nat := 3989409896047973623919425

theorem tailTrace_7769348 : CollatzResearch.WordTrace tailWord_7769348 prefixEnd_7769348 3989409896047973623919425 := by
  unfold tailWord_7769348
  simp only [CollatzResearch.WordTrace]
  refine ⟨141685700728493284921842349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188914267637991046562456465 141685700728493284921842349)
  ·
    refine ⟨53132137773184981845690881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141685700728493284921842349 53132137773184981845690881)
    ·
      refine ⟨39849103329888736384268161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53132137773184981845690881 39849103329888736384268161)
      ·
        refine ⟨29886827497416552288201121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39849103329888736384268161 29886827497416552288201121)
        ·
          refine ⟨22415120623062414216150841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29886827497416552288201121 22415120623062414216150841)
          ·
            refine ⟨16811340467296810662113131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22415120623062414216150841 16811340467296810662113131)
            ·
              refine ⟨25217010700945215993169697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16811340467296810662113131 25217010700945215993169697)
              ·
                refine ⟨18912758025708911994877273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25217010700945215993169697 18912758025708911994877273)
                ·
                  refine ⟨14184568519281683996157955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18912758025708911994877273 14184568519281683996157955)
                  ·
                    refine ⟨21276852778922525994236933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14184568519281683996157955 21276852778922525994236933)
                    ·
                      refine ⟨3989409896047973623919425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21276852778922525994236933 3989409896047973623919425)
                      ·
                        rfl

theorem cell23_7769348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7769348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769348 prefixEnd_7769348 := by exact prefixLift 7769348
  have htrace : WordTrace (prefixWord ++ tailWord_7769348) baseStart_7769348 baseEnd_7769348 := by
    simpa [prefixWord, tailWord_7769348, baseEnd_7769348] using wordTrace_append hprefix tailTrace_7769348
  have hstable : (prefixWord ++ tailWord_7769348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769348).length < 2 ^ (prefixWord ++ tailWord_7769348).sum := by decide
  have hdescent : baseEnd_7769348 < baseStart_7769348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769358 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_7769358 : Nat := 118140960795 + 7769358 * 2 ^ 59
def prefixEnd_7769358 : Nat := 4983230072969 + 3 ^ 40 * 7769358 * 2
def baseEnd_7769358 : Nat := 1329805010284839528264793

theorem tailTrace_7769358 : CollatzResearch.WordTrace tailWord_7769358 prefixEnd_7769358 1329805010284839528264793 := by
  unfold tailWord_7769358
  simp only [CollatzResearch.WordTrace]
  refine ⟨35421470773368792693943591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188914510791300227701032485 35421470773368792693943591)
  ·
    refine ⟨53132206160053189040915387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35421470773368792693943591 53132206160053189040915387)
    ·
      refine ⟨79698309240079783561373081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53132206160053189040915387 79698309240079783561373081)
      ·
        refine ⟨59773731930059837671029811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79698309240079783561373081 59773731930059837671029811)
        ·
          refine ⟨89660597895089756506544717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59773731930059837671029811 89660597895089756506544717)
          ·
            refine ⟨33622724210658658689954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89660597895089756506544717 33622724210658658689954269)
            ·
              refine ⟨12608521578996997008732851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33622724210658658689954269 12608521578996997008732851)
              ·
                refine ⟨18912782368495495513099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608521578996997008732851 18912782368495495513099277)
                ·
                  refine ⟨7092293388185810817412229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18912782368495495513099277 7092293388185810817412229)
                  ·
                    refine ⟨1329805010284839528264793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092293388185810817412229 1329805010284839528264793)
                    ·
                      rfl

theorem cell23_7769358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_7769358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769358 prefixEnd_7769358 := by exact prefixLift 7769358
  have htrace : WordTrace (prefixWord ++ tailWord_7769358) baseStart_7769358 baseEnd_7769358 := by
    simpa [prefixWord, tailWord_7769358, baseEnd_7769358] using wordTrace_append hprefix tailTrace_7769358
  have hstable : (prefixWord ++ tailWord_7769358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769358).length < 2 ^ (prefixWord ++ tailWord_7769358).sum := by decide
  have hdescent : baseEnd_7769358 < baseStart_7769358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769405 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 6]
def baseStart_7769405 : Nat := 118140960795 + 7769405 * 2 ^ 59
def prefixEnd_7769405 : Nat := 4983230072969 + 3 ^ 40 * 7769405 * 2
def baseEnd_7769405 : Nat := 443271018271697766767407

theorem tailTrace_7769405 : CollatzResearch.WordTrace tailWord_7769405 prefixEnd_7769405 443271018271697766767407 := by
  unfold tailWord_7769405
  simp only [CollatzResearch.WordTrace]
  refine ⟨283373480417780068578509669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188915653611853379052339779 283373480417780068578509669)
  ·
    refine ⟨53132527578333762858470563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283373480417780068578509669 53132527578333762858470563)
    ·
      refine ⟨79698791367500644287705845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53132527578333762858470563 79698791367500644287705845)
      ·
        refine ⟨7471761690703185401972423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79698791367500644287705845 7471761690703185401972423)
        ·
          refine ⟨11207642536054778102958635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471761690703185401972423 11207642536054778102958635)
          ·
            refine ⟨16811463804082167154437953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207642536054778102958635 16811463804082167154437953)
            ·
              refine ⟨12608597853061625365828465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16811463804082167154437953 12608597853061625365828465)
              ·
                refine ⟨9456448389796219024371349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608597853061625365828465 9456448389796219024371349)
                ·
                  refine ⟨443271018271697766767407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9456448389796219024371349 443271018271697766767407)
                  ·
                    rfl

theorem cell23_7769405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_7769405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769405 prefixEnd_7769405 := by exact prefixLift 7769405
  have htrace : WordTrace (prefixWord ++ tailWord_7769405) baseStart_7769405 baseEnd_7769405 := by
    simpa [prefixWord, tailWord_7769405, baseEnd_7769405] using wordTrace_append hprefix tailTrace_7769405
  have hstable : (prefixWord ++ tailWord_7769405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769405).length < 2 ^ (prefixWord ++ tailWord_7769405).sum := by decide
  have hdescent : baseEnd_7769405 < baseStart_7769405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769408 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2]
def baseStart_7769408 : Nat := 118140960795 + 7769408 * 2 ^ 59
def prefixEnd_7769408 : Nat := 4983230072969 + 3 ^ 40 * 7769408 * 2
def baseEnd_7769408 : Nat := 3989440704887243389169149

theorem tailTrace_7769408 : CollatzResearch.WordTrace tailWord_7769408 prefixEnd_7769408 3989440704887243389169149 := by
  unfold tailWord_7769408
  simp only [CollatzResearch.WordTrace]
  refine ⟨141686794918384600045434439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188915726557846133393912585 141686794918384600045434439)
  ·
    refine ⟨212530192377576900068151659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141686794918384600045434439 212530192377576900068151659)
    ·
      refine ⟨318795288566365350102227489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212530192377576900068151659 318795288566365350102227489)
      ·
        refine ⟨239096466424774012576670617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318795288566365350102227489 239096466424774012576670617)
        ·
          refine ⟨179322349818580509432502963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239096466424774012576670617 179322349818580509432502963)
          ·
            refine ⟨268983524727870764148754445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179322349818580509432502963 268983524727870764148754445)
            ·
              refine ⟨100868821772951536555782917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268983524727870764148754445 100868821772951536555782917)
              ·
                refine ⟨18912904082428413104209297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100868821772951536555782917 18912904082428413104209297)
                ·
                  refine ⟨14184678061821309828156973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18912904082428413104209297 14184678061821309828156973)
                  ·
                    refine ⟨5319254273182991185558865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14184678061821309828156973 5319254273182991185558865)
                    ·
                      refine ⟨3989440704887243389169149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319254273182991185558865 3989440704887243389169149)
                      ·
                        rfl

theorem cell23_7769408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_7769408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769408 prefixEnd_7769408 := by exact prefixLift 7769408
  have htrace : WordTrace (prefixWord ++ tailWord_7769408) baseStart_7769408 baseEnd_7769408 := by
    simpa [prefixWord, tailWord_7769408, baseEnd_7769408] using wordTrace_append hprefix tailTrace_7769408
  have hstable : (prefixWord ++ tailWord_7769408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769408).length < 2 ^ (prefixWord ++ tailWord_7769408).sum := by decide
  have hdescent : baseEnd_7769408 < baseStart_7769408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769409 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7769409 : Nat := 118140960795 + 7769409 * 2 ^ 59
def prefixEnd_7769409 : Nat := 4983230072969 + 3 ^ 40 * 7769409 * 2
def baseEnd_7769409 : Nat := 1329813739455965961752215

theorem tailTrace_7769409 : CollatzResearch.WordTrace tailWord_7769409 prefixEnd_7769409 1329813739455965961752215 := by
  unfold tailWord_7769409
  simp only [CollatzResearch.WordTrace]
  refine ⟨283373626309765577261655281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188915750873177051507770187 283373626309765577261655281)
  ·
    refine ⟨212530219732324182946241461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283373626309765577261655281 212530219732324182946241461)
    ·
      refine ⟨19924708099905392151210137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212530219732324182946241461 19924708099905392151210137)
      ·
        refine ⟨14943531074929044113407603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19924708099905392151210137 14943531074929044113407603)
        ·
          refine ⟨22415296612393566170111405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14943531074929044113407603 22415296612393566170111405)
          ·
            refine ⟨8405736229647587313791777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22415296612393566170111405 8405736229647587313791777)
            ·
              refine ⟨6304302172235690485343833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405736229647587313791777 6304302172235690485343833)
              ·
                refine ⟨4728226629176767864007875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304302172235690485343833 4728226629176767864007875)
                ·
                  refine ⟨7092339943765151796011813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728226629176767864007875 7092339943765151796011813)
                  ·
                    refine ⟨1329813739455965961752215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092339943765151796011813 1329813739455965961752215)
                    ·
                      rfl

theorem cell23_7769409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7769409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769409 prefixEnd_7769409 := by exact prefixLift 7769409
  have htrace : WordTrace (prefixWord ++ tailWord_7769409) baseStart_7769409 baseEnd_7769409 := by
    simpa [prefixWord, tailWord_7769409, baseEnd_7769409] using wordTrace_append hprefix tailTrace_7769409
  have hstable : (prefixWord ++ tailWord_7769409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769409).length < 2 ^ (prefixWord ++ tailWord_7769409).sum := by decide
  have hdescent : baseEnd_7769409 < baseStart_7769409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769431 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 6]
def baseStart_7769431 : Nat := 118140960795 + 7769431 * 2 ^ 59
def prefixEnd_7769431 : Nat := 4983230072969 + 3 ^ 40 * 7769431 * 2
def baseEnd_7769431 : Nat := 1329817504980765599727181

theorem tailTrace_7769431 : CollatzResearch.WordTrace tailWord_7769431 prefixEnd_7769431 1329817504980765599727181 := by
  unfold tailWord_7769431
  simp only [CollatzResearch.WordTrace]
  refine ⟨283374428715685875018956147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188916285810457250012637431 283374428715685875018956147)
  ·
    refine ⟨425061643073528812528434221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283374428715685875018956147 425061643073528812528434221)
    ·
      refine ⟨159398116152573304698162833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425061643073528812528434221 159398116152573304698162833)
      ·
        refine ⟨119548587114429978523622125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159398116152573304698162833 119548587114429978523622125)
        ·
          refine ⟨44830720167911241946358297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119548587114429978523622125 44830720167911241946358297)
          ·
            refine ⟨33623040125933431459768723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44830720167911241946358297 33623040125933431459768723)
            ·
              refine ⟨50434560188900147189653085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33623040125933431459768723 50434560188900147189653085)
              ·
                refine ⟨18912960070837555196119907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50434560188900147189653085 18912960070837555196119907)
                ·
                  refine ⟨28369440106256332794179861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18912960070837555196119907 28369440106256332794179861)
                  ·
                    refine ⟨1329817504980765599727181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28369440106256332794179861 1329817504980765599727181)
                    ·
                      rfl

theorem cell23_7769431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_7769431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769431 prefixEnd_7769431 := by exact prefixLift 7769431
  have htrace : WordTrace (prefixWord ++ tailWord_7769431) baseStart_7769431 baseEnd_7769431 := by
    simpa [prefixWord, tailWord_7769431, baseEnd_7769431] using wordTrace_append hprefix tailTrace_7769431
  have hstable : (prefixWord ++ tailWord_7769431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769431).length < 2 ^ (prefixWord ++ tailWord_7769431).sum := by decide
  have hdescent : baseEnd_7769431 < baseStart_7769431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769492 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7769492 : Nat := 118140960795 + 7769492 * 2 ^ 59
def prefixEnd_7769492 : Nat := 4983230072969 + 3 ^ 40 * 7769492 * 2
def baseEnd_7769492 : Nat := 3989483837262221060518763

theorem tailTrace_7769492 : CollatzResearch.WordTrace tailWord_7769492 prefixEnd_7769492 3989483837262221060518763 := by
  unfold tailWord_7769492
  simp only [CollatzResearch.WordTrace]
  refine ⟨141688326784232441218463365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188917769045643254957951153 141688326784232441218463365)
  ·
    refine ⟨26566561272043582728461881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141688326784232441218463365 26566561272043582728461881)
    ·
      refine ⟨19924920954032687046346411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26566561272043582728461881 19924920954032687046346411)
      ·
        refine ⟨29887381431049030569519617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19924920954032687046346411 29887381431049030569519617)
        ·
          refine ⟨22415536073286772927139713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29887381431049030569519617 22415536073286772927139713)
          ·
            refine ⟨16811652054965079695354785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22415536073286772927139713 16811652054965079695354785)
            ·
              refine ⟨12608739041223809771516089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16811652054965079695354785 12608739041223809771516089)
              ·
                refine ⟨9456554280917857328637067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608739041223809771516089 9456554280917857328637067)
                ·
                  refine ⟨14184831421376785992955601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456554280917857328637067 14184831421376785992955601)
                  ·
                    refine ⟨10638623566032589494716701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14184831421376785992955601 10638623566032589494716701)
                    ·
                      refine ⟨3989483837262221060518763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10638623566032589494716701 3989483837262221060518763)
                      ·
                        rfl

theorem cell23_7769492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7769492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769492 prefixEnd_7769492 := by exact prefixLift 7769492
  have htrace : WordTrace (prefixWord ++ tailWord_7769492) baseStart_7769492 baseEnd_7769492 := by
    simpa [prefixWord, tailWord_7769492, baseEnd_7769492] using wordTrace_append hprefix tailTrace_7769492
  have hstable : (prefixWord ++ tailWord_7769492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769492).length < 2 ^ (prefixWord ++ tailWord_7769492).sum := by decide
  have hdescent : baseEnd_7769492 < baseStart_7769492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769506 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7769506 : Nat := 118140960795 + 7769506 * 2 ^ 59
def prefixEnd_7769506 : Nat := 4983230072969 + 3 ^ 40 * 7769506 * 2
def baseEnd_7769506 : Nat := 3989491025991384005743699

theorem tailTrace_7769506 : CollatzResearch.WordTrace tailWord_7769506 prefixEnd_7769506 3989491025991384005743699 := by
  unfold tailWord_7769506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70844291047603540706984093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188918109460276108551957581 70844291047603540706984093)
  ·
    refine ⟨26566609142851327765119035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70844291047603540706984093 26566609142851327765119035)
    ·
      refine ⟨39849913714276991647678553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26566609142851327765119035 39849913714276991647678553)
      ·
        refine ⟨29887435285707743735758915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39849913714276991647678553 29887435285707743735758915)
        ·
          refine ⟨44831152928561615603638373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29887435285707743735758915 44831152928561615603638373)
          ·
            refine ⟨8405841174105302925682195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44831152928561615603638373 8405841174105302925682195)
            ·
              refine ⟨12608761761157954388523293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405841174105302925682195 12608761761157954388523293)
              ·
                refine ⟨4728285660434232895696235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12608761761157954388523293 4728285660434232895696235)
                ·
                  refine ⟨7092428490651349343544353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728285660434232895696235 7092428490651349343544353)
                  ·
                    refine ⟨5319321367988512007658265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092428490651349343544353 5319321367988512007658265)
                    ·
                      refine ⟨3989491025991384005743699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319321367988512007658265 3989491025991384005743699)
                      ·
                        rfl

theorem cell23_7769506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7769506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769506 prefixEnd_7769506 := by exact prefixLift 7769506
  have htrace : WordTrace (prefixWord ++ tailWord_7769506) baseStart_7769506 baseEnd_7769506 := by
    simpa [prefixWord, tailWord_7769506, baseEnd_7769506] using wordTrace_append hprefix tailTrace_7769506
  have hstable : (prefixWord ++ tailWord_7769506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769506).length < 2 ^ (prefixWord ++ tailWord_7769506).sum := by decide
  have hdescent : baseEnd_7769506 < baseStart_7769506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769548 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7769548 : Nat := 118140960795 + 7769548 * 2 ^ 59
def prefixEnd_7769548 : Nat := 4983230072969 + 3 ^ 40 * 7769548 * 2
def baseEnd_7769548 : Nat := 3989512592178872841418505

theorem tailTrace_7769548 : CollatzResearch.WordTrace tailWord_7769548 prefixEnd_7769548 3989512592178872841418505 := by
  unfold tailWord_7769548
  simp only [CollatzResearch.WordTrace]
  refine ⟨141689348028131002000482649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188919130704174669333976865 141689348028131002000482649)
  ·
    refine ⟨106267011021098251500361987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141689348028131002000482649 106267011021098251500361987)
    ·
      refine ⟨159400516531647377250542981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106267011021098251500361987 159400516531647377250542981)
      ·
        refine ⟨29887596849683883234476809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159400516531647377250542981 29887596849683883234476809)
        ·
          refine ⟨22415697637262912425857607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29887596849683883234476809 22415697637262912425857607)
          ·
            refine ⟨33623546455894368638786411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22415697637262912425857607 33623546455894368638786411)
            ·
              refine ⟨50435319683841552958179617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33623546455894368638786411 50435319683841552958179617)
              ·
                refine ⟨37826489762881164718634713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50435319683841552958179617 37826489762881164718634713)
                ·
                  refine ⟨28369867322160873538976035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37826489762881164718634713 28369867322160873538976035)
                  ·
                    refine ⟨42554800983241310308464053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28369867322160873538976035 42554800983241310308464053)
                    ·
                      refine ⟨3989512592178872841418505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42554800983241310308464053 3989512592178872841418505)
                      ·
                        rfl

theorem cell23_7769548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7769548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769548 prefixEnd_7769548 := by exact prefixLift 7769548
  have htrace : WordTrace (prefixWord ++ tailWord_7769548) baseStart_7769548 baseEnd_7769548 := by
    simpa [prefixWord, tailWord_7769548, baseEnd_7769548] using wordTrace_append hprefix tailTrace_7769548
  have hstable : (prefixWord ++ tailWord_7769548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769548).length < 2 ^ (prefixWord ++ tailWord_7769548).sum := by decide
  have hdescent : baseEnd_7769548 < baseStart_7769548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769551 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 7]
def baseStart_7769551 : Nat := 118140960795 + 7769551 * 2 ^ 59
def prefixEnd_7769551 : Nat := 4983230072969 + 3 ^ 40 * 7769551 * 2
def baseEnd_7769551 : Nat := 443279348068981814408999

theorem tailTrace_7769551 : CollatzResearch.WordTrace tailWord_7769551 prefixEnd_7769551 443279348068981814408999 := by
  unfold tailWord_7769551
  simp only [CollatzResearch.WordTrace]
  refine ⟨283378805475251135513324507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188919203650167423675549671 283378805475251135513324507)
  ·
    refine ⟨425068208212876703269986761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283378805475251135513324507 425068208212876703269986761)
    ·
      refine ⟨318801156159657527452490071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425068208212876703269986761 318801156159657527452490071)
      ·
        refine ⟨478201734239486291178735107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318801156159657527452490071 478201734239486291178735107)
        ·
          refine ⟨717302601359229436768102661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478201734239486291178735107 717302601359229436768102661)
          ·
            refine ⟨134494237754855519394019249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717302601359229436768102661 134494237754855519394019249)
            ·
              refine ⟨100870678316141639545514437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134494237754855519394019249 100870678316141639545514437)
              ·
                refine ⟨18913252184276557414783957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100870678316141639545514437 18913252184276557414783957)
                ·
                  refine ⟨443279348068981814408999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18913252184276557414783957 443279348068981814408999)
                  ·
                    rfl

theorem cell23_7769551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 7].length) (baseStart_7769551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769551 prefixEnd_7769551 := by exact prefixLift 7769551
  have htrace : WordTrace (prefixWord ++ tailWord_7769551) baseStart_7769551 baseEnd_7769551 := by
    simpa [prefixWord, tailWord_7769551, baseEnd_7769551] using wordTrace_append hprefix tailTrace_7769551
  have hstable : (prefixWord ++ tailWord_7769551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769551).length < 2 ^ (prefixWord ++ tailWord_7769551).sum := by decide
  have hdescent : baseEnd_7769551 < baseStart_7769551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769585 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 5]
def baseStart_7769585 : Nat := 118140960795 + 7769585 * 2 ^ 59
def prefixEnd_7769585 : Nat := 4983230072969 + 3 ^ 40 * 7769585 * 2
def baseEnd_7769585 : Nat := 443281287884787688517315

theorem tailTrace_7769585 : CollatzResearch.WordTrace tailWord_7769585 prefixEnd_7769585 443281287884787688517315 := by
  unfold tailWord_7769585
  simp only [CollatzResearch.WordTrace]
  refine ⟨283380045557127959320062209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188920030371418639546708139 283380045557127959320062209)
  ·
    refine ⟨212535034167845969490046657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283380045557127959320062209 212535034167845969490046657)
    ·
      refine ⟨159401275625884477117534993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212535034167845969490046657 159401275625884477117534993)
      ·
        refine ⟨119550956719413357838151245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159401275625884477117534993 119550956719413357838151245)
        ·
          refine ⟨44831608769780009189306717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119550956719413357838151245 44831608769780009189306717)
          ·
            refine ⟨16811853288667503445990019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44831608769780009189306717 16811853288667503445990019)
            ·
              refine ⟨25217779933001255168985029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16811853288667503445990019 25217779933001255168985029)
              ·
                refine ⟨4728333737437735344184693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25217779933001255168985029 4728333737437735344184693)
                ·
                  refine ⟨443281287884787688517315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4728333737437735344184693 443281287884787688517315)
                  ·
                    rfl

theorem cell23_7769585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 5].length) (baseStart_7769585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769585 prefixEnd_7769585 := by exact prefixLift 7769585
  have htrace : WordTrace (prefixWord ++ tailWord_7769585) baseStart_7769585 baseEnd_7769585 := by
    simpa [prefixWord, tailWord_7769585, baseEnd_7769585] using wordTrace_append hprefix tailTrace_7769585
  have hstable : (prefixWord ++ tailWord_7769585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769585).length < 2 ^ (prefixWord ++ tailWord_7769585).sum := by decide
  have hdescent : baseEnd_7769585 < baseStart_7769585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769591 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_7769591 : Nat := 118140960795 + 7769591 * 2 ^ 59
def prefixEnd_7769591 : Nat := 4983230072969 + 3 ^ 40 * 7769591 * 2
def baseEnd_7769591 : Nat := 3989534671847016173180807

theorem tailTrace_7769591 : CollatzResearch.WordTrace tailWord_7769591 prefixEnd_7769591 3989534671847016173180807 := by
  unfold tailWord_7769591
  simp only [CollatzResearch.WordTrace]
  refine ⟨283380264395106222344780627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188920176263404148229853751 283380264395106222344780627)
  ·
    refine ⟨425070396592659333517170941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283380264395106222344780627 425070396592659333517170941)
    ·
      refine ⟨159401398722247250068939103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425070396592659333517170941 159401398722247250068939103)
      ·
        refine ⟨239102098083370875103408655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159401398722247250068939103 239102098083370875103408655)
        ·
          refine ⟨358653147125056312655112983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239102098083370875103408655 358653147125056312655112983)
          ·
            refine ⟨537979720687584468982669475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358653147125056312655112983 537979720687584468982669475)
            ·
              refine ⟨806969581031376703474004213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537979720687584468982669475 806969581031376703474004213)
              ·
                refine ⟨75653398221691565950687895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806969581031376703474004213 75653398221691565950687895)
                ·
                  refine ⟨113480097332537348926031843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75653398221691565950687895 113480097332537348926031843)
                  ·
                    refine ⟨170220145998806023389047765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113480097332537348926031843 170220145998806023389047765)
                    ·
                      refine ⟨3989534671847016173180807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170220145998806023389047765 3989534671847016173180807)
                      ·
                        rfl

theorem cell23_7769591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_7769591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769591 prefixEnd_7769591 := by exact prefixLift 7769591
  have htrace : WordTrace (prefixWord ++ tailWord_7769591) baseStart_7769591 baseEnd_7769591 := by
    simpa [prefixWord, tailWord_7769591, baseEnd_7769591] using wordTrace_append hprefix tailTrace_7769591
  have hstable : (prefixWord ++ tailWord_7769591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769591).length < 2 ^ (prefixWord ++ tailWord_7769591).sum := by decide
  have hdescent : baseEnd_7769591 < baseStart_7769591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769686 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7769686 : Nat := 118140960795 + 7769686 * 2 ^ 59
def prefixEnd_7769686 : Nat := 4983230072969 + 3 ^ 40 * 7769686 * 2
def baseEnd_7769686 : Nat := 3989583452509193301492871

theorem tailTrace_7769686 : CollatzResearch.WordTrace tailWord_7769686 prefixEnd_7769686 3989583452509193301492871 := by
  unfold tailWord_7769686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711483083110128348093057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188922486219841369046325941 17711483083110128348093057)
  ·
    refine ⟨13283612312332596261069793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17711483083110128348093057 13283612312332596261069793)
    ·
      refine ⟨9962709234249447195802345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13283612312332596261069793 9962709234249447195802345)
      ·
        refine ⟨7472031925687085396851759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9962709234249447195802345 7472031925687085396851759)
        ·
          refine ⟨11208047888530628095277639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472031925687085396851759 11208047888530628095277639)
          ·
            refine ⟨16812071832795942142916459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11208047888530628095277639 16812071832795942142916459)
            ·
              refine ⟨25218107749193913214374689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16812071832795942142916459 25218107749193913214374689)
              ·
                refine ⟨18913580811895434910781017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25218107749193913214374689 18913580811895434910781017)
                ·
                  refine ⟨14185185608921576183085763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18913580811895434910781017 14185185608921576183085763)
                  ·
                    refine ⟨21277778413382364274628645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14185185608921576183085763 21277778413382364274628645)
                    ·
                      refine ⟨3989583452509193301492871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21277778413382364274628645 3989583452509193301492871)
                      ·
                        rfl

theorem cell23_7769686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7769686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769686 prefixEnd_7769686 := by exact prefixLift 7769686
  have htrace : WordTrace (prefixWord ++ tailWord_7769686) baseStart_7769686 baseEnd_7769686 := by
    simpa [prefixWord, tailWord_7769686, baseEnd_7769686] using wordTrace_append hprefix tailTrace_7769686
  have hstable : (prefixWord ++ tailWord_7769686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769686).length < 2 ^ (prefixWord ++ tailWord_7769686).sum := by decide
  have hdescent : baseEnd_7769686 < baseStart_7769686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769688 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_7769688 : Nat := 118140960795 + 7769688 * 2 ^ 59
def prefixEnd_7769688 : Nat := 4983230072969 + 3 ^ 40 * 7769688 * 2
def baseEnd_7769688 : Nat := 1329861493156834097889287

theorem tailTrace_7769688 : CollatzResearch.WordTrace tailWord_7769688 prefixEnd_7769688 1329861493156834097889287 := by
  unfold tailWord_7769688
  simp only [CollatzResearch.WordTrace]
  refine ⟨141691901137877403955530859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188922534850503205274041145 141691901137877403955530859)
  ·
    refine ⟨212537851706816105933296289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141691901137877403955530859 212537851706816105933296289)
    ·
      refine ⟨159403388780112079449972217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212537851706816105933296289 159403388780112079449972217)
      ·
        refine ⟨119552541585084059587479163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159403388780112079449972217 119552541585084059587479163)
        ·
          refine ⟨179328812377626089381218745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119552541585084059587479163 179328812377626089381218745)
          ·
            refine ⟨134496609283219567035914059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179328812377626089381218745 134496609283219567035914059)
            ·
              refine ⟨201744913924829350553871089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134496609283219567035914059 201744913924829350553871089)
              ·
                refine ⟨151308685443622012915403317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201744913924829350553871089 151308685443622012915403317)
                ·
                  refine ⟨14185189260339563710819061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151308685443622012915403317 14185189260339563710819061)
                  ·
                    refine ⟨1329861493156834097889287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14185189260339563710819061 1329861493156834097889287)
                    ·
                      rfl

theorem cell23_7769688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_7769688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769688 prefixEnd_7769688 := by exact prefixLift 7769688
  have htrace : WordTrace (prefixWord ++ tailWord_7769688) baseStart_7769688 baseEnd_7769688 := by
    simpa [prefixWord, tailWord_7769688, baseEnd_7769688] using wordTrace_append hprefix tailTrace_7769688
  have hstable : (prefixWord ++ tailWord_7769688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769688).length < 2 ^ (prefixWord ++ tailWord_7769688).sum := by decide
  have hdescent : baseEnd_7769688 < baseStart_7769688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769708 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_7769708 : Nat := 118140960795 + 7769708 * 2 ^ 59
def prefixEnd_7769708 : Nat := 4983230072969 + 3 ^ 40 * 7769708 * 2
def baseEnd_7769708 : Nat := 3989594749083592215417769

theorem tailTrace_7769708 : CollatzResearch.WordTrace tailWord_7769708 prefixEnd_7769708 3989594749083592215417769 := by
  unfold tailWord_7769708
  simp only [CollatzResearch.WordTrace]
  refine ⟨141692265867841175663394889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188923021157121567551193185 141692265867841175663394889)
  ·
    refine ⟨106269199400880881747546167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141692265867841175663394889 106269199400880881747546167)
    ·
      refine ⟨159403799101321322621319251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106269199400880881747546167 159403799101321322621319251)
      ·
        refine ⟨239105698651981983931978877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159403799101321322621319251 239105698651981983931978877)
        ·
          refine ⟨89664636994493243974492079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239105698651981983931978877 89664636994493243974492079)
          ·
            refine ⟨134496955491739865961738119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89664636994493243974492079 134496955491739865961738119)
            ·
              refine ⟨201745433237609798942607179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134496955491739865961738119 201745433237609798942607179)
              ·
                refine ⟨302618149856414698413910769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201745433237609798942607179 302618149856414698413910769)
                ·
                  refine ⟨226963612392311023810433077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302618149856414698413910769 226963612392311023810433077)
                  ·
                    refine ⟨21277838661779158482228101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226963612392311023810433077 21277838661779158482228101)
                    ·
                      refine ⟨3989594749083592215417769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21277838661779158482228101 3989594749083592215417769)
                      ·
                        rfl

theorem cell23_7769708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_7769708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769708 prefixEnd_7769708 := by exact prefixLift 7769708
  have htrace : WordTrace (prefixWord ++ tailWord_7769708) baseStart_7769708 baseEnd_7769708 := by
    simpa [prefixWord, tailWord_7769708, baseEnd_7769708] using wordTrace_append hprefix tailTrace_7769708
  have hstable : (prefixWord ++ tailWord_7769708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769708).length < 2 ^ (prefixWord ++ tailWord_7769708).sum := by decide
  have hdescent : baseEnd_7769708 < baseStart_7769708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769709 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 6]
def baseStart_7769709 : Nat := 118140960795 + 7769709 * 2 ^ 59
def prefixEnd_7769709 : Nat := 4983230072969 + 3 ^ 40 * 7769709 * 2
def baseEnd_7769709 : Nat := 443288362507138523500585

theorem tailTrace_7769709 : CollatzResearch.WordTrace tailWord_7769709 prefixEnd_7769709 443288362507138523500585 := by
  unfold tailWord_7769709
  simp only [CollatzResearch.WordTrace]
  refine ⟨283384568208678728497576181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188923045472452485665050787 283384568208678728497576181)
  ·
    refine ⟨26567303269563630796647767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283384568208678728497576181 26567303269563630796647767)
    ·
      refine ⟨39850954904345446194971651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26567303269563630796647767 39850954904345446194971651)
      ·
        refine ⟨59776432356518169292457477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39850954904345446194971651 59776432356518169292457477)
        ·
          refine ⟨11208081066847156742335777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59776432356518169292457477 11208081066847156742335777)
          ·
            refine ⟨8406060800135367556751833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11208081066847156742335777 8406060800135367556751833)
            ·
              refine ⟨6304545600101525667563875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406060800135367556751833 6304545600101525667563875)
              ·
                refine ⟨9456818400152288501345813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304545600101525667563875 9456818400152288501345813)
                ·
                  refine ⟨443288362507138523500585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9456818400152288501345813 443288362507138523500585)
                  ·
                    rfl

theorem cell23_7769709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_7769709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769709 prefixEnd_7769709 := by exact prefixLift 7769709
  have htrace : WordTrace (prefixWord ++ tailWord_7769709) baseStart_7769709 baseEnd_7769709 := by
    simpa [prefixWord, tailWord_7769709, baseEnd_7769709] using wordTrace_append hprefix tailTrace_7769709
  have hstable : (prefixWord ++ tailWord_7769709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769709).length < 2 ^ (prefixWord ++ tailWord_7769709).sum := by decide
  have hdescent : baseEnd_7769709 < baseStart_7769709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769729 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7769729 : Nat := 118140960795 + 7769729 * 2 ^ 59
def prefixEnd_7769729 : Nat := 4983230072969 + 3 ^ 40 * 7769729 * 2
def baseEnd_7769729 : Nat := 3989605532177336633255173

theorem tailTrace_7769729 : CollatzResearch.WordTrace tailWord_7769729 prefixEnd_7769729 3989605532177336633255173 := by
  unfold tailWord_7769729
  simp only [CollatzResearch.WordTrace]
  refine ⟨283385297668606271913304241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188923531779070847942202827 283385297668606271913304241)
  ·
    refine ⟨212538973251454703934978181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283385297668606271913304241 212538973251454703934978181)
    ·
      refine ⟨39851057484647756987808409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212538973251454703934978181 39851057484647756987808409)
      ·
        refine ⟨29888293113485817740856307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39851057484647756987808409 29888293113485817740856307)
        ·
          refine ⟨44832439670228726611284461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29888293113485817740856307 44832439670228726611284461)
          ·
            refine ⟨16812164876335772479231673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44832439670228726611284461 16812164876335772479231673)
            ·
              refine ⟨12609123657251829359423755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16812164876335772479231673 12609123657251829359423755)
              ·
                refine ⟨18913685485877744039135633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609123657251829359423755 18913685485877744039135633)
                ·
                  refine ⟨14185264114408308029351725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18913685485877744039135633 14185264114408308029351725)
                  ·
                    refine ⟨5319474042903115511006897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14185264114408308029351725 5319474042903115511006897)
                    ·
                      refine ⟨3989605532177336633255173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5319474042903115511006897 3989605532177336633255173)
                      ·
                        rfl

theorem cell23_7769729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7769729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769729 prefixEnd_7769729 := by exact prefixLift 7769729
  have htrace : WordTrace (prefixWord ++ tailWord_7769729) baseStart_7769729 baseEnd_7769729 := by
    simpa [prefixWord, tailWord_7769729, baseEnd_7769729] using wordTrace_append hprefix tailTrace_7769729
  have hstable : (prefixWord ++ tailWord_7769729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769729).length < 2 ^ (prefixWord ++ tailWord_7769729).sum := by decide
  have hdescent : baseEnd_7769729 < baseStart_7769729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769735 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 6]
def baseStart_7769735 : Nat := 118140960795 + 7769735 * 2 ^ 59
def prefixEnd_7769735 : Nat := 4983230072969 + 3 ^ 40 * 7769735 * 2
def baseEnd_7769735 : Nat := 1329869537687087869926715

theorem tailTrace_7769735 : CollatzResearch.WordTrace tailWord_7769735 prefixEnd_7769735 1329869537687087869926715 := by
  unfold tailWord_7769735
  simp only [CollatzResearch.WordTrace]
  refine ⟨283385516506584534938022659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188923677671056356625348439 283385516506584534938022659)
  ·
    refine ⟨425078274759876802407033989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283385516506584534938022659 425078274759876802407033989)
    ·
      refine ⟨79702176517476900451318873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425078274759876802407033989 79702176517476900451318873)
      ·
        refine ⟨59776632388107675338489155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79702176517476900451318873 59776632388107675338489155)
        ·
          refine ⟨89664948582161513007733733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59776632388107675338489155 89664948582161513007733733)
          ·
            refine ⟨16812177859155283688950075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89664948582161513007733733 16812177859155283688950075)
            ·
              refine ⟨25218266788732925533425113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16812177859155283688950075 25218266788732925533425113)
              ·
                refine ⟨18913700091549694150068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25218266788732925533425113 18913700091549694150068835)
                ·
                  refine ⟨28370550137324541225103253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18913700091549694150068835 28370550137324541225103253)
                  ·
                    refine ⟨1329869537687087869926715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28370550137324541225103253 1329869537687087869926715)
                    ·
                      rfl

theorem cell23_7769735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_7769735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769735 prefixEnd_7769735 := by exact prefixLift 7769735
  have htrace : WordTrace (prefixWord ++ tailWord_7769735) baseStart_7769735 baseEnd_7769735 := by
    simpa [prefixWord, tailWord_7769735, baseEnd_7769735] using wordTrace_append hprefix tailTrace_7769735
  have hstable : (prefixWord ++ tailWord_7769735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769735).length < 2 ^ (prefixWord ++ tailWord_7769735).sum := by decide
  have hdescent : baseEnd_7769735 < baseStart_7769735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769752 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_7769752 : Nat := 118140960795 + 7769752 * 2 ^ 59
def prefixEnd_7769752 : Nat := 4983230072969 + 3 ^ 40 * 7769752 * 2
def baseEnd_7769752 : Nat := 1329872447410796681089189

theorem tailTrace_7769752 : CollatzResearch.WordTrace tailWord_7769752 prefixEnd_7769752 1329872447410796681089189 := by
  unfold tailWord_7769752
  simp only [CollatzResearch.WordTrace]
  refine ⟨141693068273761473420695755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188924091031681964560927673 141693068273761473420695755)
  ·
    refine ⟨212539602410642210131043633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141693068273761473420695755 212539602410642210131043633)
    ·
      refine ⟨159404701807981657598282725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212539602410642210131043633 159404701807981657598282725)
      ·
        refine ⟨29888381588996560799678011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159404701807981657598282725 29888381588996560799678011)
        ·
          refine ⟨44832572383494841199517017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29888381588996560799678011 44832572383494841199517017)
          ·
            refine ⟨33624429287621130899637763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44832572383494841199517017 33624429287621130899637763)
            ·
              refine ⟨50436643931431696349456645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33624429287621130899637763 50436643931431696349456645)
              ·
                refine ⟨9456870737143443065523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50436643931431696349456645 9456870737143443065523121)
                ·
                  refine ⟨7092653052857582299142341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456870737143443065523121 7092653052857582299142341)
                  ·
                    refine ⟨1329872447410796681089189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092653052857582299142341 1329872447410796681089189)
                    ·
                      rfl

theorem cell23_7769752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_7769752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769752 prefixEnd_7769752 := by exact prefixLift 7769752
  have htrace : WordTrace (prefixWord ++ tailWord_7769752) baseStart_7769752 baseEnd_7769752 := by
    simpa [prefixWord, tailWord_7769752, baseEnd_7769752] using wordTrace_append hprefix tailTrace_7769752
  have hstable : (prefixWord ++ tailWord_7769752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769752).length < 2 ^ (prefixWord ++ tailWord_7769752).sum := by decide
  have hdescent : baseEnd_7769752 < baseStart_7769752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769792 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_7769792 : Nat := 118140960795 + 7769792 * 2 ^ 59
def prefixEnd_7769792 : Nat := 4983230072969 + 3 ^ 40 * 7769792 * 2
def baseEnd_7769792 : Nat := 3989637881458569886767383

theorem tailTrace_7769792 : CollatzResearch.WordTrace tailWord_7769792 prefixEnd_7769792 3989637881458569886767383 := by
  unfold tailWord_7769792
  simp only [CollatzResearch.WordTrace]
  refine ⟨141693797733689016836423815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188925063644918689115231753 141693797733689016836423815)
  ·
    refine ⟨212540696600533525254635723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141693797733689016836423815 212540696600533525254635723)
    ·
      refine ⟨318811044900800287881953585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212540696600533525254635723 318811044900800287881953585)
      ·
        refine ⟨239108283675600215911465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318811044900800287881953585 239108283675600215911465189)
        ·
          refine ⟨44832803189175040483399723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239108283675600215911465189 44832803189175040483399723)
          ·
            refine ⟨67249204783762560725099585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44832803189175040483399723 67249204783762560725099585)
            ·
              refine ⟨50436903587821920543824689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67249204783762560725099585 50436903587821920543824689)
              ·
                refine ⟨37827677690866440407868517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50436903587821920543824689 37827677690866440407868517)
                ·
                  refine ⟨7092689567037457576475347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37827677690866440407868517 7092689567037457576475347)
                  ·
                    refine ⟨10639034350556186364713021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092689567037457576475347 10639034350556186364713021)
                    ·
                      refine ⟨3989637881458569886767383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639034350556186364713021 3989637881458569886767383)
                      ·
                        rfl

theorem cell23_7769792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_7769792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769792 prefixEnd_7769792 := by exact prefixLift 7769792
  have htrace : WordTrace (prefixWord ++ tailWord_7769792) baseStart_7769792 baseEnd_7769792 := by
    simpa [prefixWord, tailWord_7769792, baseEnd_7769792] using wordTrace_append hprefix tailTrace_7769792
  have hstable : (prefixWord ++ tailWord_7769792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769792).length < 2 ^ (prefixWord ++ tailWord_7769792).sum := by decide
  have hdescent : baseEnd_7769792 < baseStart_7769792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769809 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_7769809 : Nat := 118140960795 + 7769809 * 2 ^ 59
def prefixEnd_7769809 : Nat := 4983230072969 + 3 ^ 40 * 7769809 * 2
def baseEnd_7769809 : Nat := 3989646610629696320254805

theorem tailTrace_7769809 : CollatzResearch.WordTrace tailWord_7769809 prefixEnd_7769809 3989646610629696320254805 := by
  unfold tailWord_7769809
  simp only [CollatzResearch.WordTrace]
  refine ⟨283388215508316445576216481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188925477005544297050810987 283388215508316445576216481)
  ·
    refine ⟨212541161631237334182162361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283388215508316445576216481 212541161631237334182162361)
    ·
      refine ⟨159405871223428000636621771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212541161631237334182162361 159405871223428000636621771)
      ·
        refine ⟨239108806835142000954932657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159405871223428000636621771 239108806835142000954932657)
        ·
          refine ⟨179331605126356500716199493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239108806835142000954932657 179331605126356500716199493)
          ·
            refine ⟨33624675961191843884287405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179331605126356500716199493 33624675961191843884287405)
            ·
              refine ⟨12609253485446941456607777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33624675961191843884287405 12609253485446941456607777)
              ·
                refine ⟨9456940114085206092455833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12609253485446941456607777 9456940114085206092455833)
                ·
                  refine ⟨7092705085563904569341875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456940114085206092455833 7092705085563904569341875)
                  ·
                    refine ⟨10639057628345856854012813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092705085563904569341875 10639057628345856854012813)
                    ·
                      refine ⟨3989646610629696320254805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639057628345856854012813 3989646610629696320254805)
                      ·
                        rfl

theorem cell23_7769809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_7769809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769809 prefixEnd_7769809 := by exact prefixLift 7769809
  have htrace : WordTrace (prefixWord ++ tailWord_7769809) baseStart_7769809 baseEnd_7769809 := by
    simpa [prefixWord, tailWord_7769809, baseEnd_7769809] using wordTrace_append hprefix tailTrace_7769809
  have hstable : (prefixWord ++ tailWord_7769809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769809).length < 2 ^ (prefixWord ++ tailWord_7769809).sum := by decide
  have hdescent : baseEnd_7769809 < baseStart_7769809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769835 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3]
def baseStart_7769835 : Nat := 118140960795 + 7769835 * 2 ^ 59
def prefixEnd_7769835 : Nat := 4983230072969 + 3 ^ 40 * 7769835 * 2
def baseEnd_7769835 : Nat := 3989659961126713218529685

theorem tailTrace_7769835 : CollatzResearch.WordTrace tailWord_7769835 prefixEnd_7769835 3989659961126713218529685 := by
  unfold tailWord_7769835
  simp only [CollatzResearch.WordTrace]
  refine ⟨283389163806222252016662959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188926109204148168011108639 283389163806222252016662959)
  ·
    refine ⟨425083745709333378024994439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283389163806222252016662959 425083745709333378024994439)
    ·
      refine ⟨637625618564000067037491659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425083745709333378024994439 637625618564000067037491659)
      ·
        refine ⟨956438427846000100556237489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637625618564000067037491659 956438427846000100556237489)
        ·
          refine ⟨717328820884500075417178117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956438427846000100556237489 717328820884500075417178117)
          ·
            refine ⟨134499153915843764140720897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717328820884500075417178117 134499153915843764140720897)
            ·
              refine ⟨100874365436882823105540673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134499153915843764140720897 100874365436882823105540673)
              ·
                refine ⟨75655774077662117329155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100874365436882823105540673 75655774077662117329155505)
                ·
                  refine ⟨56741830558246587996866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75655774077662117329155505 56741830558246587996866629)
                  ·
                    refine ⟨10639093229671235249412493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56741830558246587996866629 10639093229671235249412493)
                    ·
                      refine ⟨3989659961126713218529685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639093229671235249412493 3989659961126713218529685)
                      ·
                        rfl

theorem cell23_7769835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].length) (baseStart_7769835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769835 prefixEnd_7769835 := by exact prefixLift 7769835
  have htrace : WordTrace (prefixWord ++ tailWord_7769835) baseStart_7769835 baseEnd_7769835 := by
    simpa [prefixWord, tailWord_7769835, baseEnd_7769835] using wordTrace_append hprefix tailTrace_7769835
  have hstable : (prefixWord ++ tailWord_7769835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769835).length < 2 ^ (prefixWord ++ tailWord_7769835).sum := by decide
  have hdescent : baseEnd_7769835 < baseStart_7769835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769925 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7769925 : Nat := 118140960795 + 7769925 * 2 ^ 59
def prefixEnd_7769925 : Nat := 4983230072969 + 3 ^ 40 * 7769925 * 2
def baseEnd_7769925 : Nat := 3989706174385617866404271

theorem tailTrace_7769925 : CollatzResearch.WordTrace tailWord_7769925 prefixEnd_7769925 3989706174385617866404271 := by
  unfold tailWord_7769925
  simp only [CollatzResearch.WordTrace]
  refine ⟨283392446375896197387439229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188928297583930798258292819 283392446375896197387439229)
  ·
    refine ⟨106272167390961074020289711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283392446375896197387439229 106272167390961074020289711)
    ·
      refine ⟨159408251086441611030434567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106272167390961074020289711 159408251086441611030434567)
      ·
        refine ⟨239112376629662416545651851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159408251086441611030434567 239112376629662416545651851)
        ·
          refine ⟨358668564944493624818477777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239112376629662416545651851 358668564944493624818477777)
          ·
            refine ⟨269001423708370218613858333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358668564944493624818477777 269001423708370218613858333)
            ·
              refine ⟨100875533890638831980196875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269001423708370218613858333 100875533890638831980196875)
              ·
                refine ⟨151313300835958247970295313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100875533890638831980196875 151313300835958247970295313)
                ·
                  refine ⟨113484975626968685977721485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151313300835958247970295313 113484975626968685977721485)
                  ·
                    refine ⟨42556865860113257241645557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113484975626968685977721485 42556865860113257241645557)
                    ·
                      refine ⟨3989706174385617866404271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42556865860113257241645557 3989706174385617866404271)
                      ·
                        rfl

theorem cell23_7769925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7769925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769925 prefixEnd_7769925 := by exact prefixLift 7769925
  have htrace : WordTrace (prefixWord ++ tailWord_7769925) baseStart_7769925 baseEnd_7769925 := by
    simpa [prefixWord, tailWord_7769925, baseEnd_7769925] using wordTrace_append hprefix tailTrace_7769925
  have hstable : (prefixWord ++ tailWord_7769925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769925).length < 2 ^ (prefixWord ++ tailWord_7769925).sum := by decide
  have hdescent : baseEnd_7769925 < baseStart_7769925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7769956 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_7769956 : Nat := 118140960795 + 7769956 * 2 ^ 59
def prefixEnd_7769956 : Nat := 4983230072969 + 3 ^ 40 * 7769956 * 2
def baseEnd_7769956 : Nat := 3989722092285907245116629

theorem tailTrace_7769956 : CollatzResearch.WordTrace tailWord_7769956 prefixEnd_7769956 3989722092285907245116629 := by
  unfold tailWord_7769956
  simp only [CollatzResearch.WordTrace]
  refine ⟨141696788519391944840908861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188929051359189259787878481 141696788519391944840908861)
  ·
    refine ⟨53136295694771979315340823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141696788519391944840908861 53136295694771979315340823)
    ·
      refine ⟨79704443542157968973011235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53136295694771979315340823 79704443542157968973011235)
      ·
        refine ⟨119556665313236953459516853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79704443542157968973011235 119556665313236953459516853)
        ·
          refine ⟨11208437373115964386829705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119556665313236953459516853 11208437373115964386829705)
          ·
            refine ⟨8406328029836973290122279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11208437373115964386829705 8406328029836973290122279)
            ·
              refine ⟨12609492044755459935183419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8406328029836973290122279 12609492044755459935183419)
              ·
                refine ⟨18914238067133189902775129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12609492044755459935183419 18914238067133189902775129)
                ·
                  refine ⟨14185678550349892427081347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18914238067133189902775129 14185678550349892427081347)
                  ·
                    refine ⟨21278517825524838640622021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14185678550349892427081347 21278517825524838640622021)
                    ·
                      refine ⟨3989722092285907245116629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21278517825524838640622021 3989722092285907245116629)
                      ·
                        rfl

theorem cell23_7769956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_7769956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7769956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7769956 prefixEnd_7769956 := by exact prefixLift 7769956
  have htrace : WordTrace (prefixWord ++ tailWord_7769956) baseStart_7769956 baseEnd_7769956 := by
    simpa [prefixWord, tailWord_7769956, baseEnd_7769956] using wordTrace_append hprefix tailTrace_7769956
  have hstable : (prefixWord ++ tailWord_7769956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7769956).length < 2 ^ (prefixWord ++ tailWord_7769956).sum := by decide
  have hdescent : baseEnd_7769956 < baseStart_7769956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7769956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770039 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 2, 4]
def baseStart_7770039 : Nat := 118140960795 + 7770039 * 2 ^ 59
def prefixEnd_7770039 : Nat := 4983230072969 + 3 ^ 40 * 7770039 * 2
def baseEnd_7770039 : Nat := 1329921570393410140126249

theorem tailTrace_7770039 : CollatzResearch.WordTrace tailWord_7770039 prefixEnd_7770039 1329921570393410140126249 := by
  unfold tailWord_7770039
  simp only [CollatzResearch.WordTrace]
  refine ⟨283396604297483194857089171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188931069531655463238059447 283396604297483194857089171)
  ·
    refine ⟨425094906446224792285633757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283396604297483194857089171 425094906446224792285633757)
    ·
      refine ⟨159410589917334297107112659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425094906446224792285633757 159410589917334297107112659)
      ·
        refine ⟨239115884876001445660668989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159410589917334297107112659 239115884876001445660668989)
        ·
          refine ⟨89668456828500542122750871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239115884876001445660668989 89668456828500542122750871)
          ·
            refine ⟨134502685242750813184126307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89668456828500542122750871 134502685242750813184126307)
            ·
              refine ⟨201754027864126219776189461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134502685242750813184126307 201754027864126219776189461)
              ·
                refine ⟨9457220056130916552008881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201754027864126219776189461 9457220056130916552008881)
                ·
                  refine ⟨7092915042098187414006661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457220056130916552008881 7092915042098187414006661)
                  ·
                    refine ⟨1329921570393410140126249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092915042098187414006661 1329921570393410140126249)
                    ·
                      rfl

theorem cell23_7770039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_7770039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770039 prefixEnd_7770039 := by exact prefixLift 7770039
  have htrace : WordTrace (prefixWord ++ tailWord_7770039) baseStart_7770039 baseEnd_7770039 := by
    simpa [prefixWord, tailWord_7770039, baseEnd_7770039] using wordTrace_append hprefix tailTrace_7770039
  have hstable : (prefixWord ++ tailWord_7770039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770039).length < 2 ^ (prefixWord ++ tailWord_7770039).sum := by decide
  have hdescent : baseEnd_7770039 < baseStart_7770039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770042 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_7770042 : Nat := 118140960795 + 7770042 * 2 ^ 59
def prefixEnd_7770042 : Nat := 4983230072969 + 3 ^ 40 * 7770042 * 2
def baseEnd_7770042 : Nat := 3989766251622193908641233

theorem tailTrace_7770042 : CollatzResearch.WordTrace tailWord_7770042 prefixEnd_7770042 3989766251622193908641233 := by
  unfold tailWord_7770042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70849178429118081592362095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188931142477648217579632253 70849178429118081592362095)
  ·
    refine ⟨106273767643677122388543143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70849178429118081592362095 106273767643677122388543143)
    ·
      refine ⟨159410651465515683582814715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106273767643677122388543143 159410651465515683582814715)
      ·
        refine ⟨239115977198273525374222073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159410651465515683582814715 239115977198273525374222073)
        ·
          refine ⟨179336982898705144030666555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239115977198273525374222073 179336982898705144030666555)
          ·
            refine ⟨269005474348057716045999833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179336982898705144030666555 269005474348057716045999833)
            ·
              refine ⟨201754105761043287034499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269005474348057716045999833 201754105761043287034499875)
              ·
                refine ⟨302631158641564930551749813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201754105761043287034499875 302631158641564930551749813)
                ·
                  refine ⟨28371671122646712239226545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302631158641564930551749813 28371671122646712239226545)
                  ·
                    refine ⟨21278753341985034179419909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28371671122646712239226545 21278753341985034179419909)
                    ·
                      refine ⟨3989766251622193908641233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21278753341985034179419909 3989766251622193908641233)
                      ·
                        rfl

theorem cell23_7770042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_7770042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770042 prefixEnd_7770042 := by exact prefixLift 7770042
  have htrace : WordTrace (prefixWord ++ tailWord_7770042) baseStart_7770042 baseEnd_7770042 := by
    simpa [prefixWord, tailWord_7770042, baseEnd_7770042] using wordTrace_append hprefix tailTrace_7770042
  have hstable : (prefixWord ++ tailWord_7770042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770042).length < 2 ^ (prefixWord ++ tailWord_7770042).sum := by decide
  have hdescent : baseEnd_7770042 < baseStart_7770042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770056 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_7770056 : Nat := 118140960795 + 7770056 * 2 ^ 59
def prefixEnd_7770056 : Nat := 4983230072969 + 3 ^ 40 * 7770056 * 2
def baseEnd_7770056 : Nat := 1329924480117118951288723

theorem tailTrace_7770056 : CollatzResearch.WordTrace tailWord_7770056 prefixEnd_7770056 1329924480117118951288723 := by
  unfold tailWord_7770056
  simp only [CollatzResearch.WordTrace]
  refine ⟨141698612169210803380229011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188931482892281071173638681 141698612169210803380229011)
  ·
    refine ⟨212547918253816205070343517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141698612169210803380229011 212547918253816205070343517)
    ·
      refine ⟨79705469345181076901378819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212547918253816205070343517 79705469345181076901378819)
      ·
        refine ⟨119558204017771615352068229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79705469345181076901378819 119558204017771615352068229)
        ·
          refine ⟨22417163253332177878512793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119558204017771615352068229 22417163253332177878512793)
          ·
            refine ⟨16812872439999133408884595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22417163253332177878512793 16812872439999133408884595)
            ·
              refine ⟨25219308659998700113326893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16812872439999133408884595 25219308659998700113326893)
              ·
                refine ⟨9457240747499512542497585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25219308659998700113326893 9457240747499512542497585)
                ·
                  refine ⟨7092930560624634406873189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9457240747499512542497585 7092930560624634406873189)
                  ·
                    refine ⟨1329924480117118951288723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7092930560624634406873189 1329924480117118951288723)
                    ·
                      rfl

theorem cell23_7770056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_7770056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770056 prefixEnd_7770056 := by exact prefixLift 7770056
  have htrace : WordTrace (prefixWord ++ tailWord_7770056) baseStart_7770056 baseEnd_7770056 := by
    simpa [prefixWord, tailWord_7770056, baseEnd_7770056] using wordTrace_append hprefix tailTrace_7770056
  have hstable : (prefixWord ++ tailWord_7770056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770056).length < 2 ^ (prefixWord ++ tailWord_7770056).sum := by decide
  have hdescent : baseEnd_7770056 < baseStart_7770056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7770079 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_7770079 : Nat := 118140960795 + 7770079 * 2 ^ 59
def prefixEnd_7770079 : Nat := 4983230072969 + 3 ^ 40 * 7770079 * 2
def baseEnd_7770079 : Nat := 3989785250406410263878563

theorem tailTrace_7770079 : CollatzResearch.WordTrace tailWord_7770079 prefixEnd_7770079 3989785250406410263878563 := by
  unfold tailWord_7770079
  simp only [CollatzResearch.WordTrace]
  refine ⟨283398063217338281688545291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188932042144892187792363527 283398063217338281688545291)
  ·
    refine ⟨425097094826007422532817937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283398063217338281688545291 425097094826007422532817937)
    ·
      refine ⟨318822821119505566899613453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425097094826007422532817937 318822821119505566899613453)
      ·
        refine ⟨119558557919814587587355045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318822821119505566899613453 119558557919814587587355045)
        ·
          refine ⟨22417229609965235172629071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119558557919814587587355045 22417229609965235172629071)
          ·
            refine ⟨33625844414947852758943607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22417229609965235172629071 33625844414947852758943607)
            ·
              refine ⟨50438766622421779138415411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33625844414947852758943607 50438766622421779138415411)
              ·
                refine ⟨75658149933632668707623117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50438766622421779138415411 75658149933632668707623117)
                ·
                  refine ⟨28371806225112250765358669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75658149933632668707623117 28371806225112250765358669)
                  ·
                    refine ⟨10639427334417094037009501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28371806225112250765358669 10639427334417094037009501)
                    ·
                      refine ⟨3989785250406410263878563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10639427334417094037009501 3989785250406410263878563)
                      ·
                        rfl

theorem cell23_7770079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_7770079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7770079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7770079 prefixEnd_7770079 := by exact prefixLift 7770079
  have htrace : WordTrace (prefixWord ++ tailWord_7770079) baseStart_7770079 baseEnd_7770079 := by
    simpa [prefixWord, tailWord_7770079, baseEnd_7770079] using wordTrace_append hprefix tailTrace_7770079
  have hstable : (prefixWord ++ tailWord_7770079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7770079).length < 2 ^ (prefixWord ++ tailWord_7770079).sum := by decide
  have hdescent : baseEnd_7770079 < baseStart_7770079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7770079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
