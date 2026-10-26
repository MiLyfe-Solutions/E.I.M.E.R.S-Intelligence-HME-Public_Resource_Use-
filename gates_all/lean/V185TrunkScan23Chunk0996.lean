import V185TrunkScan23Chunk0995

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5898068 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5898068 : Nat := 118140960795 + 5898068 * 2 ^ 59
def prefixEnd_5898068 : Nat := 4983230072969 + 3 ^ 40 * 5898068 * 2
def baseEnd_5898068 : Nat := 3028543816902535015525285

theorem tailTrace_5898068 : CollatzResearch.WordTrace tailWord_5898068 prefixEnd_5898068 3028543816902535015525285 := by
  unfold tailWord_5898068
  simp only [CollatzResearch.WordTrace]
  refine ⟨107560106398157210331739429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143413475197542947108985905 107560106398157210331739429)
  ·
    refine ⟨20167519949654476937201143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107560106398157210331739429 20167519949654476937201143)
    ·
      refine ⟨30251279924481715405801715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167519949654476937201143 30251279924481715405801715)
      ·
        refine ⟨45376919886722573108702573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30251279924481715405801715 45376919886722573108702573)
        ·
          refine ⟨17016344957520964915763465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45376919886722573108702573 17016344957520964915763465)
          ·
            refine ⟨12762258718140723686822599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17016344957520964915763465 12762258718140723686822599)
            ·
              refine ⟨19143388077211085530233899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12762258718140723686822599 19143388077211085530233899)
              ·
                refine ⟨28715082115816628295350849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19143388077211085530233899 28715082115816628295350849)
                ·
                  refine ⟨21536311586862471221513137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28715082115816628295350849 21536311586862471221513137)
                  ·
                    refine ⟨16152233690146853416134853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21536311586862471221513137 16152233690146853416134853)
                    ·
                      refine ⟨3028543816902535015525285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16152233690146853416134853 3028543816902535015525285)
                      ·
                        rfl

theorem cell23_5898068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5898068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898068 prefixEnd_5898068 := by exact prefixLift 5898068
  have htrace : WordTrace (prefixWord ++ tailWord_5898068) baseStart_5898068 baseEnd_5898068 := by
    simpa [prefixWord, tailWord_5898068, baseEnd_5898068] using wordTrace_append hprefix tailTrace_5898068
  have hstable : (prefixWord ++ tailWord_5898068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898068).length < 2 ^ (prefixWord ++ tailWord_5898068).sum := by decide
  have hdescent : baseEnd_5898068 < baseStart_5898068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898111 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_5898111 : Nat := 118140960795 + 5898111 * 2 ^ 59
def prefixEnd_5898111 : Nat := 4983230072969 + 3 ^ 40 * 5898111 * 2
def baseEnd_5898111 : Nat := 3028565896570678347287587

theorem tailTrace_5898111 : CollatzResearch.WordTrace tailWord_5898111 prefixEnd_5898111 3028565896570678347287587 := by
  unfold tailWord_5898111
  simp only [CollatzResearch.WordTrace]
  refine ⟨215121781135158639007294187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143414520756772426004862791 215121781135158639007294187)
  ·
    refine ⟨322682671702737958510941281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215121781135158639007294187 322682671702737958510941281)
    ·
      refine ⟨242012003777053468883205961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322682671702737958510941281 242012003777053468883205961)
      ·
        refine ⟨181509002832790101662404471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242012003777053468883205961 181509002832790101662404471)
        ·
          refine ⟨272263504249185152493606707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181509002832790101662404471 272263504249185152493606707)
          ·
            refine ⟨408395256373777728740410061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272263504249185152493606707 408395256373777728740410061)
            ·
              refine ⟨153148221140166648277653773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408395256373777728740410061 153148221140166648277653773)
              ·
                refine ⟨57430582927562493104120165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153148221140166648277653773 57430582927562493104120165)
                ·
                  refine ⟨10768234298917967457022531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57430582927562493104120165 10768234298917967457022531)
                  ·
                    refine ⟨16152351448376951185533797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10768234298917967457022531 16152351448376951185533797)
                    ·
                      refine ⟨3028565896570678347287587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16152351448376951185533797 3028565896570678347287587)
                      ·
                        rfl

theorem cell23_5898111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_5898111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898111 prefixEnd_5898111 := by exact prefixLift 5898111
  have htrace : WordTrace (prefixWord ++ tailWord_5898111) baseStart_5898111 baseEnd_5898111 := by
    simpa [prefixWord, tailWord_5898111, baseEnd_5898111] using wordTrace_append hprefix tailTrace_5898111
  have hstable : (prefixWord ++ tailWord_5898111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898111).length < 2 ^ (prefixWord ++ tailWord_5898111).sum := by decide
  have hdescent : baseEnd_5898111 < baseStart_5898111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898148 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_5898148 : Nat := 118140960795 + 5898148 * 2 ^ 59
def prefixEnd_5898148 : Nat := 4983230072969 + 3 ^ 40 * 5898148 * 2
def baseEnd_5898148 : Nat := 3028584895354894702524917

theorem tailTrace_5898148 : CollatzResearch.WordTrace tailWord_5898148 prefixEnd_5898148 3028584895354894702524917 := by
  unfold tailWord_5898148
  simp only [CollatzResearch.WordTrace]
  refine ⟨107561565318012297163195549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143415420424016396217594065 107561565318012297163195549)
  ·
    refine ⟨40335586994254611436198331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107561565318012297163195549 40335586994254611436198331)
    ·
      refine ⟨60503380491381917154297497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40335586994254611436198331 60503380491381917154297497)
      ·
        refine ⟨45377535368536437865723123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60503380491381917154297497 45377535368536437865723123)
        ·
          refine ⟨68066303052804656798584685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45377535368536437865723123 68066303052804656798584685)
          ·
            refine ⟨25524863644801746299469257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68066303052804656798584685 25524863644801746299469257)
            ·
              refine ⟨19143647733601309724601943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25524863644801746299469257 19143647733601309724601943)
              ·
                refine ⟨28715471600401964586902915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19143647733601309724601943 28715471600401964586902915)
                ·
                  refine ⟨43073207400602946880354373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28715471600401964586902915 43073207400602946880354373)
                  ·
                    refine ⟨8076226387613052540066445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43073207400602946880354373 8076226387613052540066445)
                    ·
                      refine ⟨3028584895354894702524917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8076226387613052540066445 3028584895354894702524917)
                      ·
                        rfl

theorem cell23_5898148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_5898148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898148 prefixEnd_5898148 := by exact prefixLift 5898148
  have htrace : WordTrace (prefixWord ++ tailWord_5898148) baseStart_5898148 baseEnd_5898148 := by
    simpa [prefixWord, tailWord_5898148, baseEnd_5898148] using wordTrace_append hprefix tailTrace_5898148
  have hstable : (prefixWord ++ tailWord_5898148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898148).length < 2 ^ (prefixWord ++ tailWord_5898148).sum := by decide
  have hdescent : baseEnd_5898148 < baseStart_5898148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898165 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5898165 : Nat := 118140960795 + 5898165 * 2 ^ 59
def prefixEnd_5898165 : Nat := 4983230072969 + 3 ^ 40 * 5898165 * 2
def baseEnd_5898165 : Nat := 3028593624526021136012339

theorem tailTrace_5898165 : CollatzResearch.WordTrace tailWord_5898165 prefixEnd_5898165 3028593624526021136012339 := by
  unfold tailWord_5898165
  simp only [CollatzResearch.WordTrace]
  refine ⟨215123750676963006229759949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143415833784642004153173299 215123750676963006229759949)
  ·
    refine ⟨80671406503861127336159981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215123750676963006229759949 80671406503861127336159981)
    ·
      refine ⟨30251777438947922751059993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80671406503861127336159981 30251777438947922751059993)
      ·
        refine ⟨22688833079210942063294995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30251777438947922751059993 22688833079210942063294995)
        ·
          refine ⟨34033249618816413094942493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22688833079210942063294995 34033249618816413094942493)
          ·
            refine ⟨12762468607056154910603435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34033249618816413094942493 12762468607056154910603435)
            ·
              refine ⟨19143702910584232365905153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12762468607056154910603435 19143702910584232365905153)
              ·
                refine ⟨14357777182938174274428865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19143702910584232365905153 14357777182938174274428865)
                ·
                  refine ⟨10768332887203630705821649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14357777182938174274428865 10768332887203630705821649)
                  ·
                    refine ⟨8076249665402723029366237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10768332887203630705821649 8076249665402723029366237)
                    ·
                      refine ⟨3028593624526021136012339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8076249665402723029366237 3028593624526021136012339)
                      ·
                        rfl

theorem cell23_5898165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5898165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898165 prefixEnd_5898165 := by exact prefixLift 5898165
  have htrace : WordTrace (prefixWord ++ tailWord_5898165) baseStart_5898165 baseEnd_5898165 := by
    simpa [prefixWord, tailWord_5898165, baseEnd_5898165] using wordTrace_append hprefix tailTrace_5898165
  have hstable : (prefixWord ++ tailWord_5898165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898165).length < 2 ^ (prefixWord ++ tailWord_5898165).sum := by decide
  have hdescent : baseEnd_5898165 < baseStart_5898165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898212 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_5898212 : Nat := 118140960795 + 5898212 * 2 ^ 59
def prefixEnd_5898212 : Nat := 4983230072969 + 3 ^ 40 * 5898212 * 2
def baseEnd_5898212 : Nat := 3028617758116782452124623

theorem tailTrace_5898212 : CollatzResearch.WordTrace tailWord_5898212 prefixEnd_5898212 3028617758116782452124623 := by
  unfold tailWord_5898212
  simp only [CollatzResearch.WordTrace]
  refine ⟨107562732453896366628360445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143416976605195155504480593 107562732453896366628360445)
  ·
    refine ⟨40336024670211137485635167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107562732453896366628360445 40336024670211137485635167)
    ·
      refine ⟨60504037005316706228452751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40336024670211137485635167 60504037005316706228452751)
      ·
        refine ⟨90756055507975059342679127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60504037005316706228452751 90756055507975059342679127)
        ·
          refine ⟨136134083261962589014018691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90756055507975059342679127 136134083261962589014018691)
          ·
            refine ⟨204201124892943883521028037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136134083261962589014018691 204201124892943883521028037)
            ·
              refine ⟨38287710917426978160192757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204201124892943883521028037 38287710917426978160192757)
              ·
                refine ⟨3589472898508779202518071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38287710917426978160192757 3589472898508779202518071)
                ·
                  refine ⟨5384209347763168803777107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589472898508779202518071 5384209347763168803777107)
                  ·
                    refine ⟨8076314021644753205665661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384209347763168803777107 8076314021644753205665661)
                    ·
                      refine ⟨3028617758116782452124623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8076314021644753205665661 3028617758116782452124623)
                      ·
                        rfl

theorem cell23_5898212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_5898212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898212 prefixEnd_5898212 := by exact prefixLift 5898212
  have htrace : WordTrace (prefixWord ++ tailWord_5898212) baseStart_5898212 baseEnd_5898212 := by
    simpa [prefixWord, tailWord_5898212, baseEnd_5898212] using wordTrace_append hprefix tailTrace_5898212
  have hstable : (prefixWord ++ tailWord_5898212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898212).length < 2 ^ (prefixWord ++ tailWord_5898212).sum := by decide
  have hdescent : baseEnd_5898212 < baseStart_5898212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898222 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_5898222 : Nat := 118140960795 + 5898222 * 2 ^ 59
def prefixEnd_5898222 : Nat := 4983230072969 + 3 ^ 40 * 5898222 * 2
def baseEnd_5898222 : Nat := 3028622892923327412999577

theorem tailTrace_5898222 : CollatzResearch.WordTrace tailWord_5898222 prefixEnd_5898222 3028622892923327412999577 := by
  unfold tailWord_5898222
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890728704719563120573115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143417219758504336643056613 26890728704719563120573115)
  ·
    refine ⟨40336093057079344680859673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26890728704719563120573115 40336093057079344680859673)
    ·
      refine ⟨30252069792809508510644755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40336093057079344680859673 30252069792809508510644755)
      ·
        refine ⟨45378104689214262765967133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30252069792809508510644755 45378104689214262765967133)
        ·
          refine ⟨17016789258455348537237675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45378104689214262765967133 17016789258455348537237675)
          ·
            refine ⟨25525183887683022805856513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17016789258455348537237675 25525183887683022805856513)
            ·
              refine ⟨19143887915762267104392385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25525183887683022805856513 19143887915762267104392385)
              ·
                refine ⟨14357915936821700328294289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19143887915762267104392385 14357915936821700328294289)
                ·
                  refine ⟨10768436952616275246220717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14357915936821700328294289 10768436952616275246220717)
                  ·
                    refine ⟨4038163857231103217332769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10768436952616275246220717 4038163857231103217332769)
                    ·
                      refine ⟨3028622892923327412999577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038163857231103217332769 3028622892923327412999577)
                      ·
                        rfl

theorem cell23_5898222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_5898222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898222 prefixEnd_5898222 := by exact prefixLift 5898222
  have htrace : WordTrace (prefixWord ++ tailWord_5898222) baseStart_5898222 baseEnd_5898222 := by
    simpa [prefixWord, tailWord_5898222, baseEnd_5898222] using wordTrace_append hprefix tailTrace_5898222
  have hstable : (prefixWord ++ tailWord_5898222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898222).length < 2 ^ (prefixWord ++ tailWord_5898222).sum := by decide
  have hdescent : baseEnd_5898222 < baseStart_5898222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898245 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_5898245 : Nat := 118140960795 + 5898245 * 2 ^ 59
def prefixEnd_5898245 : Nat := 4983230072969 + 3 ^ 40 * 5898245 * 2
def baseEnd_5898245 : Nat := 1009544900992793607670657

theorem tailTrace_5898245 : CollatzResearch.WordTrace tailWord_5898245 prefixEnd_5898245 1009544900992793607670657 := by
  unfold tailWord_5898245
  simp only [CollatzResearch.WordTrace]
  refine ⟨215126668516673179892672189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143417779011115453261781459 215126668516673179892672189)
  ·
    refine ⟨80672500693752442459752071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215126668516673179892672189 80672500693752442459752071)
    ·
      refine ⟨121008751040628663689628107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80672500693752442459752071 121008751040628663689628107)
      ·
        refine ⟨181513126560942995534442161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121008751040628663689628107 181513126560942995534442161)
        ·
          refine ⟨136134844920707246650831621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181513126560942995534442161 136134844920707246650831621)
          ·
            refine ⟨25525283422632608747030929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136134844920707246650831621 25525283422632608747030929)
            ·
              refine ⟨19143962566974456560273197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25525283422632608747030929 19143962566974456560273197)
              ·
                refine ⟨7178985962615421210102449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19143962566974456560273197 7178985962615421210102449)
                ·
                  refine ⟨5384239471961565907576837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178985962615421210102449 5384239471961565907576837)
                  ·
                    refine ⟨1009544900992793607670657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384239471961565907576837 1009544900992793607670657)
                    ·
                      rfl

theorem cell23_5898245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_5898245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898245 prefixEnd_5898245 := by exact prefixLift 5898245
  have htrace : WordTrace (prefixWord ++ tailWord_5898245) baseStart_5898245 baseEnd_5898245 := by
    simpa [prefixWord, tailWord_5898245, baseEnd_5898245] using wordTrace_append hprefix tailTrace_5898245
  have hstable : (prefixWord ++ tailWord_5898245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898245).length < 2 ^ (prefixWord ++ tailWord_5898245).sum := by decide
  have hdescent : baseEnd_5898245 < baseStart_5898245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898252 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_5898252 : Nat := 118140960795 + 5898252 * 2 ^ 59
def prefixEnd_5898252 : Nat := 4983230072969 + 3 ^ 40 * 5898252 * 2
def baseEnd_5898252 : Nat := 3028638297342962295624439

theorem tailTrace_5898252 : CollatzResearch.WordTrace tailWord_5898252 prefixEnd_5898252 3028638297342962295624439 := by
  unfold tailWord_5898252
  simp only [CollatzResearch.WordTrace]
  refine ⟨107563461913823910044088505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143417949218431880058784673 107563461913823910044088505)
  ·
    refine ⟨80672596435367932533066379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107563461913823910044088505 80672596435367932533066379)
    ·
      refine ⟨121008894653051898799599569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80672596435367932533066379 121008894653051898799599569)
      ·
        refine ⟨90756670989788924099699677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121008894653051898799599569 90756670989788924099699677)
        ·
          refine ⟨34033751621170846537387379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90756670989788924099699677 34033751621170846537387379)
          ·
            refine ⟨51050627431756269806081069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34033751621170846537387379 51050627431756269806081069)
            ·
              refine ⟨19143985286908601177280401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51050627431756269806081069 19143985286908601177280401)
              ·
                refine ⟨14357988965181450882960301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19143985286908601177280401 14357988965181450882960301)
                ·
                  refine ⟨5384245861943044081110113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14357988965181450882960301 5384245861943044081110113)
                  ·
                    refine ⟨4038184396457283060832585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384245861943044081110113 4038184396457283060832585)
                    ·
                      refine ⟨3028638297342962295624439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038184396457283060832585 3028638297342962295624439)
                      ·
                        rfl

theorem cell23_5898252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_5898252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898252 prefixEnd_5898252 := by exact prefixLift 5898252
  have htrace : WordTrace (prefixWord ++ tailWord_5898252) baseStart_5898252 baseEnd_5898252 := by
    simpa [prefixWord, tailWord_5898252, baseEnd_5898252] using wordTrace_append hprefix tailTrace_5898252
  have hstable : (prefixWord ++ tailWord_5898252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898252).length < 2 ^ (prefixWord ++ tailWord_5898252).sum := by decide
  have hdescent : baseEnd_5898252 < baseStart_5898252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898269 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_5898269 : Nat := 118140960795 + 5898269 * 2 ^ 59
def prefixEnd_5898269 : Nat := 4983230072969 + 3 ^ 40 * 5898269 * 2
def baseEnd_5898269 : Nat := 3028647026514088729111861

theorem tailTrace_5898269 : CollatzResearch.WordTrace tailWord_5898269 prefixEnd_5898269 3028647026514088729111861 := by
  unfold tailWord_5898269
  simp only [CollatzResearch.WordTrace]
  refine ⟨215127543868586231991545861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143418362579057487994363907 215127543868586231991545861)
  ·
    refine ⟨40336414475359918498414849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215127543868586231991545861 40336414475359918498414849)
    ·
      refine ⟨30252310856519938873811137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40336414475359918498414849 30252310856519938873811137)
      ·
        refine ⟨22689233142389954155358353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30252310856519938873811137 22689233142389954155358353)
        ·
          refine ⟨17016924856792465616518765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22689233142389954155358353 17016924856792465616518765)
          ·
            refine ⟨6381346821297174606194537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17016924856792465616518765 6381346821297174606194537)
            ·
              refine ⟨4786010115972880954645903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6381346821297174606194537 4786010115972880954645903)
              ·
                refine ⟨7179015173959321431968855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786010115972880954645903 7179015173959321431968855)
                ·
                  refine ⟨10768522760938982147953283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7179015173959321431968855 10768522760938982147953283)
                  ·
                    refine ⟨16152784141408473221929925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10768522760938982147953283 16152784141408473221929925)
                    ·
                      refine ⟨3028647026514088729111861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16152784141408473221929925 3028647026514088729111861)
                      ·
                        rfl

theorem cell23_5898269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_5898269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898269 prefixEnd_5898269 := by exact prefixLift 5898269
  have htrace : WordTrace (prefixWord ++ tailWord_5898269) baseStart_5898269 baseEnd_5898269 := by
    simpa [prefixWord, tailWord_5898269, baseEnd_5898269] using wordTrace_append hprefix tailTrace_5898269
  have hstable : (prefixWord ++ tailWord_5898269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898269).length < 2 ^ (prefixWord ++ tailWord_5898269).sum := by decide
  have hdescent : baseEnd_5898269 < baseStart_5898269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898286 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5898286 : Nat := 118140960795 + 5898286 * 2 ^ 59
def prefixEnd_5898286 : Nat := 4983230072969 + 3 ^ 40 * 5898286 * 2
def baseEnd_5898286 : Nat := 3028655755685215162599283

theorem tailTrace_5898286 : CollatzResearch.WordTrace tailWord_5898286 prefixEnd_5898286 3028655755685215162599283 := by
  unfold tailWord_5898286
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891020488690580486864339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143418775939683095929943141 26891020488690580486864339)
  ·
    refine ⟨40336530733035870730296509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26891020488690580486864339 40336530733035870730296509)
    ·
      refine ⟨15126199024888451523861191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40336530733035870730296509 15126199024888451523861191)
      ·
        refine ⟨22689298537332677285791787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126199024888451523861191 22689298537332677285791787)
        ·
          refine ⟨34033947805999015928687681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22689298537332677285791787 34033947805999015928687681)
          ·
            refine ⟨25525460854499261946515761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34033947805999015928687681 25525460854499261946515761)
            ·
              refine ⟨19144095640874446459886821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25525460854499261946515761 19144095640874446459886821)
              ·
                refine ⟨3589517932663958711228779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19144095640874446459886821 3589517932663958711228779)
                ·
                  refine ⟨5384276898995938066843169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589517932663958711228779 5384276898995938066843169)
                  ·
                    refine ⟨4038207674246953550132377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384276898995938066843169 4038207674246953550132377)
                    ·
                      refine ⟨3028655755685215162599283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038207674246953550132377 3028655755685215162599283)
                      ·
                        rfl

theorem cell23_5898286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5898286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898286 prefixEnd_5898286 := by exact prefixLift 5898286
  have htrace : WordTrace (prefixWord ++ tailWord_5898286) baseStart_5898286 baseEnd_5898286 := by
    simpa [prefixWord, tailWord_5898286, baseEnd_5898286] using wordTrace_append hprefix tailTrace_5898286
  have hstable : (prefixWord ++ tailWord_5898286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898286).length < 2 ^ (prefixWord ++ tailWord_5898286).sum := by decide
  have hdescent : baseEnd_5898286 < baseStart_5898286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898295 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_5898295 : Nat := 118140960795 + 5898295 * 2 ^ 59
def prefixEnd_5898295 : Nat := 4983230072969 + 3 ^ 40 * 5898295 * 2
def baseEnd_5898295 : Nat := 3028660377011105627386741

theorem tailTrace_5898295 : CollatzResearch.WordTrace tailWord_5898295 prefixEnd_5898295 3028660377011105627386741 := by
  unfold tailWord_5898295
  simp only [CollatzResearch.WordTrace]
  refine ⟨215128492166492038431992339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143418994777661358954661559 215128492166492038431992339)
  ·
    refine ⟨322692738249738057647988509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215128492166492038431992339 322692738249738057647988509)
    ·
      refine ⟨121009776843651771617995691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322692738249738057647988509 121009776843651771617995691)
      ·
        refine ⟨181514665265477657426993537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121009776843651771617995691 181514665265477657426993537)
        ·
          refine ⟨136135998949108243070245153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181514665265477657426993537 136135998949108243070245153)
          ·
            refine ⟨102101999211831182302683865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136135998949108243070245153 102101999211831182302683865)
            ·
              refine ⟨76576499408873386727012899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102101999211831182302683865 76576499408873386727012899)
              ·
                refine ⟨114864749113310080090519349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76576499408873386727012899 114864749113310080090519349)
                ·
                  refine ⟨10768570229372820008486189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114864749113310080090519349 10768570229372820008486189)
                  ·
                    refine ⟨4038213836014807503182321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10768570229372820008486189 4038213836014807503182321)
                    ·
                      refine ⟨3028660377011105627386741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038213836014807503182321 3028660377011105627386741)
                      ·
                        rfl

theorem cell23_5898295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_5898295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898295 prefixEnd_5898295 := by exact prefixLift 5898295
  have htrace : WordTrace (prefixWord ++ tailWord_5898295) baseStart_5898295 baseEnd_5898295 := by
    simpa [prefixWord, tailWord_5898295, baseEnd_5898295] using wordTrace_append hprefix tailTrace_5898295
  have hstable : (prefixWord ++ tailWord_5898295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898295).length < 2 ^ (prefixWord ++ tailWord_5898295).sum := by decide
  have hdescent : baseEnd_5898295 < baseStart_5898295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898328 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_5898328 : Nat := 118140960795 + 5898328 * 2 ^ 59
def prefixEnd_5898328 : Nat := 4983230072969 + 3 ^ 40 * 5898328 * 2
def baseEnd_5898328 : Nat := 3028677321872703998274089

theorem tailTrace_5898328 : CollatzResearch.WordTrace tailWord_5898328 prefixEnd_5898328 3028677321872703998274089 := by
  unfold tailWord_5898328
  simp only [CollatzResearch.WordTrace]
  refine ⟨107564847887686242533971819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143419797183581656711962425 107564847887686242533971819)
  ·
    refine ⟨161347271831529363800957729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107564847887686242533971819 161347271831529363800957729)
    ·
      refine ⟨121010453873647022850718297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161347271831529363800957729 121010453873647022850718297)
      ·
        refine ⟨90757840405235267138038723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121010453873647022850718297 90757840405235267138038723)
        ·
          refine ⟨136136760607852900707058085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90757840405235267138038723 136136760607852900707058085)
          ·
            refine ⟨25525642613972418882573391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136136760607852900707058085 25525642613972418882573391)
            ·
              refine ⟨38288463920958628323860087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25525642613972418882573391 38288463920958628323860087)
              ·
                refine ⟨57432695881437942485790131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38288463920958628323860087 57432695881437942485790131)
                ·
                  refine ⟨86149043822156913728685197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57432695881437942485790131 86149043822156913728685197)
                  ·
                    refine ⟨32305891433308842648256949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86149043822156913728685197 32305891433308842648256949)
                    ·
                      refine ⟨3028677321872703998274089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32305891433308842648256949 3028677321872703998274089)
                      ·
                        rfl

theorem cell23_5898328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_5898328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898328 prefixEnd_5898328 := by exact prefixLift 5898328
  have htrace : WordTrace (prefixWord ++ tailWord_5898328) baseStart_5898328 baseEnd_5898328 := by
    simpa [prefixWord, tailWord_5898328, baseEnd_5898328] using wordTrace_append hprefix tailTrace_5898328
  have hstable : (prefixWord ++ tailWord_5898328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898328).length < 2 ^ (prefixWord ++ tailWord_5898328).sum := by decide
  have hdescent : baseEnd_5898328 < baseStart_5898328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898359 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_5898359 : Nat := 118140960795 + 5898359 * 2 ^ 59
def prefixEnd_5898359 : Nat := 4983230072969 + 3 ^ 40 * 5898359 * 2
def baseEnd_5898359 : Nat := 3028693239772993376986447

theorem tailTrace_5898359 : CollatzResearch.WordTrace tailWord_5898359 prefixEnd_5898359 3028693239772993376986447 := by
  unfold tailWord_5898359
  simp only [CollatzResearch.WordTrace]
  refine ⟨215130826438260177362322131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143420550958840118241548087 215130826438260177362322131)
  ·
    refine ⟨322696239657390266043483197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215130826438260177362322131 322696239657390266043483197)
    ·
      refine ⟨121011089871521349766306199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322696239657390266043483197 121011089871521349766306199)
      ·
        refine ⟨181516634807282024649459299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121011089871521349766306199 181516634807282024649459299)
        ·
          refine ⟨272274952210923036974188949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181516634807282024649459299 272274952210923036974188949)
          ·
            refine ⟨12762888384887017358165107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272274952210923036974188949 12762888384887017358165107)
            ·
              refine ⟨19144332577330526037247661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12762888384887017358165107 19144332577330526037247661)
              ·
                refine ⟨7179124716498947263967873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19144332577330526037247661 7179124716498947263967873)
                ·
                  refine ⟨5384343537374210447975905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179124716498947263967873 5384343537374210447975905)
                  ·
                    refine ⟨4038257653030657835981929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384343537374210447975905 4038257653030657835981929)
                    ·
                      refine ⟨3028693239772993376986447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038257653030657835981929 3028693239772993376986447)
                      ·
                        rfl

theorem cell23_5898359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_5898359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898359 prefixEnd_5898359 := by exact prefixLift 5898359
  have htrace : WordTrace (prefixWord ++ tailWord_5898359) baseStart_5898359 baseEnd_5898359 := by
    simpa [prefixWord, tailWord_5898359, baseEnd_5898359] using wordTrace_append hprefix tailTrace_5898359
  have hstable : (prefixWord ++ tailWord_5898359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898359).length < 2 ^ (prefixWord ++ tailWord_5898359).sum := by decide
  have hdescent : baseEnd_5898359 < baseStart_5898359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898385 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_5898385 : Nat := 118140960795 + 5898385 * 2 ^ 59
def prefixEnd_5898385 : Nat := 4983230072969 + 3 ^ 40 * 5898385 * 2
def baseEnd_5898385 : Nat := 3028706590270010275261327

theorem tailTrace_5898385 : CollatzResearch.WordTrace tailWord_5898385 prefixEnd_5898385 3028706590270010275261327 := by
  unfold tailWord_5898385
  simp only [CollatzResearch.WordTrace]
  refine ⟨215131774736165983802768609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143421183157443989201845739 215131774736165983802768609)
  ·
    refine ⟨161348831052124487852076457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215131774736165983802768609 161348831052124487852076457)
    ·
      refine ⟨121011623289093365889057343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161348831052124487852076457 121011623289093365889057343)
      ·
        refine ⟨181517434933640048833586015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121011623289093365889057343 181517434933640048833586015)
        ·
          refine ⟨272276152400460073250379023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181517434933640048833586015 272276152400460073250379023)
          ·
            refine ⟨408414228600690109875568535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272276152400460073250379023 408414228600690109875568535)
            ·
              refine ⟨612621342901035164813352803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408414228600690109875568535 612621342901035164813352803)
              ·
                refine ⟨918932014351552747220029205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612621342901035164813352803 918932014351552747220029205)
                ·
                  refine ⟨43074938172729035025938869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 918932014351552747220029205 43074938172729035025938869)
                  ·
                    refine ⟨4038275453693347033681769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43074938172729035025938869 4038275453693347033681769)
                    ·
                      refine ⟨3028706590270010275261327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038275453693347033681769 3028706590270010275261327)
                      ·
                        rfl

theorem cell23_5898385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_5898385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898385 prefixEnd_5898385 := by exact prefixLift 5898385
  have htrace : WordTrace (prefixWord ++ tailWord_5898385) baseStart_5898385 baseEnd_5898385 := by
    simpa [prefixWord, tailWord_5898385, baseEnd_5898385] using wordTrace_append hprefix tailTrace_5898385
  have hstable : (prefixWord ++ tailWord_5898385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898385).length < 2 ^ (prefixWord ++ tailWord_5898385).sum := by decide
  have hdescent : baseEnd_5898385 < baseStart_5898385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898399 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 5]
def baseStart_5898399 : Nat := 118140960795 + 5898399 * 2 ^ 59
def prefixEnd_5898399 : Nat := 4983230072969 + 3 ^ 40 * 5898399 * 2
def baseEnd_5898399 : Nat := 336523753222130357831807

theorem tailTrace_5898399 : CollatzResearch.WordTrace tailWord_5898399 prefixEnd_5898399 336523753222130357831807 := by
  unfold tailWord_5898399
  simp only [CollatzResearch.WordTrace]
  refine ⟨215132285358115264193778251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143421523572076842795852167 215132285358115264193778251)
  ·
    refine ⟨322698428037172896290667377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215132285358115264193778251 322698428037172896290667377)
    ·
      refine ⟨242023821027879672218000533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322698428037172896290667377 242023821027879672218000533)
      ·
        refine ⟨11344866610681859635218775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242023821027879672218000533 11344866610681859635218775)
        ·
          refine ⟨17017299916022789452828163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11344866610681859635218775 17017299916022789452828163)
          ·
            refine ⟨25525949874034184179242245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17017299916022789452828163 25525949874034184179242245)
            ·
              refine ⟨4786115601381409533607921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25525949874034184179242245 4786115601381409533607921)
              ·
                refine ⟨3589586701036057150205941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786115601381409533607921 3589586701036057150205941)
                ·
                  refine ⟨336523753222130357831807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3589586701036057150205941 336523753222130357831807)
                  ·
                    rfl

theorem cell23_5898399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 5].length) (baseStart_5898399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898399 prefixEnd_5898399 := by exact prefixLift 5898399
  have htrace : WordTrace (prefixWord ++ tailWord_5898399) baseStart_5898399 baseEnd_5898399 := by
    simpa [prefixWord, tailWord_5898399, baseEnd_5898399] using wordTrace_append hprefix tailTrace_5898399
  have hstable : (prefixWord ++ tailWord_5898399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898399).length < 2 ^ (prefixWord ++ tailWord_5898399).sum := by decide
  have hdescent : baseEnd_5898399 < baseStart_5898399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898432 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_5898432 : Nat := 118140960795 + 5898432 * 2 ^ 59
def prefixEnd_5898432 : Nat := 4983230072969 + 3 ^ 40 * 5898432 * 2
def baseEnd_5898432 : Nat := 3028730723860771591373611

theorem tailTrace_5898432 : CollatzResearch.WordTrace tailWord_5898432 prefixEnd_5898432 3028730723860771591373611 := by
  unfold tailWord_5898432
  simp only [CollatzResearch.WordTrace]
  refine ⟨107566744483497855414864775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143422325977997140553153033 107566744483497855414864775)
  ·
    refine ⟨161350116725246783122297163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107566744483497855414864775 161350116725246783122297163)
    ·
      refine ⟨242025175087870174683445745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161350116725246783122297163 242025175087870174683445745)
      ·
        refine ⟨181518881315902631012584309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242025175087870174683445745 181518881315902631012584309)
        ·
          refine ⟨17017395123365871657429779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181518881315902631012584309 17017395123365871657429779)
          ·
            refine ⟨25526092685048807486144669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17017395123365871657429779 25526092685048807486144669)
            ·
              refine ⟨9572284756893302807304251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25526092685048807486144669 9572284756893302807304251)
              ·
                refine ⟨14358427135339954210956377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572284756893302807304251 14358427135339954210956377)
                ·
                  refine ⟨10768820351504965658217283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14358427135339954210956377 10768820351504965658217283)
                  ·
                    refine ⟨16153230527257448487325925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10768820351504965658217283 16153230527257448487325925)
                    ·
                      refine ⟨3028730723860771591373611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16153230527257448487325925 3028730723860771591373611)
                      ·
                        rfl

theorem cell23_5898432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_5898432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898432 prefixEnd_5898432 := by exact prefixLift 5898432
  have htrace : WordTrace (prefixWord ++ tailWord_5898432) baseStart_5898432 baseEnd_5898432 := by
    simpa [prefixWord, tailWord_5898432, baseEnd_5898432] using wordTrace_append hprefix tailTrace_5898432
  have hstable : (prefixWord ++ tailWord_5898432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898432).length < 2 ^ (prefixWord ++ tailWord_5898432).sum := by decide
  have hdescent : baseEnd_5898432 < baseStart_5898432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898448 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_5898448 : Nat := 118140960795 + 5898448 * 2 ^ 59
def prefixEnd_5898448 : Nat := 4983230072969 + 3 ^ 40 * 5898448 * 2
def baseEnd_5898448 : Nat := 3028738939551243528773537

theorem tailTrace_5898448 : CollatzResearch.WordTrace tailWord_5898448 prefixEnd_5898448 3028738939551243528773537 := by
  unfold tailWord_5898448
  simp only [CollatzResearch.WordTrace]
  refine ⟨107567036267468872781155999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143422715023291830374874665 107567036267468872781155999)
  ·
    refine ⟨161350554401203309171733999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107567036267468872781155999 161350554401203309171733999)
    ·
      refine ⟨242025831601804963757600999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161350554401203309171733999 242025831601804963757600999)
      ·
        refine ⟨363038747402707445636401499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242025831601804963757600999 363038747402707445636401499)
        ·
          refine ⟨544558121104061168454602249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363038747402707445636401499 544558121104061168454602249)
          ·
            refine ⟨408418590828045876340951687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544558121104061168454602249 408418590828045876340951687)
            ·
              refine ⟨612627886242068814511427531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408418590828045876340951687 612627886242068814511427531)
              ·
                refine ⟨918941829363103221767141297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612627886242068814511427531 918941829363103221767141297)
                ·
                  refine ⟨689206372022327416325355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918941829363103221767141297 689206372022327416325355973)
                  ·
                    refine ⟨129226194754186390561004245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689206372022327416325355973 129226194754186390561004245)
                    ·
                      refine ⟨3028738939551243528773537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129226194754186390561004245 3028738939551243528773537)
                      ·
                        rfl

theorem cell23_5898448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_5898448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898448 prefixEnd_5898448 := by exact prefixLift 5898448
  have htrace : WordTrace (prefixWord ++ tailWord_5898448) baseStart_5898448 baseEnd_5898448 := by
    simpa [prefixWord, tailWord_5898448, baseEnd_5898448] using wordTrace_append hprefix tailTrace_5898448
  have hstable : (prefixWord ++ tailWord_5898448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898448).length < 2 ^ (prefixWord ++ tailWord_5898448).sum := by decide
  have hdescent : baseEnd_5898448 < baseStart_5898448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898536 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5898536 : Nat := 118140960795 + 5898536 * 2 ^ 59
def prefixEnd_5898536 : Nat := 4983230072969 + 3 ^ 40 * 5898536 * 2
def baseEnd_5898536 : Nat := 1009594708616279728157711

theorem tailTrace_5898536 : CollatzResearch.WordTrace tailWord_5898536 prefixEnd_5898536 1009594708616279728157711 := by
  unfold tailWord_5898536
  simp only [CollatzResearch.WordTrace]
  refine ⟨107568641079309468295757731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143424854772412624394343641 107568641079309468295757731)
  ·
    refine ⟨161352961618964202443636597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107568641079309468295757731 161352961618964202443636597)
    ·
      refine ⟨15126840151777893979090931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161352961618964202443636597 15126840151777893979090931)
      ·
        refine ⟨22690260227666840968636397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126840151777893979090931 22690260227666840968636397)
        ·
          refine ⟨8508847585375065363238649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22690260227666840968636397 8508847585375065363238649)
          ·
            refine ⟨6381635689031299022428987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8508847585375065363238649 6381635689031299022428987)
            ·
              refine ⟨9572453533546948533643481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6381635689031299022428987 9572453533546948533643481)
              ·
                refine ⟨7179340150160211400232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9572453533546948533643481 7179340150160211400232611)
                ·
                  refine ⟨10769010225240317100348917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7179340150160211400232611 10769010225240317100348917)
                  ·
                    refine ⟨1009594708616279728157711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10769010225240317100348917 1009594708616279728157711)
                    ·
                      rfl

theorem cell23_5898536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5898536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898536 prefixEnd_5898536 := by exact prefixLift 5898536
  have htrace : WordTrace (prefixWord ++ tailWord_5898536) baseStart_5898536 baseEnd_5898536 := by
    simpa [prefixWord, tailWord_5898536, baseEnd_5898536] using wordTrace_append hprefix tailTrace_5898536
  have hstable : (prefixWord ++ tailWord_5898536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898536).length < 2 ^ (prefixWord ++ tailWord_5898536).sum := by decide
  have hdescent : baseEnd_5898536 < baseStart_5898536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898572 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_5898572 : Nat := 118140960795 + 5898572 * 2 ^ 59
def prefixEnd_5898572 : Nat := 4983230072969 + 3 ^ 40 * 5898572 * 2
def baseEnd_5898572 : Nat := 3028802611152401043622967

theorem tailTrace_5898572 : CollatzResearch.WordTrace tailWord_5898572 prefixEnd_5898572 3028802611152401043622967 := by
  unfold tailWord_5898572
  simp only [CollatzResearch.WordTrace]
  refine ⟨107569297593244257369912985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143425730124325676493217313 107569297593244257369912985)
  ·
    refine ⟨80676973194933193027434739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107569297593244257369912985 80676973194933193027434739)
    ·
      refine ⟨121015459792399789541152109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80676973194933193027434739 121015459792399789541152109)
      ·
        refine ⟨45380797422149921077932041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121015459792399789541152109 45380797422149921077932041)
        ·
          refine ⟨34035598066612440808449031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45380797422149921077932041 34035598066612440808449031)
          ·
            refine ⟨51053397099918661212673547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34035598066612440808449031 51053397099918661212673547)
            ·
              refine ⟨76580095649877991819010321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51053397099918661212673547 76580095649877991819010321)
              ·
                refine ⟨57435071737408493864257741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76580095649877991819010321 57435071737408493864257741)
                ·
                  refine ⟨21538151901528185199096653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57435071737408493864257741 21538151901528185199096653)
                  ·
                    refine ⟨8076806963073069449661245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21538151901528185199096653 8076806963073069449661245)
                    ·
                      refine ⟨3028802611152401043622967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8076806963073069449661245 3028802611152401043622967)
                      ·
                        rfl

theorem cell23_5898572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_5898572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898572 prefixEnd_5898572 := by exact prefixLift 5898572
  have htrace : WordTrace (prefixWord ++ tailWord_5898572) baseStart_5898572 baseEnd_5898572 := by
    simpa [prefixWord, tailWord_5898572, baseEnd_5898572] using wordTrace_append hprefix tailTrace_5898572
  have hstable : (prefixWord ++ tailWord_5898572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898572).length < 2 ^ (prefixWord ++ tailWord_5898572).sum := by decide
  have hdescent : baseEnd_5898572 < baseStart_5898572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898585 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5898585 : Nat := 118140960795 + 5898585 * 2 ^ 59
def prefixEnd_5898585 : Nat := 4983230072969 + 3 ^ 40 * 5898585 * 2
def baseEnd_5898585 : Nat := 3028809286400909492760407

theorem tailTrace_5898585 : CollatzResearch.WordTrace tailWord_5898585 prefixEnd_5898585 3028809286400909492760407 := by
  unfold tailWord_5898585
  simp only [CollatzResearch.WordTrace]
  refine ⟨215139069335441417960049209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143426046223627611973366139 215139069335441417960049209)
  ·
    refine ⟨161354302001581063470036907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215139069335441417960049209 161354302001581063470036907)
    ·
      refine ⟨242031453002371595205055361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161354302001581063470036907 242031453002371595205055361)
      ·
        refine ⟨181523589751778696403791521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242031453002371595205055361 181523589751778696403791521)
        ·
          refine ⟨136142692313834022302843641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181523589751778696403791521 136142692313834022302843641)
          ·
            refine ⟨102107019235375516727132731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136142692313834022302843641 102107019235375516727132731)
            ·
              refine ⟨153160528853063275090699097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102107019235375516727132731 153160528853063275090699097)
              ·
                refine ⟨114870396639797456318024323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153160528853063275090699097 114870396639797456318024323)
                ·
                  refine ⟨172305594959696184477036485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114870396639797456318024323 172305594959696184477036485)
                  ·
                    refine ⟨32307299054943034589444341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172305594959696184477036485 32307299054943034589444341)
                    ·
                      refine ⟨3028809286400909492760407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32307299054943034589444341 3028809286400909492760407)
                      ·
                        rfl

theorem cell23_5898585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5898585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898585 prefixEnd_5898585 := by exact prefixLift 5898585
  have htrace : WordTrace (prefixWord ++ tailWord_5898585) baseStart_5898585 baseEnd_5898585 := by
    simpa [prefixWord, tailWord_5898585, baseEnd_5898585] using wordTrace_append hprefix tailTrace_5898585
  have hstable : (prefixWord ++ tailWord_5898585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898585).length < 2 ^ (prefixWord ++ tailWord_5898585).sum := by decide
  have hdescent : baseEnd_5898585 < baseStart_5898585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898719 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_5898719 : Nat := 118140960795 + 5898719 * 2 ^ 59
def prefixEnd_5898719 : Nat := 4983230072969 + 3 ^ 40 * 5898719 * 2
def baseEnd_5898719 : Nat := 3028878092808611968484791

theorem tailTrace_5898719 : CollatzResearch.WordTrace tailWord_5898719 prefixEnd_5898719 3028878092808611968484791 := by
  unfold tailWord_5898719
  simp only [CollatzResearch.WordTrace]
  refine ⟨215143956716955958845427211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143429304477970639230284807 215143956716955958845427211)
  ·
    refine ⟨322715935075433938268140817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215143956716955958845427211 322715935075433938268140817)
    ·
      refine ⟨242036951306575453701105613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322715935075433938268140817 242036951306575453701105613)
      ·
        refine ⟨90763856739965795137914605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242036951306575453701105613 90763856739965795137914605)
        ·
          refine ⟨34036446277487173176717977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90763856739965795137914605 34036446277487173176717977)
          ·
            refine ⟨25527334708115379882538483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34036446277487173176717977 25527334708115379882538483)
            ·
              refine ⟨38291002062173069823807725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527334708115379882538483 38291002062173069823807725)
              ·
                refine ⟨14359125773314901183927897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38291002062173069823807725 14359125773314901183927897)
                ·
                  refine ⟨10769344329986175887945923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14359125773314901183927897 10769344329986175887945923)
                  ·
                    refine ⟨16154016494979263831918885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10769344329986175887945923 16154016494979263831918885)
                    ·
                      refine ⟨3028878092808611968484791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16154016494979263831918885 3028878092808611968484791)
                      ·
                        rfl

theorem cell23_5898719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_5898719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898719 prefixEnd_5898719 := by exact prefixLift 5898719
  have htrace : WordTrace (prefixWord ++ tailWord_5898719) baseStart_5898719 baseEnd_5898719 := by
    simpa [prefixWord, tailWord_5898719, baseEnd_5898719] using wordTrace_append hprefix tailTrace_5898719
  have hstable : (prefixWord ++ tailWord_5898719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898719).length < 2 ^ (prefixWord ++ tailWord_5898719).sum := by decide
  have hdescent : baseEnd_5898719 < baseStart_5898719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898732 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_5898732 : Nat := 118140960795 + 5898732 * 2 ^ 59
def prefixEnd_5898732 : Nat := 4983230072969 + 3 ^ 40 * 5898732 * 2
def baseEnd_5898732 : Nat := 3028884768057120417622231

theorem tailTrace_5898732 : CollatzResearch.WordTrace tailWord_5898732 prefixEnd_5898732 3028884768057120417622231 := by
  unfold tailWord_5898732
  simp only [CollatzResearch.WordTrace]
  refine ⟨107572215432954431032825225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143429620577272574710433633 107572215432954431032825225)
  ·
    refine ⟨80679161574715823274618919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107572215432954431032825225 80679161574715823274618919)
    ·
      refine ⟨121018742362073734911928379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80679161574715823274618919 121018742362073734911928379)
      ·
        refine ⟨181528113543110602367892569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121018742362073734911928379 181528113543110602367892569)
        ·
          refine ⟨136146085157332951775919427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181528113543110602367892569 136146085157332951775919427)
          ·
            refine ⟨204219127735999427663879141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136146085157332951775919427 204219127735999427663879141)
            ·
              refine ⟨38291086450499892686977339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204219127735999427663879141 38291086450499892686977339)
              ·
                refine ⟨57436629675749839030466009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38291086450499892686977339 57436629675749839030466009)
                ·
                  refine ⟨43077472256812379272849507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57436629675749839030466009 43077472256812379272849507)
                  ·
                    refine ⟨64616208385218568909274261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43077472256812379272849507 64616208385218568909274261)
                    ·
                      refine ⟨3028884768057120417622231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64616208385218568909274261 3028884768057120417622231)
                      ·
                        rfl

theorem cell23_5898732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_5898732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898732 prefixEnd_5898732 := by exact prefixLift 5898732
  have htrace : WordTrace (prefixWord ++ tailWord_5898732) baseStart_5898732 baseEnd_5898732 := by
    simpa [prefixWord, tailWord_5898732, baseEnd_5898732] using wordTrace_append hprefix tailTrace_5898732
  have hstable : (prefixWord ++ tailWord_5898732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898732).length < 2 ^ (prefixWord ++ tailWord_5898732).sum := by decide
  have hdescent : baseEnd_5898732 < baseStart_5898732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898739 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3]
def baseStart_5898739 : Nat := 118140960795 + 5898739 * 2 ^ 59
def prefixEnd_5898739 : Nat := 4983230072969 + 3 ^ 40 * 5898739 * 2
def baseEnd_5898739 : Nat := 3028888362421701890234699

theorem tailTrace_5898739 : CollatzResearch.WordTrace tailWord_5898739 prefixEnd_5898739 3028888362421701890234699 := by
  unfold tailWord_5898739
  simp only [CollatzResearch.WordTrace]
  refine ⟨215144686176883502261155271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143429790784589001507436847 215144686176883502261155271)
  ·
    refine ⟨322717029265325253391732907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215144686176883502261155271 322717029265325253391732907)
    ·
      refine ⟨484075543897987880087599361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322717029265325253391732907 484075543897987880087599361)
      ·
        refine ⟨363056657923490910065699521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484075543897987880087599361 363056657923490910065699521)
        ·
          refine ⟨272292493442618182549274641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363056657923490910065699521 272292493442618182549274641)
          ·
            refine ⟨204219370081963636911955981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272292493442618182549274641 204219370081963636911955981)
            ·
              refine ⟨76582263780736363841983493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204219370081963636911955981 76582263780736363841983493)
              ·
                refine ⟨14359174458888068220371905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76582263780736363841983493 14359174458888068220371905)
                ·
                  refine ⟨10769380844166051165278929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14359174458888068220371905 10769380844166051165278929)
                  ·
                    refine ⟨8077035633124538373959197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10769380844166051165278929 8077035633124538373959197)
                    ·
                      refine ⟨3028888362421701890234699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077035633124538373959197 3028888362421701890234699)
                      ·
                        rfl

theorem cell23_5898739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_5898739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898739 prefixEnd_5898739 := by exact prefixLift 5898739
  have htrace : WordTrace (prefixWord ++ tailWord_5898739) baseStart_5898739 baseEnd_5898739 := by
    simpa [prefixWord, tailWord_5898739, baseEnd_5898739] using wordTrace_append hprefix tailTrace_5898739
  have hstable : (prefixWord ++ tailWord_5898739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898739).length < 2 ^ (prefixWord ++ tailWord_5898739).sum := by decide
  have hdescent : baseEnd_5898739 < baseStart_5898739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898786 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5898786 : Nat := 118140960795 + 5898786 * 2 ^ 59
def prefixEnd_5898786 : Nat := 4983230072969 + 3 ^ 40 * 5898786 * 2
def baseEnd_5898786 : Nat := 3028912496012463206346983

theorem tailTrace_5898786 : CollatzResearch.WordTrace tailWord_5898786 prefixEnd_5898786 3028912496012463206346983 := by
  unfold tailWord_5898786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53786600101928307322029053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143430933605142152858744141 53786600101928307322029053)
  ·
    refine ⟨20169975038223115245760895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53786600101928307322029053 20169975038223115245760895)
    ·
      refine ⟨30254962557334672868641343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20169975038223115245760895 30254962557334672868641343)
      ·
        refine ⟨45382443836002009302962015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30254962557334672868641343 45382443836002009302962015)
        ·
          refine ⟨68073665754003013954443023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45382443836002009302962015 68073665754003013954443023)
          ·
            refine ⟨102110498631004520931664535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68073665754003013954443023 102110498631004520931664535)
            ·
              refine ⟨153165747946506781397496803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102110498631004520931664535 153165747946506781397496803)
              ·
                refine ⟨229748621919760172096245205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153165747946506781397496803 229748621919760172096245205)
                ·
                  refine ⟨5384733326244379033505747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 229748621919760172096245205 5384733326244379033505747)
                  ·
                    refine ⟨8077099989366568550258621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384733326244379033505747 8077099989366568550258621)
                    ·
                      refine ⟨3028912496012463206346983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077099989366568550258621 3028912496012463206346983)
                      ·
                        rfl

theorem cell23_5898786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5898786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898786 prefixEnd_5898786 := by exact prefixLift 5898786
  have htrace : WordTrace (prefixWord ++ tailWord_5898786) baseStart_5898786 baseEnd_5898786 := by
    simpa [prefixWord, tailWord_5898786, baseEnd_5898786] using wordTrace_append hprefix tailTrace_5898786
  have hstable : (prefixWord ++ tailWord_5898786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898786).length < 2 ^ (prefixWord ++ tailWord_5898786).sum := by decide
  have hdescent : baseEnd_5898786 < baseStart_5898786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898796 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_5898796 : Nat := 118140960795 + 5898796 * 2 ^ 59
def prefixEnd_5898796 : Nat := 4983230072969 + 3 ^ 40 * 5898796 * 2
def baseEnd_5898796 : Nat := 3028917630819008167221937

theorem tailTrace_5898796 : CollatzResearch.WordTrace tailWord_5898796 prefixEnd_5898796 3028917630819008167221937 := by
  unfold tailWord_5898796
  simp only [CollatzResearch.WordTrace]
  refine ⟨107573382568838500497990121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143431176758451333997320161 107573382568838500497990121)
  ·
    refine ⟨80680036926628875373492591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107573382568838500497990121 80680036926628875373492591)
    ·
      refine ⟨121020055389943313060238887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80680036926628875373492591 121020055389943313060238887)
      ·
        refine ⟨181530083084914969590358331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121020055389943313060238887 181530083084914969590358331)
        ·
          refine ⟨272295124627372454385537497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181530083084914969590358331 272295124627372454385537497)
          ·
            refine ⟨204221343470529340789153123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272295124627372454385537497 204221343470529340789153123)
            ·
              refine ⟨306332015205794011183729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204221343470529340789153123 306332015205794011183729685)
              ·
                refine ⟨14359313212771594274237329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306332015205794011183729685 14359313212771594274237329)
                ·
                  refine ⟨10769484909578695705677997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14359313212771594274237329 10769484909578695705677997)
                  ·
                    refine ⟨4038556841092010889629249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10769484909578695705677997 4038556841092010889629249)
                    ·
                      refine ⟨3028917630819008167221937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038556841092010889629249 3028917630819008167221937)
                      ·
                        rfl

theorem cell23_5898796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_5898796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898796 prefixEnd_5898796 := by exact prefixLift 5898796
  have htrace : WordTrace (prefixWord ++ tailWord_5898796) baseStart_5898796 baseEnd_5898796 := by
    simpa [prefixWord, tailWord_5898796, baseEnd_5898796] using wordTrace_append hprefix tailTrace_5898796
  have hstable : (prefixWord ++ tailWord_5898796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898796).length < 2 ^ (prefixWord ++ tailWord_5898796).sum := by decide
  have hdescent : baseEnd_5898796 < baseStart_5898796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898797 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5898797 : Nat := 118140960795 + 5898797 * 2 ^ 59
def prefixEnd_5898797 : Nat := 4983230072969 + 3 ^ 40 * 5898797 * 2
def baseEnd_5898797 : Nat := 1009639381433220887769811

theorem tailTrace_5898797 : CollatzResearch.WordTrace tailWord_5898797 prefixEnd_5898797 1009639381433220887769811 := by
  unfold tailWord_5898797
  simp only [CollatzResearch.WordTrace]
  refine ⟨215146801610673378166766645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143431201073782252111177763 215146801610673378166766645)
  ·
    refine ⟨20170012651000629203134373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215146801610673378166766645 20170012651000629203134373)
    ·
      refine ⟨3781877372062617975587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20170012651000629203134373 3781877372062617975587695)
      ·
        refine ⟨5672816058093926963381543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781877372062617975587695 5672816058093926963381543)
        ·
          refine ⟨8509224087140890445072315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5672816058093926963381543 8509224087140890445072315)
          ·
            refine ⟨12763836130711335667608473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509224087140890445072315 12763836130711335667608473)
            ·
              refine ⟨9572877098033501750706355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763836130711335667608473 9572877098033501750706355)
              ·
                refine ⟨14359315647050252626059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572877098033501750706355 14359315647050252626059533)
                ·
                  refine ⟨5384743367643844734772325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14359315647050252626059533 5384743367643844734772325)
                  ·
                    refine ⟨1009639381433220887769811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384743367643844734772325 1009639381433220887769811)
                    ·
                      rfl

theorem cell23_5898797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5898797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898797 prefixEnd_5898797 := by exact prefixLift 5898797
  have htrace : WordTrace (prefixWord ++ tailWord_5898797) baseStart_5898797 baseEnd_5898797 := by
    simpa [prefixWord, tailWord_5898797, baseEnd_5898797] using wordTrace_append hprefix tailTrace_5898797
  have hstable : (prefixWord ++ tailWord_5898797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898797).length < 2 ^ (prefixWord ++ tailWord_5898797).sum := by decide
  have hdescent : baseEnd_5898797 < baseStart_5898797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898803 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 1, 1, 3]
def baseStart_5898803 : Nat := 118140960795 + 5898803 * 2 ^ 59
def prefixEnd_5898803 : Nat := 4983230072969 + 3 ^ 40 * 5898803 * 2
def baseEnd_5898803 : Nat := 3028921225183589639834405

theorem tailTrace_5898803 : CollatzResearch.WordTrace tailWord_5898803 prefixEnd_5898803 3028921225183589639834405 := by
  unfold tailWord_5898803
  simp only [CollatzResearch.WordTrace]
  refine ⟨215147020448651641191485063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143431346965767760794323375 215147020448651641191485063)
  ·
    refine ⟨322720530672977461787227595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215147020448651641191485063 322720530672977461787227595)
    ·
      refine ⟨484080796009466192680841393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322720530672977461787227595 484080796009466192680841393)
      ·
        refine ⟨363060597007099644510631045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484080796009466192680841393 363060597007099644510631045)
        ·
          refine ⟨68073861938831183345743321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363060597007099644510631045 68073861938831183345743321)
          ·
            refine ⟨51055396454123387509307491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68073861938831183345743321 51055396454123387509307491)
            ·
              refine ⟨76583094681185081263961237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51055396454123387509307491 76583094681185081263961237)
              ·
                refine ⟨3589832563180550684248183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76583094681185081263961237 3589832563180550684248183)
                ·
                  refine ⟨5384748844770826026372275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589832563180550684248183 5384748844770826026372275)
                  ·
                    refine ⟨8077123267156239039558413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384748844770826026372275 8077123267156239039558413)
                    ·
                      refine ⟨3028921225183589639834405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077123267156239039558413 3028921225183589639834405)
                      ·
                        rfl

theorem cell23_5898803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 1, 3].length) (baseStart_5898803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898803 prefixEnd_5898803 := by exact prefixLift 5898803
  have htrace : WordTrace (prefixWord ++ tailWord_5898803) baseStart_5898803 baseEnd_5898803 := by
    simpa [prefixWord, tailWord_5898803, baseEnd_5898803] using wordTrace_append hprefix tailTrace_5898803
  have hstable : (prefixWord ++ tailWord_5898803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898803).length < 2 ^ (prefixWord ++ tailWord_5898803).sum := by decide
  have hdescent : baseEnd_5898803 < baseStart_5898803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898826 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_5898826 : Nat := 118140960795 + 5898826 * 2 ^ 59
def prefixEnd_5898826 : Nat := 4983230072969 + 3 ^ 40 * 5898826 * 2
def baseEnd_5898826 : Nat := 3028933035238643049846799

theorem tailTrace_5898826 : CollatzResearch.WordTrace tailWord_5898826 prefixEnd_5898826 3028933035238643049846799 := by
  unfold tailWord_5898826
  simp only [CollatzResearch.WordTrace]
  refine ⟨53786964831892079029893083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143431906218378877413048221 53786964831892079029893083)
  ·
    refine ⟨80680447247838118544839625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53786964831892079029893083 80680447247838118544839625)
    ·
      refine ⟨60510335435878588908629719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80680447247838118544839625 60510335435878588908629719)
      ·
        refine ⟨90765503153817883362944579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60510335435878588908629719 90765503153817883362944579)
        ·
          refine ⟨136148254730726825044416869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90765503153817883362944579 136148254730726825044416869)
          ·
            refine ⟨25527797762011279695828163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136148254730726825044416869 25527797762011279695828163)
            ·
              refine ⟨38291696643016919543742245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527797762011279695828163 38291696643016919543742245)
              ·
                refine ⟨7179693120565672414451671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38291696643016919543742245 7179693120565672414451671)
                ·
                  refine ⟨10769539680848508621677507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7179693120565672414451671 10769539680848508621677507)
                  ·
                    refine ⟨16154309521272762932516261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10769539680848508621677507 16154309521272762932516261)
                    ·
                      refine ⟨3028933035238643049846799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16154309521272762932516261 3028933035238643049846799)
                      ·
                        rfl

theorem cell23_5898826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_5898826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898826 prefixEnd_5898826 := by exact prefixLift 5898826
  have htrace : WordTrace (prefixWord ++ tailWord_5898826) baseStart_5898826 baseEnd_5898826 := by
    simpa [prefixWord, tailWord_5898826, baseEnd_5898826] using wordTrace_append hprefix tailTrace_5898826
  have hstable : (prefixWord ++ tailWord_5898826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898826).length < 2 ^ (prefixWord ++ tailWord_5898826).sum := by decide
  have hdescent : baseEnd_5898826 < baseStart_5898826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898836 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_5898836 : Nat := 118140960795 + 5898836 * 2 ^ 59
def prefixEnd_5898836 : Nat := 4983230072969 + 3 ^ 40 * 5898836 * 2
def baseEnd_5898836 : Nat := 1009646056681729336907251

theorem tailTrace_5898836 : CollatzResearch.WordTrace tailWord_5898836 prefixEnd_5898836 1009646056681729336907251 := by
  unfold tailWord_5898836
  simp only [CollatzResearch.WordTrace]
  refine ⟨107574112028766043913718181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143432149371688058551624241 107574112028766043913718181)
  ·
    refine ⟨20170146005393633233822159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107574112028766043913718181 20170146005393633233822159)
    ·
      refine ⟨30255219008090449850733239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20170146005393633233822159 30255219008090449850733239)
      ·
        refine ⟨45382828512135674776099859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30255219008090449850733239 45382828512135674776099859)
        ·
          refine ⟨68074242768203512164149789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45382828512135674776099859 68074242768203512164149789)
          ·
            refine ⟨25527841038076317061556171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68074242768203512164149789 25527841038076317061556171)
            ·
              refine ⟨38291761557114475592334257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527841038076317061556171 38291761557114475592334257)
              ·
                refine ⟨28718821167835856694250693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38291761557114475592334257 28718821167835856694250693)
                ·
                  refine ⟨5384778968969223130172005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28718821167835856694250693 5384778968969223130172005)
                  ·
                    refine ⟨1009646056681729336907251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384778968969223130172005 1009646056681729336907251)
                    ·
                      rfl

theorem cell23_5898836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_5898836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898836 prefixEnd_5898836 := by exact prefixLift 5898836
  have htrace : WordTrace (prefixWord ++ tailWord_5898836) baseStart_5898836 baseEnd_5898836 := by
    simpa [prefixWord, tailWord_5898836, baseEnd_5898836] using wordTrace_append hprefix tailTrace_5898836
  have hstable : (prefixWord ++ tailWord_5898836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898836).length < 2 ^ (prefixWord ++ tailWord_5898836).sum := by decide
  have hdescent : baseEnd_5898836 < baseStart_5898836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898839 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_5898839 : Nat := 118140960795 + 5898839 * 2 ^ 59
def prefixEnd_5898839 : Nat := 4983230072969 + 3 ^ 40 * 5898839 * 2
def baseEnd_5898839 : Nat := 3028939710487151498984239

theorem tailTrace_5898839 : CollatzResearch.WordTrace tailWord_5898839 prefixEnd_5898839 3028939710487151498984239 := by
  unfold tailWord_5898839
  simp only [CollatzResearch.WordTrace]
  refine ⟨215148333476521219339795571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143432222317680812893197047 215148333476521219339795571)
  ·
    refine ⟨322722500214781829009693357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215148333476521219339795571 322722500214781829009693357)
    ·
      refine ⟨121020937580543185878635009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322722500214781829009693357 121020937580543185878635009)
      ·
        refine ⟨90765703185407389408976257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121020937580543185878635009 90765703185407389408976257)
        ·
          refine ⟨68074277389055542056732193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90765703185407389408976257 68074277389055542056732193)
          ·
            refine ⟨51055708041791656542549145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68074277389055542056732193 51055708041791656542549145)
            ·
              refine ⟨38291781031343742406911859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51055708041791656542549145 38291781031343742406911859)
              ·
                refine ⟨57437671547015613610367789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38291781031343742406911859 57437671547015613610367789)
                ·
                  refine ⟨21539126830130855103887921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57437671547015613610367789 21539126830130855103887921)
                  ·
                    refine ⟨16154345122598141327915941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21539126830130855103887921 16154345122598141327915941)
                    ·
                      refine ⟨3028939710487151498984239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16154345122598141327915941 3028939710487151498984239)
                      ·
                        rfl

theorem cell23_5898839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_5898839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898839 prefixEnd_5898839 := by exact prefixLift 5898839
  have htrace : WordTrace (prefixWord ++ tailWord_5898839) baseStart_5898839 baseEnd_5898839 := by
    simpa [prefixWord, tailWord_5898839, baseEnd_5898839] using wordTrace_append hprefix tailTrace_5898839
  have hstable : (prefixWord ++ tailWord_5898839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898839).length < 2 ^ (prefixWord ++ tailWord_5898839).sum := by decide
  have hdescent : baseEnd_5898839 < baseStart_5898839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898849 : List Nat := [1, 2, 3, 1, 1, 6, 9]
def baseStart_5898849 : Nat := 118140960795 + 5898849 * 2 ^ 59
def prefixEnd_5898849 : Nat := 4983230072969 + 3 ^ 40 * 5898849 * 2
def baseEnd_5898849 : Nat := 37394380806095018022953

theorem tailTrace_5898849 : CollatzResearch.WordTrace tailWord_5898849 prefixEnd_5898849 37394380806095018022953 := by
  unfold tailWord_5898849
  simp only [CollatzResearch.WordTrace]
  refine ⟨215148698206484991047659601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143432465470989994031773067 215148698206484991047659601)
  ·
    refine ⟨161361523654863743285744701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215148698206484991047659601 161361523654863743285744701)
    ·
      refine ⟨60510571370573903732154263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161361523654863743285744701 60510571370573903732154263)
      ·
        refine ⟨90765857055860855598231395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60510571370573903732154263 90765857055860855598231395)
        ·
          refine ⟨136148785583791283397347093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90765857055860855598231395 136148785583791283397347093)
          ·
            refine ⟨6381974324240216409250645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136148785583791283397347093 6381974324240216409250645)
            ·
              refine ⟨37394380806095018022953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6381974324240216409250645 37394380806095018022953)
              ·
                rfl

theorem cell23_5898849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 9].length) (baseStart_5898849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898849 prefixEnd_5898849 := by exact prefixLift 5898849
  have htrace : WordTrace (prefixWord ++ tailWord_5898849) baseStart_5898849 baseEnd_5898849 := by
    simpa [prefixWord, tailWord_5898849, baseEnd_5898849] using wordTrace_append hprefix tailTrace_5898849
  have hstable : (prefixWord ++ tailWord_5898849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898849).length < 2 ^ (prefixWord ++ tailWord_5898849).sum := by decide
  have hdescent : baseEnd_5898849 < baseStart_5898849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3]
def baseStart_5898859 : Nat := 118140960795 + 5898859 * 2 ^ 59
def prefixEnd_5898859 : Nat := 4983230072969 + 3 ^ 40 * 5898859 * 2
def baseEnd_5898859 : Nat := 3028949980100241420734147

theorem tailTrace_5898859 : CollatzResearch.WordTrace tailWord_5898859 prefixEnd_5898859 3028949980100241420734147 := by
  unfold tailWord_5898859
  simp only [CollatzResearch.WordTrace]
  refine ⟨215149062936448762755523631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143432708624299175170349087 215149062936448762755523631)
  ·
    refine ⟨322723594404673144133285447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215149062936448762755523631 322723594404673144133285447)
    ·
      refine ⟨484085391607009716199928171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322723594404673144133285447 484085391607009716199928171)
      ·
        refine ⟨726128087410514574299892257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484085391607009716199928171 726128087410514574299892257)
        ·
          refine ⟨544596065557885930724919193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726128087410514574299892257 544596065557885930724919193)
          ·
            refine ⟨408447049168414448043689395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544596065557885930724919193 408447049168414448043689395)
            ·
              refine ⟨612670573752621672065534093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408447049168414448043689395 612670573752621672065534093)
              ·
                refine ⟨229751465157233127024575285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612670573752621672065534093 229751465157233127024575285)
                ·
                  refine ⟨21539199858490605658553933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229751465157233127024575285 21539199858490605658553933)
                  ·
                    refine ⟨8077199946933977121957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21539199858490605658553933 8077199946933977121957725)
                    ·
                      refine ⟨3028949980100241420734147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077199946933977121957725 3028949980100241420734147)
                      ·
                        rfl

theorem cell23_5898859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].length) (baseStart_5898859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898859 prefixEnd_5898859 := by exact prefixLift 5898859
  have htrace : WordTrace (prefixWord ++ tailWord_5898859) baseStart_5898859 baseEnd_5898859 := by
    simpa [prefixWord, tailWord_5898859, baseEnd_5898859] using wordTrace_append hprefix tailTrace_5898859
  have hstable : (prefixWord ++ tailWord_5898859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898859).length < 2 ^ (prefixWord ++ tailWord_5898859).sum := by decide
  have hdescent : baseEnd_5898859 < baseStart_5898859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898860 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_5898860 : Nat := 118140960795 + 5898860 * 2 ^ 59
def prefixEnd_5898860 : Nat := 4983230072969 + 3 ^ 40 * 5898860 * 2
def baseEnd_5898860 : Nat := 3028950493580895916821643

theorem tailTrace_5898860 : CollatzResearch.WordTrace tailWord_5898860 prefixEnd_5898860 3028950493580895916821643 := by
  unfold tailWord_5898860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107574549704722569963155017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143432732939630093284206689 107574549704722569963155017)
  ·
    refine ⟨80680912278541927472366263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107574549704722569963155017 80680912278541927472366263)
    ·
      refine ⟨121021368417812891208549395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80680912278541927472366263 121021368417812891208549395)
      ·
        refine ⟨181532052626719336812824093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121021368417812891208549395 181532052626719336812824093)
        ·
          refine ⟨68074519735019751304809035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181532052626719336812824093 68074519735019751304809035)
          ·
            refine ⟨102111779602529626957213553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68074519735019751304809035 102111779602529626957213553)
            ·
              refine ⟨76583834701897220217910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102111779602529626957213553 76583834701897220217910165)
              ·
                refine ⟨3589867251651432197714539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76583834701897220217910165 3589867251651432197714539)
                ·
                  refine ⟨5384800877477148296571809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589867251651432197714539 5384800877477148296571809)
                  ·
                    refine ⟨4038600658107861222428857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384800877477148296571809 4038600658107861222428857)
                    ·
                      refine ⟨3028950493580895916821643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038600658107861222428857 3028950493580895916821643)
                      ·
                        rfl

theorem cell23_5898860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_5898860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898860 prefixEnd_5898860 := by exact prefixLift 5898860
  have htrace : WordTrace (prefixWord ++ tailWord_5898860) baseStart_5898860 baseEnd_5898860 := by
    simpa [prefixWord, tailWord_5898860, baseEnd_5898860] using wordTrace_append hprefix tailTrace_5898860
  have hstable : (prefixWord ++ tailWord_5898860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898860).length < 2 ^ (prefixWord ++ tailWord_5898860).sum := by decide
  have hdescent : baseEnd_5898860 < baseStart_5898860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898866 : List Nat := [3, 2, 1, 2, 4, 1, 2, 8]
def baseStart_5898866 : Nat := 118140960795 + 5898866 * 2 ^ 59
def prefixEnd_5898866 : Nat := 4983230072969 + 3 ^ 40 * 5898866 * 2
def baseEnd_5898866 : Nat := 112183465720919366420245

theorem tailTrace_5898866 : CollatzResearch.WordTrace tailWord_5898866 prefixEnd_5898866 112183465720919366420245 := by
  unfold tailWord_5898866
  simp only [CollatzResearch.WordTrace]
  refine ⟨53787329561855850737757113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143432878831615601967352301 53787329561855850737757113)
  ·
    refine ⟨40340497171391888053317835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53787329561855850737757113 40340497171391888053317835)
    ·
      refine ⟨60510745757087832079976753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40340497171391888053317835 60510745757087832079976753)
      ·
        refine ⟨45383059317815874059982565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60510745757087832079976753 45383059317815874059982565)
        ·
          refine ⟨8509323622090476386246731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45383059317815874059982565 8509323622090476386246731)
          ·
            refine ⟨12763985433135714579370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509323622090476386246731 12763985433135714579370097)
            ·
              refine ⟨9572989074851785934527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763985433135714579370097 9572989074851785934527573)
              ·
                refine ⟨112183465720919366420245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9572989074851785934527573 112183465720919366420245)
                ·
                  rfl

theorem cell23_5898866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_5898866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898866 prefixEnd_5898866 := by exact prefixLift 5898866
  have htrace : WordTrace (prefixWord ++ tailWord_5898866) baseStart_5898866 baseEnd_5898866 := by
    simpa [prefixWord, tailWord_5898866, baseEnd_5898866] using wordTrace_append hprefix tailTrace_5898866
  have hstable : (prefixWord ++ tailWord_5898866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898866).length < 2 ^ (prefixWord ++ tailWord_5898866).sum := by decide
  have hdescent : baseEnd_5898866 < baseStart_5898866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898870 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_5898870 : Nat := 118140960795 + 5898870 * 2 ^ 59
def prefixEnd_5898870 : Nat := 4983230072969 + 3 ^ 40 * 5898870 * 2
def baseEnd_5898870 : Nat := 1009651876129146959232199

theorem tailTrace_5898870 : CollatzResearch.WordTrace tailWord_5898870 prefixEnd_5898870 1009651876129146959232199 := by
  unfold tailWord_5898870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446841508713056977135879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143432976092939274422782709 13446841508713056977135879)
  ·
    refine ⟨20170262263069585465703819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13446841508713056977135879 20170262263069585465703819)
    ·
      refine ⟨30255393394604378198555729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20170262263069585465703819 30255393394604378198555729)
      ·
        refine ⟨22691545045953283648916797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30255393394604378198555729 22691545045953283648916797)
        ·
          refine ⟨8509329392232481368343799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22691545045953283648916797 8509329392232481368343799)
          ·
            refine ⟨12763994088348722052515699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509329392232481368343799 12763994088348722052515699)
            ·
              refine ⟨19145991132523083078773549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12763994088348722052515699 19145991132523083078773549)
              ·
                refine ⟨7179746674696156154540081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19145991132523083078773549 7179746674696156154540081)
                ·
                  refine ⟨5384810006022117115905061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179746674696156154540081 5384810006022117115905061)
                  ·
                    refine ⟨1009651876129146959232199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384810006022117115905061 1009651876129146959232199)
                    ·
                      rfl

theorem cell23_5898870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_5898870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898870 prefixEnd_5898870 := by exact prefixLift 5898870
  have htrace : WordTrace (prefixWord ++ tailWord_5898870) baseStart_5898870 baseEnd_5898870 := by
    simpa [prefixWord, tailWord_5898870, baseEnd_5898870] using wordTrace_append hprefix tailTrace_5898870
  have hstable : (prefixWord ++ tailWord_5898870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898870).length < 2 ^ (prefixWord ++ tailWord_5898870).sum := by decide
  have hdescent : baseEnd_5898870 < baseStart_5898870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898967 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_5898967 : Nat := 118140960795 + 5898967 * 2 ^ 59
def prefixEnd_5898967 : Nat := 4983230072969 + 3 ^ 40 * 5898967 * 2
def baseEnd_5898967 : Nat := 3029005436010926998183651

theorem tailTrace_5898967 : CollatzResearch.WordTrace tailWord_5898967 prefixEnd_5898967 3029005436010926998183651 := by
  unfold tailWord_5898967
  simp only [CollatzResearch.WordTrace]
  refine ⟨215153002020057497200455155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143435334680038331466970103 215153002020057497200455155)
  ·
    refine ⟨322729503030086245800682733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215153002020057497200455155 322729503030086245800682733)
    ·
      refine ⟨121023563636282342175256025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322729503030086245800682733 121023563636282342175256025)
      ·
        refine ⟨90767672727211756631442019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121023563636282342175256025 90767672727211756631442019)
        ·
          refine ⟨136151509090817634947163029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90767672727211756631442019 136151509090817634947163029)
          ·
            refine ⟨6382101988632076638148267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136151509090817634947163029 6382101988632076638148267)
            ·
              refine ⟨9573152982948114957222401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382101988632076638148267 9573152982948114957222401)
              ·
                refine ⟨7179864737211086217916801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573152982948114957222401 7179864737211086217916801)
                ·
                  refine ⟨5384898552908314663437601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179864737211086217916801 5384898552908314663437601)
                  ·
                    refine ⟨4038673914681235997578201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384898552908314663437601 4038673914681235997578201)
                    ·
                      refine ⟨3029005436010926998183651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038673914681235997578201 3029005436010926998183651)
                      ·
                        rfl

theorem cell23_5898967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_5898967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898967 prefixEnd_5898967 := by exact prefixLift 5898967
  have htrace : WordTrace (prefixWord ++ tailWord_5898967) baseStart_5898967 baseEnd_5898967 := by
    simpa [prefixWord, tailWord_5898967, baseEnd_5898967] using wordTrace_append hprefix tailTrace_5898967
  have hstable : (prefixWord ++ tailWord_5898967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898967).length < 2 ^ (prefixWord ++ tailWord_5898967).sum := by decide
  have hdescent : baseEnd_5898967 < baseStart_5898967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898984 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5898984 : Nat := 118140960795 + 5898984 * 2 ^ 59
def prefixEnd_5898984 : Nat := 4983230072969 + 3 ^ 40 * 5898984 * 2
def baseEnd_5898984 : Nat := 3029014165182053431671073

theorem tailTrace_5898984 : CollatzResearch.WordTrace tailWord_5898984 prefixEnd_5898984 3029014165182053431671073 := by
  unfold tailWord_5898984
  simp only [CollatzResearch.WordTrace]
  refine ⟨107576811030497954551912003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143435748040663939402549337 107576811030497954551912003)
  ·
    refine ⟨161365216545746931827868005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107576811030497954551912003 161365216545746931827868005)
    ·
      refine ⟨30255978102327549717725251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161365216545746931827868005 30255978102327549717725251)
      ·
        refine ⟨45383967153491324576587877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30255978102327549717725251 45383967153491324576587877)
        ·
          refine ⟨8509493841279623358110227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45383967153491324576587877 8509493841279623358110227)
          ·
            refine ⟨12764240761919435037165341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509493841279623358110227 12764240761919435037165341)
            ·
              refine ⟨4786590285719788138937003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12764240761919435037165341 4786590285719788138937003)
              ·
                refine ⟨7179885428579682208405505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786590285719788138937003 7179885428579682208405505)
                ·
                  refine ⟨5384914071434761656304129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179885428579682208405505 5384914071434761656304129)
                  ·
                    refine ⟨4038685553576071242228097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384914071434761656304129 4038685553576071242228097)
                    ·
                      refine ⟨3029014165182053431671073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038685553576071242228097 3029014165182053431671073)
                      ·
                        rfl

theorem cell23_5898984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5898984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898984 prefixEnd_5898984 := by exact prefixLift 5898984
  have htrace : WordTrace (prefixWord ++ tailWord_5898984) baseStart_5898984 baseEnd_5898984 := by
    simpa [prefixWord, tailWord_5898984, baseEnd_5898984] using wordTrace_append hprefix tailTrace_5898984
  have hstable : (prefixWord ++ tailWord_5898984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898984).length < 2 ^ (prefixWord ++ tailWord_5898984).sum := by decide
  have hdescent : baseEnd_5898984 < baseStart_5898984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5898999 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 10]
def baseStart_5898999 : Nat := 118140960795 + 5898999 * 2 ^ 59
def prefixEnd_5898999 : Nat := 4983230072969 + 3 ^ 40 * 5898999 * 2
def baseEnd_5898999 : Nat := 1009673955797290290994501

theorem tailTrace_5898999 : CollatzResearch.WordTrace tailWord_5898999 prefixEnd_5898999 1009673955797290290994501 := by
  unfold tailWord_5898999
  simp only [CollatzResearch.WordTrace]
  refine ⟨215154169155941566665620051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143436112770627711110413367 215154169155941566665620051)
  ·
    refine ⟨322731253733912349998430077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215154169155941566665620051 322731253733912349998430077)
    ·
      refine ⟨121024220150217131249411279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322731253733912349998430077 121024220150217131249411279)
      ·
        refine ⟨181536330225325696874116919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121024220150217131249411279 181536330225325696874116919)
        ·
          refine ⟨272304495337988545311175379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181536330225325696874116919 272304495337988545311175379)
          ·
            refine ⟨408456743006982817966763069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272304495337988545311175379 408456743006982817966763069)
            ·
              refine ⟨153171278627618556737536151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408456743006982817966763069 153171278627618556737536151)
              ·
                refine ⟨229756917941427835106304227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153171278627618556737536151 229756917941427835106304227)
                ·
                  refine ⟨344635376912141752659456341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229756917941427835106304227 344635376912141752659456341)
                  ·
                    refine ⟨1009673955797290290994501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 344635376912141752659456341 1009673955797290290994501)
                    ·
                      rfl

theorem cell23_5898999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_5898999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5898999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5898999 prefixEnd_5898999 := by exact prefixLift 5898999
  have htrace : WordTrace (prefixWord ++ tailWord_5898999) baseStart_5898999 baseEnd_5898999 := by
    simpa [prefixWord, tailWord_5898999, baseEnd_5898999] using wordTrace_append hprefix tailTrace_5898999
  have hstable : (prefixWord ++ tailWord_5898999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5898999).length < 2 ^ (prefixWord ++ tailWord_5898999).sum := by decide
  have hdescent : baseEnd_5898999 < baseStart_5898999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5898999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899056 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_5899056 : Nat := 118140960795 + 5899056 * 2 ^ 59
def prefixEnd_5899056 : Nat := 4983230072969 + 3 ^ 40 * 5899056 * 2
def baseEnd_5899056 : Nat := 3029051135789177149970741

theorem tailTrace_5899056 : CollatzResearch.WordTrace tailWord_5899056 prefixEnd_5899056 3029051135789177149970741 := by
  unfold tailWord_5899056
  simp only [CollatzResearch.WordTrace]
  refine ⟨107578124058367532700222511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143437498744490043600296681 107578124058367532700222511)
  ·
    refine ⟨161367186087551299050333767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107578124058367532700222511 161367186087551299050333767)
    ·
      refine ⟨242050779131326948575500651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161367186087551299050333767 242050779131326948575500651)
      ·
        refine ⟨363076168696990422863250977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242050779131326948575500651 363076168696990422863250977)
        ·
          refine ⟨272307126522742817147438233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363076168696990422863250977 272307126522742817147438233)
          ·
            refine ⟨204230344892057112860578675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272307126522742817147438233 204230344892057112860578675)
            ·
              refine ⟨306345517338085669290868013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204230344892057112860578675 306345517338085669290868013)
              ·
                refine ⟨114879569001782125984075505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306345517338085669290868013 114879569001782125984075505)
                ·
                  refine ⟨86159676751336594488056629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114879569001782125984075505 86159676751336594488056629)
                  ·
                    refine ⟨8077469695437805733255309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86159676751336594488056629 8077469695437805733255309)
                    ·
                      refine ⟨3029051135789177149970741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077469695437805733255309 3029051135789177149970741)
                      ·
                        rfl

theorem cell23_5899056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_5899056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899056 prefixEnd_5899056 := by exact prefixLift 5899056
  have htrace : WordTrace (prefixWord ++ tailWord_5899056) baseStart_5899056 baseEnd_5899056 := by
    simpa [prefixWord, tailWord_5899056, baseEnd_5899056] using wordTrace_append hprefix tailTrace_5899056
  have hstable : (prefixWord ++ tailWord_5899056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899056).length < 2 ^ (prefixWord ++ tailWord_5899056).sum := by decide
  have hdescent : baseEnd_5899056 < baseStart_5899056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899084 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_5899084 : Nat := 118140960795 + 5899084 * 2 ^ 59
def prefixEnd_5899084 : Nat := 4983230072969 + 3 ^ 40 * 5899084 * 2
def baseEnd_5899084 : Nat := 1009688504415834346806871

theorem tailTrace_5899084 : CollatzResearch.WordTrace tailWord_5899084 prefixEnd_5899084 1009688504415834346806871 := by
  unfold tailWord_5899084
  simp only [CollatzResearch.WordTrace]
  refine ⟨107578634680316813091232153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143438179573755750788309537 107578634680316813091232153)
  ·
    refine ⟨80683976010237609818424115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107578634680316813091232153 80683976010237609818424115)
    ·
      refine ⟨121025964015356414727636173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80683976010237609818424115 121025964015356414727636173)
      ·
        refine ⟨45384736505758655522863565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121025964015356414727636173 45384736505758655522863565)
        ·
          refine ⟨17019276189659495821073837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45384736505758655522863565 17019276189659495821073837)
          ·
            refine ⟨6382228571122310932902689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17019276189659495821073837 6382228571122310932902689)
            ·
              refine ⟨4786671428341733199677017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382228571122310932902689 4786671428341733199677017)
              ·
                refine ⟨3590003571256299899757763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786671428341733199677017 3590003571256299899757763)
                ·
                  refine ⟨5385005356884449849636645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590003571256299899757763 5385005356884449849636645)
                  ·
                    refine ⟨1009688504415834346806871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385005356884449849636645 1009688504415834346806871)
                    ·
                      rfl

theorem cell23_5899084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_5899084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899084 prefixEnd_5899084 := by exact prefixLift 5899084
  have htrace : WordTrace (prefixWord ++ tailWord_5899084) baseStart_5899084 baseEnd_5899084 := by
    simpa [prefixWord, tailWord_5899084, baseEnd_5899084] using wordTrace_append hprefix tailTrace_5899084
  have hstable : (prefixWord ++ tailWord_5899084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899084).length < 2 ^ (prefixWord ++ tailWord_5899084).sum := by decide
  have hdescent : baseEnd_5899084 < baseStart_5899084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899086 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5899086 : Nat := 118140960795 + 5899086 * 2 ^ 59
def prefixEnd_5899086 : Nat := 4983230072969 + 3 ^ 40 * 5899086 * 2
def baseEnd_5899086 : Nat := 3029066540208812032595603

theorem tailTrace_5899086 : CollatzResearch.WordTrace tailWord_5899086 prefixEnd_5899086 3029066540208812032595603 := by
  unfold tailWord_5899086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26894667788328297565504639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143438228204417587016024741 26894667788328297565504639)
  ·
    refine ⟨40342001682492446348256959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26894667788328297565504639 40342001682492446348256959)
    ·
      refine ⟨60513002523738669522385439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40342001682492446348256959 60513002523738669522385439)
      ·
        refine ⟨90769503785608004283578159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60513002523738669522385439 90769503785608004283578159)
        ·
          refine ⟨136154255678412006425367239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90769503785608004283578159 136154255678412006425367239)
          ·
            refine ⟨204231383517618009638050859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136154255678412006425367239 204231383517618009638050859)
            ·
              refine ⟨306347075276427014457076289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204231383517618009638050859 306347075276427014457076289)
              ·
                refine ⟨229760306457320260842807217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306347075276427014457076289 229760306457320260842807217)
                ·
                  refine ⟨172320229842990195632105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229760306457320260842807217 172320229842990195632105413)
                  ·
                    refine ⟨32310043095560661681019765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172320229842990195632105413 32310043095560661681019765)
                    ·
                      refine ⟨3029066540208812032595603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32310043095560661681019765 3029066540208812032595603)
                      ·
                        rfl

theorem cell23_5899086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5899086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899086 prefixEnd_5899086 := by exact prefixLift 5899086
  have htrace : WordTrace (prefixWord ++ tailWord_5899086) baseStart_5899086 baseEnd_5899086 := by
    simpa [prefixWord, tailWord_5899086, baseEnd_5899086] using wordTrace_append hprefix tailTrace_5899086
  have hstable : (prefixWord ++ tailWord_5899086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899086).length < 2 ^ (prefixWord ++ tailWord_5899086).sum := by decide
  have hdescent : baseEnd_5899086 < baseStart_5899086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899090 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_5899090 : Nat := 118140960795 + 5899090 * 2 ^ 59
def prefixEnd_5899090 : Nat := 4983230072969 + 3 ^ 40 * 5899090 * 2
def baseEnd_5899090 : Nat := 3029068594131430016945585

theorem tailTrace_5899090 : CollatzResearch.WordTrace tailWord_5899090 prefixEnd_5899090 3029068594131430016945585 := by
  unfold tailWord_5899090
  simp only [CollatzResearch.WordTrace]
  refine ⟨53789372049652972301795681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143438325465741259471455149 53789372049652972301795681)
  ·
    refine ⟨40342029037239729226346761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53789372049652972301795681 40342029037239729226346761)
    ·
      refine ⟨30256521777929796919760071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40342029037239729226346761 30256521777929796919760071)
      ·
        refine ⟨45384782666894695379640107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30256521777929796919760071 45384782666894695379640107)
        ·
          refine ⟨68077174000342043069460161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45384782666894695379640107 68077174000342043069460161)
          ·
            refine ⟨51057880500256532302095121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68077174000342043069460161 51057880500256532302095121)
            ·
              refine ⟨38293410375192399226571341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51057880500256532302095121 38293410375192399226571341)
              ·
                refine ⟨14360028890697149709964253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38293410375192399226571341 14360028890697149709964253)
                ·
                  refine ⟨5385010834011431141236595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14360028890697149709964253 5385010834011431141236595)
                  ·
                    refine ⟨8077516251017146711854893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385010834011431141236595 8077516251017146711854893)
                    ·
                      refine ⟨3029068594131430016945585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077516251017146711854893 3029068594131430016945585)
                      ·
                        rfl

theorem cell23_5899090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_5899090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899090 prefixEnd_5899090 := by exact prefixLift 5899090
  have htrace : WordTrace (prefixWord ++ tailWord_5899090) baseStart_5899090 baseEnd_5899090 := by
    simpa [prefixWord, tailWord_5899090, baseEnd_5899090] using wordTrace_append hprefix tailTrace_5899090
  have hstable : (prefixWord ++ tailWord_5899090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899090).length < 2 ^ (prefixWord ++ tailWord_5899090).sum := by decide
  have hdescent : baseEnd_5899090 < baseStart_5899090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899130 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_5899130 : Nat := 118140960795 + 5899130 * 2 ^ 59
def prefixEnd_5899130 : Nat := 4983230072969 + 3 ^ 40 * 5899130 * 2
def baseEnd_5899130 : Nat := 3029089133357609860445401

theorem tailTrace_5899130 : CollatzResearch.WordTrace tailWord_5899130 prefixEnd_5899130 3029089133357609860445401 := by
  unfold tailWord_5899130
  simp only [CollatzResearch.WordTrace]
  refine ⟨53789736779616744009659711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143439298078977984025759229 53789736779616744009659711)
  ·
    refine ⟨80684605169425116014489567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53789736779616744009659711 80684605169425116014489567)
    ·
      refine ⟨121026907754137674021734351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80684605169425116014489567 121026907754137674021734351)
      ·
        refine ⟨181540361631206511032601527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121026907754137674021734351 181540361631206511032601527)
        ·
          refine ⟨272310542446809766548902291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181540361631206511032601527 272310542446809766548902291)
          ·
            refine ⟨408465813670214649823353437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272310542446809766548902291 408465813670214649823353437)
            ·
              refine ⟨153174680126330493683757539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408465813670214649823353437 153174680126330493683757539)
              ·
                refine ⟨229762020189495740525636309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153174680126330493683757539 229762020189495740525636309)
                ·
                  refine ⟨5385047348191306418569601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 229762020189495740525636309 5385047348191306418569601)
                  ·
                    refine ⟨4038785511143479813927201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385047348191306418569601 4038785511143479813927201)
                    ·
                      refine ⟨3029089133357609860445401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038785511143479813927201 3029089133357609860445401)
                      ·
                        rfl

theorem cell23_5899130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_5899130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899130 prefixEnd_5899130 := by exact prefixLift 5899130
  have htrace : WordTrace (prefixWord ++ tailWord_5899130) baseStart_5899130 baseEnd_5899130 := by
    simpa [prefixWord, tailWord_5899130, baseEnd_5899130] using wordTrace_append hprefix tailTrace_5899130
  have hstable : (prefixWord ++ tailWord_5899130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899130).length < 2 ^ (prefixWord ++ tailWord_5899130).sum := by decide
  have hdescent : baseEnd_5899130 < baseStart_5899130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899157 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_5899157 : Nat := 118140960795 + 5899157 * 2 ^ 59
def prefixEnd_5899157 : Nat := 4983230072969 + 3 ^ 40 * 5899157 * 2
def baseEnd_5899157 : Nat := 1009700999111760418269259

theorem tailTrace_5899157 : CollatzResearch.WordTrace tailWord_5899157 prefixEnd_5899157 1009700999111760418269259 := by
  unfold tailWord_5899157
  simp only [CollatzResearch.WordTrace]
  refine ⟨215159931889369159649871725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143439954592912773099914483 215159931889369159649871725)
  ·
    refine ⟨80684974458513434868701897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215159931889369159649871725 80684974458513434868701897)
    ·
      refine ⟨60513730843885076151526423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80684974458513434868701897 60513730843885076151526423)
      ·
        refine ⟨90770596265827614227289635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60513730843885076151526423 90770596265827614227289635)
        ·
          refine ⟨136155894398741421340934453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90770596265827614227289635 136155894398741421340934453)
          ·
            refine ⟨12764615099882008250712605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136155894398741421340934453 12764615099882008250712605)
            ·
              refine ⟨4786730662455753094017227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12764615099882008250712605 4786730662455753094017227)
              ·
                refine ⟨7180095993683629641025841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786730662455753094017227 7180095993683629641025841)
                ·
                  refine ⟨5385071995262722230769381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180095993683629641025841 5385071995262722230769381)
                  ·
                    refine ⟨1009700999111760418269259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385071995262722230769381 1009700999111760418269259)
                    ·
                      rfl

theorem cell23_5899157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_5899157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899157 prefixEnd_5899157 := by exact prefixLift 5899157
  have htrace : WordTrace (prefixWord ++ tailWord_5899157) baseStart_5899157 baseEnd_5899157 := by
    simpa [prefixWord, tailWord_5899157, baseEnd_5899157] using wordTrace_append hprefix tailTrace_5899157
  have hstable : (prefixWord ++ tailWord_5899157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899157).length < 2 ^ (prefixWord ++ tailWord_5899157).sum := by decide
  have hdescent : baseEnd_5899157 < baseStart_5899157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899167 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_5899167 : Nat := 118140960795 + 5899167 * 2 ^ 59
def prefixEnd_5899167 : Nat := 4983230072969 + 3 ^ 40 * 5899167 * 2
def baseEnd_5899167 : Nat := 3029108132141826215682731

theorem tailTrace_5899167 : CollatzResearch.WordTrace tailWord_5899167 prefixEnd_5899167 3029108132141826215682731 := by
  unfold tailWord_5899167
  simp only [CollatzResearch.WordTrace]
  refine ⟨215160296619332931357735755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143440197746221954238490503 215160296619332931357735755)
  ·
    refine ⟨322740444928999397036603633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215160296619332931357735755 322740444928999397036603633)
    ·
      refine ⟨242055333696749547777452725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322740444928999397036603633 242055333696749547777452725)
      ·
        refine ⟨22692687534070270104136193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242055333696749547777452725 22692687534070270104136193)
        ·
          refine ⟨17019515650552702578102145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22692687534070270104136193 17019515650552702578102145)
          ·
            refine ⟨12764636737914526933576609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17019515650552702578102145 12764636737914526933576609)
            ·
              refine ⟨9573477553435895200182457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764636737914526933576609 9573477553435895200182457)
              ·
                refine ⟨7180108165076921400136843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573477553435895200182457 7180108165076921400136843)
                ·
                  refine ⟨10770162247615382100205265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180108165076921400136843 10770162247615382100205265)
                  ·
                    refine ⟨8077621685711536575153949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10770162247615382100205265 8077621685711536575153949)
                    ·
                      refine ⟨3029108132141826215682731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077621685711536575153949 3029108132141826215682731)
                      ·
                        rfl

theorem cell23_5899167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_5899167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899167 prefixEnd_5899167 := by exact prefixLift 5899167
  have htrace : WordTrace (prefixWord ++ tailWord_5899167) baseStart_5899167 baseEnd_5899167 := by
    simpa [prefixWord, tailWord_5899167, baseEnd_5899167] using wordTrace_append hprefix tailTrace_5899167
  have hstable : (prefixWord ++ tailWord_5899167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899167).length < 2 ^ (prefixWord ++ tailWord_5899167).sum := by decide
  have hdescent : baseEnd_5899167 < baseStart_5899167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899170 : List Nat := [3, 3, 1, 2, 2, 1, 4, 7]
def baseStart_5899170 : Nat := 118140960795 + 5899170 * 2 ^ 59
def prefixEnd_5899170 : Nat := 4983230072969 + 3 ^ 40 * 5899170 * 2
def baseEnd_5899170 : Nat := 112189247132732951997971

theorem tailTrace_5899170 : CollatzResearch.WordTrace tailWord_5899170 prefixEnd_5899170 112189247132732951997971 := by
  unfold tailWord_5899170
  simp only [CollatzResearch.WordTrace]
  refine ⟨53790101509580515717523741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143440270692214708580063309 53790101509580515717523741)
  ·
    refine ⟨20171288066092693394071403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53790101509580515717523741 20171288066092693394071403)
    ·
      refine ⟨30256932099139040091107105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20171288066092693394071403 30256932099139040091107105)
      ·
        refine ⟨22692699074354280068330329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30256932099139040091107105 22692699074354280068330329)
        ·
          refine ⟨17019524305765710051247747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22692699074354280068330329 17019524305765710051247747)
          ·
            refine ⟨25529286458648565076871621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17019524305765710051247747 25529286458648565076871621)
            ·
              refine ⟨4786741210996605951913429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25529286458648565076871621 4786741210996605951913429)
              ·
                refine ⟨112189247132732951997971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4786741210996605951913429 112189247132732951997971)
                ·
                  rfl

theorem cell23_5899170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_5899170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899170 prefixEnd_5899170 := by exact prefixLift 5899170
  have htrace : WordTrace (prefixWord ++ tailWord_5899170) baseStart_5899170 baseEnd_5899170 := by
    simpa [prefixWord, tailWord_5899170, baseEnd_5899170] using wordTrace_append hprefix tailTrace_5899170
  have hstable : (prefixWord ++ tailWord_5899170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899170).length < 2 ^ (prefixWord ++ tailWord_5899170).sum := by decide
  have hdescent : baseEnd_5899170 < baseStart_5899170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899214 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_5899214 : Nat := 118140960795 + 5899214 * 2 ^ 59
def prefixEnd_5899214 : Nat := 4983230072969 + 3 ^ 40 * 5899214 * 2
def baseEnd_5899214 : Nat := 3029132265732587531795015

theorem tailTrace_5899214 : CollatzResearch.WordTrace tailWord_5899214 prefixEnd_5899214 3029132265732587531795015 := by
  unfold tailWord_5899214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895251356270332298087087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143441340566775105589797797 26895251356270332298087087)
  ·
    refine ⟨40342877034405498447130631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26895251356270332298087087 40342877034405498447130631)
    ·
      refine ⟨60514315551608247670695947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40342877034405498447130631 60514315551608247670695947)
      ·
        refine ⟨90771473327412371506043921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60514315551608247670695947 90771473327412371506043921)
        ·
          refine ⟨68078604995559278629532941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90771473327412371506043921 68078604995559278629532941)
          ·
            refine ⟨25529476873334729486074853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68078604995559278629532941 25529476873334729486074853)
            ·
              refine ⟨4786776913750261778639035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25529476873334729486074853 4786776913750261778639035)
              ·
                refine ⟨7180165370625392667958553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786776913750261778639035 7180165370625392667958553)
                ·
                  refine ⟨5385124027969044500968915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180165370625392667958553 5385124027969044500968915)
                  ·
                    refine ⟨8077686041953566751453373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385124027969044500968915 8077686041953566751453373)
                    ·
                      refine ⟨3029132265732587531795015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077686041953566751453373 3029132265732587531795015)
                      ·
                        rfl

theorem cell23_5899214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_5899214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899214 prefixEnd_5899214 := by exact prefixLift 5899214
  have htrace : WordTrace (prefixWord ++ tailWord_5899214) baseStart_5899214 baseEnd_5899214 := by
    simpa [prefixWord, tailWord_5899214, baseEnd_5899214] using wordTrace_append hprefix tailTrace_5899214
  have hstable : (prefixWord ++ tailWord_5899214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899214).length < 2 ^ (prefixWord ++ tailWord_5899214).sum := by decide
  have hdescent : baseEnd_5899214 < baseStart_5899214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899223 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_5899223 : Nat := 118140960795 + 5899223 * 2 ^ 59
def prefixEnd_5899223 : Nat := 4983230072969 + 3 ^ 40 * 5899223 * 2
def baseEnd_5899223 : Nat := 3029136887058477996582473

theorem tailTrace_5899223 : CollatzResearch.WordTrace tailWord_5899223 prefixEnd_5899223 3029136887058477996582473 := by
  unfold tailWord_5899223
  simp only [CollatzResearch.WordTrace]
  refine ⟨215162339107130052921774323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143441559404753368614516215 215162339107130052921774323)
  ·
    refine ⟨322743508660695079382661485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215162339107130052921774323 322743508660695079382661485)
    ·
      refine ⟨121028815747760654768498057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322743508660695079382661485 121028815747760654768498057)
      ·
        refine ⟨90771611810820491076373543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121028815747760654768498057 90771611810820491076373543)
        ·
          refine ⟨136157417716230736614560315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90771611810820491076373543 136157417716230736614560315)
          ·
            refine ⟨204236126574346104921840473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136157417716230736614560315 204236126574346104921840473)
            ·
              refine ⟨153177094930759578691380355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204236126574346104921840473 153177094930759578691380355)
              ·
                refine ⟨229765642396139368037070533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153177094930759578691380355 229765642396139368037070533)
                ·
                  refine ⟨43081057949276131506950725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229765642396139368037070533 43081057949276131506950725)
                  ·
                    refine ⟨8077698365489274657553261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43081057949276131506950725 8077698365489274657553261)
                    ·
                      refine ⟨3029136887058477996582473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077698365489274657553261 3029136887058477996582473)
                      ·
                        rfl

theorem cell23_5899223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_5899223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899223 prefixEnd_5899223 := by exact prefixLift 5899223
  have htrace : WordTrace (prefixWord ++ tailWord_5899223) baseStart_5899223 baseEnd_5899223 := by
    simpa [prefixWord, tailWord_5899223, baseEnd_5899223] using wordTrace_append hprefix tailTrace_5899223
  have hstable : (prefixWord ++ tailWord_5899223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899223).length < 2 ^ (prefixWord ++ tailWord_5899223).sum := by decide
  have hdescent : baseEnd_5899223 < baseStart_5899223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899224 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_5899224 : Nat := 118140960795 + 5899224 * 2 ^ 59
def prefixEnd_5899224 : Nat := 4983230072969 + 3 ^ 40 * 5899224 * 2
def baseEnd_5899224 : Nat := 3029137400539132492669969

theorem tailTrace_5899224 : CollatzResearch.WordTrace tailWord_5899224 prefixEnd_5899224 3029137400539132492669969 := by
  unfold tailWord_5899224
  simp only [CollatzResearch.WordTrace]
  refine ⟨107581187790063215046280363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143441583720084286728373817 107581187790063215046280363)
  ·
    refine ⟨161371781685094822569420545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107581187790063215046280363 161371781685094822569420545)
    ·
      refine ⟨121028836263821116927065409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161371781685094822569420545 121028836263821116927065409)
      ·
        refine ⟨90771627197865837695299057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121028836263821116927065409 90771627197865837695299057)
        ·
          refine ⟨68078720398399378271474293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90771627197865837695299057 68078720398399378271474293)
          ·
            refine ⟨6382380037349941712950715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68078720398399378271474293 6382380037349941712950715)
            ·
              refine ⟨9573570056024912569426073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382380037349941712950715 9573570056024912569426073)
              ·
                refine ⟨7180177542018684427069555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573570056024912569426073 7180177542018684427069555)
                ·
                  refine ⟨10770266313028026640604333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180177542018684427069555 10770266313028026640604333)
                  ·
                    refine ⟨4038849867385509990226625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10770266313028026640604333 4038849867385509990226625)
                    ·
                      refine ⟨3029137400539132492669969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4038849867385509990226625 3029137400539132492669969)
                      ·
                        rfl

theorem cell23_5899224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_5899224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899224 prefixEnd_5899224 := by exact prefixLift 5899224
  have htrace : WordTrace (prefixWord ++ tailWord_5899224) baseStart_5899224 baseEnd_5899224 := by
    simpa [prefixWord, tailWord_5899224, baseEnd_5899224] using wordTrace_append hprefix tailTrace_5899224
  have hstable : (prefixWord ++ tailWord_5899224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899224).length < 2 ^ (prefixWord ++ tailWord_5899224).sum := by decide
  have hdescent : baseEnd_5899224 < baseStart_5899224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899233 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5899233 : Nat := 118140960795 + 5899233 * 2 ^ 59
def prefixEnd_5899233 : Nat := 4983230072969 + 3 ^ 40 * 5899233 * 2
def baseEnd_5899233 : Nat := 3029142021865022957457427

theorem tailTrace_5899233 : CollatzResearch.WordTrace tailWord_5899233 prefixEnd_5899233 3029142021865022957457427 := by
  unfold tailWord_5899233
  simp only [CollatzResearch.WordTrace]
  refine ⟨215162703837093824629638353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143441802558062549753092235 215162703837093824629638353)
  ·
    refine ⟨161372027877820368472228765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215162703837093824629638353 161372027877820368472228765)
    ·
      refine ⟨60514510454182638177085787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161372027877820368472228765 60514510454182638177085787)
      ·
        refine ⟨90771765681273957265628681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60514510454182638177085787 90771765681273957265628681)
        ·
          refine ⟨68078824260955467949221511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90771765681273957265628681 68078824260955467949221511)
          ·
            refine ⟨102118236391433201923832267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68078824260955467949221511 102118236391433201923832267)
            ·
              refine ⟨153177354587149802885748401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102118236391433201923832267 153177354587149802885748401)
              ·
                refine ⟨114883015940362352164311301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153177354587149802885748401 114883015940362352164311301)
                ·
                  refine ⟨21540565488817941030808369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114883015940362352164311301 21540565488817941030808369)
                  ·
                    refine ⟨16155424116613455773106277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21540565488817941030808369 16155424116613455773106277)
                    ·
                      refine ⟨3029142021865022957457427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16155424116613455773106277 3029142021865022957457427)
                      ·
                        rfl

theorem cell23_5899233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5899233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899233 prefixEnd_5899233 := by exact prefixLift 5899233
  have htrace : WordTrace (prefixWord ++ tailWord_5899233) baseStart_5899233 baseEnd_5899233 := by
    simpa [prefixWord, tailWord_5899233, baseEnd_5899233] using wordTrace_append hprefix tailTrace_5899233
  have hstable : (prefixWord ++ tailWord_5899233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899233).length < 2 ^ (prefixWord ++ tailWord_5899233).sum := by decide
  have hdescent : baseEnd_5899233 < baseStart_5899233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899273 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_5899273 : Nat := 118140960795 + 5899273 * 2 ^ 59
def prefixEnd_5899273 : Nat := 4983230072969 + 3 ^ 40 * 5899273 * 2
def baseEnd_5899273 : Nat := 1009720853697067600319081

theorem tailTrace_5899273 : CollatzResearch.WordTrace tailWord_5899273 prefixEnd_5899273 1009720853697067600319081 := by
  unfold tailWord_5899273
  simp only [CollatzResearch.WordTrace]
  refine ⟨215164162756948911461094473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143442775171299274307396315 215164162756948911461094473)
  ·
    refine ⟨161373122067711683595820855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215164162756948911461094473 161373122067711683595820855)
    ·
      refine ⟨242059683101567525393731283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161373122067711683595820855 242059683101567525393731283)
      ·
        refine ⟨363089524652351288090596925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242059683101567525393731283 363089524652351288090596925)
        ·
          refine ⟨136158571744631733033973847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363089524652351288090596925 136158571744631733033973847)
          ·
            refine ⟨204237857616947599550960771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136158571744631733033973847 204237857616947599550960771)
            ·
              refine ⟨306356786425421399326441157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204237857616947599550960771 306356786425421399326441157)
              ·
                refine ⟨57441897454766512373707717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306356786425421399326441157 57441897454766512373707717)
                ·
                  refine ⟨10770355772768721070070197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57441897454766512373707717 10770355772768721070070197)
                  ·
                    refine ⟨1009720853697067600319081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10770355772768721070070197 1009720853697067600319081)
                    ·
                      rfl

theorem cell23_5899273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_5899273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899273 prefixEnd_5899273 := by exact prefixLift 5899273
  have htrace : WordTrace (prefixWord ++ tailWord_5899273) baseStart_5899273 baseEnd_5899273 := by
    simpa [prefixWord, tailWord_5899273, baseEnd_5899273] using wordTrace_append hprefix tailTrace_5899273
  have hstable : (prefixWord ++ tailWord_5899273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899273).length < 2 ^ (prefixWord ++ tailWord_5899273).sum := by decide
  have hdescent : baseEnd_5899273 < baseStart_5899273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_5899323 : Nat := 118140960795 + 5899323 * 2 ^ 59
def prefixEnd_5899323 : Nat := 4983230072969 + 3 ^ 40 * 5899323 * 2
def baseEnd_5899323 : Nat := 3029188235123927605332013

theorem tailTrace_5899323 : CollatzResearch.WordTrace tailWord_5899323 prefixEnd_5899323 3029188235123927605332013 := by
  unfold tailWord_5899323
  simp only [CollatzResearch.WordTrace]
  refine ⟨215165986406767770000414623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143443990937845180000276415 215165986406767770000414623)
  ·
    refine ⟨322748979610151655000621935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215165986406767770000414623 322748979610151655000621935)
    ·
      refine ⟨484123469415227482500932903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322748979610151655000621935 484123469415227482500932903)
      ·
        refine ⟨726185204122841223751399355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484123469415227482500932903 726185204122841223751399355)
        ·
          refine ⟨1089277806184261835627099033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726185204122841223751399355 1089277806184261835627099033)
          ·
            refine ⟨816958354638196376720324275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089277806184261835627099033 816958354638196376720324275)
            ·
              refine ⟨1225437531957294565080486413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816958354638196376720324275 1225437531957294565080486413)
              ·
                refine ⟨459539074483985461905182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1225437531957294565080486413 459539074483985461905182405)
                ·
                  refine ⟨86163576465747274107221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459539074483985461905182405 86163576465747274107221701)
                  ·
                    refine ⟨16155670587327613895104069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86163576465747274107221701 16155670587327613895104069)
                    ·
                      refine ⟨3029188235123927605332013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16155670587327613895104069 3029188235123927605332013)
                      ·
                        rfl

theorem cell23_5899323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_5899323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899323 prefixEnd_5899323 := by exact prefixLift 5899323
  have htrace : WordTrace (prefixWord ++ tailWord_5899323) baseStart_5899323 baseEnd_5899323 := by
    simpa [prefixWord, tailWord_5899323, baseEnd_5899323] using wordTrace_append hprefix tailTrace_5899323
  have hstable : (prefixWord ++ tailWord_5899323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899323).length < 2 ^ (prefixWord ++ tailWord_5899323).sum := by decide
  have hdescent : baseEnd_5899323 < baseStart_5899323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5899353 : Nat := 118140960795 + 5899353 * 2 ^ 59
def prefixEnd_5899353 : Nat := 4983230072969 + 3 ^ 40 * 5899353 * 2
def baseEnd_5899353 : Nat := 3029203639543562487956875

theorem tailTrace_5899353 : CollatzResearch.WordTrace tailWord_5899353 prefixEnd_5899353 3029203639543562487956875 := by
  unfold tailWord_5899353
  simp only [CollatzResearch.WordTrace]
  refine ⟨215167080596659085124006713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143444720397772723416004475 215167080596659085124006713)
  ·
    refine ⟨161375310447494313843005035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215167080596659085124006713 161375310447494313843005035)
    ·
      refine ⟨242062965671241470764507553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161375310447494313843005035 242062965671241470764507553)
      ·
        refine ⟨181547224253431103073380665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242062965671241470764507553 181547224253431103073380665)
        ·
          refine ⟨136160418190073327305035499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181547224253431103073380665 136160418190073327305035499)
          ·
            refine ⟨204240627285109990957553249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136160418190073327305035499 204240627285109990957553249)
            ·
              refine ⟨153180470463832493218164937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204240627285109990957553249 153180470463832493218164937)
              ·
                refine ⟨114885352847874369913623703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153180470463832493218164937 114885352847874369913623703)
                ·
                  refine ⟨172328029271811554870435555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114885352847874369913623703 172328029271811554870435555)
                  ·
                    refine ⟨258492043907717332305653333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172328029271811554870435555 258492043907717332305653333)
                    ·
                      refine ⟨3029203639543562487956875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 258492043907717332305653333 3029203639543562487956875)
                      ·
                        rfl

theorem cell23_5899353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5899353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899353 prefixEnd_5899353 := by exact prefixLift 5899353
  have htrace : WordTrace (prefixWord ++ tailWord_5899353) baseStart_5899353 baseEnd_5899353 := by
    simpa [prefixWord, tailWord_5899353, baseEnd_5899353] using wordTrace_append hprefix tailTrace_5899353
  have hstable : (prefixWord ++ tailWord_5899353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899353).length < 2 ^ (prefixWord ++ tailWord_5899353).sum := by decide
  have hdescent : baseEnd_5899353 < baseStart_5899353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899377 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_5899377 : Nat := 118140960795 + 5899377 * 2 ^ 59
def prefixEnd_5899377 : Nat := 4983230072969 + 3 ^ 40 * 5899377 * 2
def baseEnd_5899377 : Nat := 3029215963079270394056765

theorem tailTrace_5899377 : CollatzResearch.WordTrace tailWord_5899377 prefixEnd_5899377 3029215963079270394056765 := by
  unfold tailWord_5899377
  simp only [CollatzResearch.WordTrace]
  refine ⟨215167955948572137222880385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143445303965714758148586923 215167955948572137222880385)
  ·
    refine ⟨161375966961429102917160289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215167955948572137222880385 161375966961429102917160289)
    ·
      refine ⟨121031975221071827187870217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161375966961429102917160289 121031975221071827187870217)
      ·
        refine ⟨90773981415803870390902663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121031975221071827187870217 90773981415803870390902663)
        ·
          refine ⟨136160972123705805586353995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90773981415803870390902663 136160972123705805586353995)
          ·
            refine ⟨204241458185558708379530993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136160972123705805586353995 204241458185558708379530993)
            ·
              refine ⟨153181093639169031284648245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204241458185558708379530993 153181093639169031284648245)
              ·
                refine ⟨14360727528672096682935773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153181093639169031284648245 14360727528672096682935773)
                ·
                  refine ⟨5385272823252036256100915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14360727528672096682935773 5385272823252036256100915)
                  ·
                    refine ⟨8077909234878054384151373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385272823252036256100915 8077909234878054384151373)
                    ·
                      refine ⟨3029215963079270394056765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077909234878054384151373 3029215963079270394056765)
                      ·
                        rfl

theorem cell23_5899377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_5899377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899377 prefixEnd_5899377 := by exact prefixLift 5899377
  have htrace : WordTrace (prefixWord ++ tailWord_5899377) baseStart_5899377 baseEnd_5899377 := by
    simpa [prefixWord, tailWord_5899377, baseEnd_5899377] using wordTrace_append hprefix tailTrace_5899377
  have hstable : (prefixWord ++ tailWord_5899377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899377).length < 2 ^ (prefixWord ++ tailWord_5899377).sum := by decide
  have hdescent : baseEnd_5899377 < baseStart_5899377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899397 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_5899397 : Nat := 118140960795 + 5899397 * 2 ^ 59
def prefixEnd_5899397 : Nat := 4983230072969 + 3 ^ 40 * 5899397 * 2
def baseEnd_5899397 : Nat := 1009742077564120105268891

theorem tailTrace_5899397 : CollatzResearch.WordTrace tailWord_5899397 prefixEnd_5899397 1009742077564120105268891 := by
  unfold tailWord_5899397
  simp only [CollatzResearch.WordTrace]
  refine ⟨215168685408499680638608445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143445790272333120425738963 215168685408499680638608445)
  ·
    refine ⟨80688257028187380239478167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215168685408499680638608445 80688257028187380239478167)
    ·
      refine ⟨121032385542281070359217251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80688257028187380239478167 121032385542281070359217251)
      ·
        refine ⟨181548578313421605538825877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121032385542281070359217251 181548578313421605538825877)
        ·
          refine ⟨8510089608441637759632463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181548578313421605538825877 8510089608441637759632463)
          ·
            refine ⟨12765134412662456639448695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510089608441637759632463 12765134412662456639448695)
            ·
              refine ⟨19147701618993684959173043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765134412662456639448695 19147701618993684959173043)
              ·
                refine ⟨28721552428490527438759565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147701618993684959173043 28721552428490527438759565)
                ·
                  refine ⟨10770582160683947789534837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28721552428490527438759565 10770582160683947789534837)
                  ·
                    refine ⟨1009742077564120105268891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10770582160683947789534837 1009742077564120105268891)
                    ·
                      rfl

theorem cell23_5899397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_5899397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899397 prefixEnd_5899397 := by exact prefixLift 5899397
  have htrace : WordTrace (prefixWord ++ tailWord_5899397) baseStart_5899397 baseEnd_5899397 := by
    simpa [prefixWord, tailWord_5899397, baseEnd_5899397] using wordTrace_append hprefix tailTrace_5899397
  have hstable : (prefixWord ++ tailWord_5899397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899397).length < 2 ^ (prefixWord ++ tailWord_5899397).sum := by decide
  have hdescent : baseEnd_5899397 < baseStart_5899397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899428 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_5899428 : Nat := 118140960795 + 5899428 * 2 ^ 59
def prefixEnd_5899428 : Nat := 4983230072969 + 3 ^ 40 * 5899428 * 2
def baseEnd_5899428 : Nat := 3029242150592649694519031

theorem tailTrace_5899428 : CollatzResearch.WordTrace tailWord_5899428 prefixEnd_5899428 3029242150592649694519031 := by
  unfold tailWord_5899428
  simp only [CollatzResearch.WordTrace]
  refine ⟨107584908035693686466493469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143446544047591581955324625 107584908035693686466493469)
  ·
    refine ⟨40344340513385132424935051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107584908035693686466493469 40344340513385132424935051)
    ·
      refine ⟨60516510770077698637402577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40344340513385132424935051 60516510770077698637402577)
      ·
        refine ⟨45387383077558273978051933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60516510770077698637402577 45387383077558273978051933)
        ·
          refine ⟨17020268654084352741769475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45387383077558273978051933 17020268654084352741769475)
          ·
            refine ⟨25530402981126529112654213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020268654084352741769475 25530402981126529112654213)
            ·
              refine ⟨4786950558961224208622665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25530402981126529112654213 4786950558961224208622665)
              ·
                refine ⟨3590212919220918156466999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786950558961224208622665 3590212919220918156466999)
                ·
                  refine ⟨5385319378831377234700499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590212919220918156466999 5385319378831377234700499)
                  ·
                    refine ⟨8077979068247065852050749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385319378831377234700499 8077979068247065852050749)
                    ·
                      refine ⟨3029242150592649694519031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8077979068247065852050749 3029242150592649694519031)
                      ·
                        rfl

theorem cell23_5899428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_5899428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899428 prefixEnd_5899428 := by exact prefixLift 5899428
  have htrace : WordTrace (prefixWord ++ tailWord_5899428) baseStart_5899428 baseEnd_5899428 := by
    simpa [prefixWord, tailWord_5899428, baseEnd_5899428] using wordTrace_append hprefix tailTrace_5899428
  have hstable : (prefixWord ++ tailWord_5899428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899428).length < 2 ^ (prefixWord ++ tailWord_5899428).sum := by decide
  have hdescent : baseEnd_5899428 < baseStart_5899428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899434 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5899434 : Nat := 118140960795 + 5899434 * 2 ^ 59
def prefixEnd_5899434 : Nat := 4983230072969 + 3 ^ 40 * 5899434 * 2
def baseEnd_5899434 : Nat := 3029245231476576671044003

theorem tailTrace_5899434 : CollatzResearch.WordTrace tailWord_5899434 prefixEnd_5899434 3029245231476576671044003 := by
  unfold tailWord_5899434
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792508727341408989426339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143446689939577090638470237 53792508727341408989426339)
  ·
    refine ⟨80688763091012113484139509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53792508727341408989426339 80688763091012113484139509)
    ·
      refine ⟨7564571539782385639138079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80688763091012113484139509 7564571539782385639138079)
      ·
        refine ⟨11346857309673578458707119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564571539782385639138079 11346857309673578458707119)
        ·
          refine ⟨17020285964510367688060679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346857309673578458707119 17020285964510367688060679)
          ·
            refine ⟨25530428946765551532091019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020285964510367688060679 25530428946765551532091019)
            ·
              refine ⟨38295643420148327298136529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530428946765551532091019 38295643420148327298136529)
              ·
                refine ⟨28721732565111245473602397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38295643420148327298136529 28721732565111245473602397)
                ·
                  refine ⟨10770649711916717052600899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28721732565111245473602397 10770649711916717052600899)
                  ·
                    refine ⟨16155974567875075578901349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10770649711916717052600899 16155974567875075578901349)
                    ·
                      refine ⟨3029245231476576671044003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16155974567875075578901349 3029245231476576671044003)
                      ·
                        rfl

theorem cell23_5899434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5899434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899434 prefixEnd_5899434 := by exact prefixLift 5899434
  have htrace : WordTrace (prefixWord ++ tailWord_5899434) baseStart_5899434 baseEnd_5899434 := by
    simpa [prefixWord, tailWord_5899434, baseEnd_5899434] using wordTrace_append hprefix tailTrace_5899434
  have hstable : (prefixWord ++ tailWord_5899434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899434).length < 2 ^ (prefixWord ++ tailWord_5899434).sum := by decide
  have hdescent : baseEnd_5899434 < baseStart_5899434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899447 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_5899447 : Nat := 118140960795 + 5899447 * 2 ^ 59
def prefixEnd_5899447 : Nat := 4983230072969 + 3 ^ 40 * 5899447 * 2
def baseEnd_5899447 : Nat := 3029251906725085120181443

theorem tailTrace_5899447 : CollatzResearch.WordTrace tailWord_5899447 prefixEnd_5899447 3029251906725085120181443 := by
  unfold tailWord_5899447
  simp only [CollatzResearch.WordTrace]
  refine ⟨215170509058318539177928595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143447006038879026118619063 215170509058318539177928595)
  ·
    refine ⟨322755763587477808766892893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215170509058318539177928595 322755763587477808766892893)
    ·
      refine ⟨121033411345304178287584835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322755763587477808766892893 121033411345304178287584835)
      ·
        refine ⟨181550117017956267431377253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121033411345304178287584835 181550117017956267431377253)
        ·
          refine ⟨34040646940866800143383235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181550117017956267431377253 34040646940866800143383235)
          ·
            refine ⟨51060970411300200215074853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34040646940866800143383235 51060970411300200215074853)
            ·
              refine ⟨9573931952118787540326535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51060970411300200215074853 9573931952118787540326535)
              ·
                refine ⟨14360897928178181310489803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9573931952118787540326535 14360897928178181310489803)
                ·
                  refine ⟨21541346892267271965734705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14360897928178181310489803 21541346892267271965734705)
                  ·
                    refine ⟨16156010169200453974301029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21541346892267271965734705 16156010169200453974301029)
                    ·
                      refine ⟨3029251906725085120181443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16156010169200453974301029 3029251906725085120181443)
                      ·
                        rfl

theorem cell23_5899447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_5899447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899447 prefixEnd_5899447 := by exact prefixLift 5899447
  have htrace : WordTrace (prefixWord ++ tailWord_5899447) baseStart_5899447 baseEnd_5899447 := by
    simpa [prefixWord, tailWord_5899447, baseEnd_5899447] using wordTrace_append hprefix tailTrace_5899447
  have hstable : (prefixWord ++ tailWord_5899447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899447).length < 2 ^ (prefixWord ++ tailWord_5899447).sum := by decide
  have hdescent : baseEnd_5899447 < baseStart_5899447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899454 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5899454 : Nat := 118140960795 + 5899454 * 2 ^ 59
def prefixEnd_5899454 : Nat := 4983230072969 + 3 ^ 40 * 5899454 * 2
def baseEnd_5899454 : Nat := 3029255501089666592793911

theorem tailTrace_5899454 : CollatzResearch.WordTrace tailWord_5899454 prefixEnd_5899454 3029255501089666592793911 := by
  unfold tailWord_5899454
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896345546161647421679177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143447176246195452915622277 26896345546161647421679177)
  ·
    refine ⟨20172259159621235566259383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26896345546161647421679177 20172259159621235566259383)
    ·
      refine ⟨30258388739431853349389075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172259159621235566259383 30258388739431853349389075)
      ·
        refine ⟨45387583109147780024083613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30258388739431853349389075 45387583109147780024083613)
        ·
          refine ⟨17020343665930417509031355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45387583109147780024083613 17020343665930417509031355)
          ·
            refine ⟨25530515498895626263547033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020343665930417509031355 25530515498895626263547033)
            ·
              refine ⟨19147886624171719697660275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25530515498895626263547033 19147886624171719697660275)
              ·
                refine ⟨28721829936257579546490413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147886624171719697660275 28721829936257579546490413)
                ·
                  refine ⟨10770686226096592329933905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28721829936257579546490413 10770686226096592329933905)
                  ·
                    refine ⟨8078014669572444247450429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10770686226096592329933905 8078014669572444247450429)
                    ·
                      refine ⟨3029255501089666592793911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078014669572444247450429 3029255501089666592793911)
                      ·
                        rfl

theorem cell23_5899454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5899454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899454 prefixEnd_5899454 := by exact prefixLift 5899454
  have htrace : WordTrace (prefixWord ++ tailWord_5899454) baseStart_5899454 baseEnd_5899454 := by
    simpa [prefixWord, tailWord_5899454, baseEnd_5899454] using wordTrace_append hprefix tailTrace_5899454
  have hstable : (prefixWord ++ tailWord_5899454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899454).length < 2 ^ (prefixWord ++ tailWord_5899454).sum := by decide
  have hdescent : baseEnd_5899454 < baseStart_5899454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899501 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5899501 : Nat := 118140960795 + 5899501 * 2 ^ 59
def prefixEnd_5899501 : Nat := 4983230072969 + 3 ^ 40 * 5899501 * 2
def baseEnd_5899501 : Nat := 3029279634680427908906195

theorem tailTrace_5899501 : CollatzResearch.WordTrace tailWord_5899501 prefixEnd_5899501 3029279634680427908906195 := by
  unfold tailWord_5899501
  simp only [CollatzResearch.WordTrace]
  refine ⟨215172478600122906400394357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143448319066748604266929571 215172478600122906400394357)
  ·
    refine ⟨20172419868761522475036971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215172478600122906400394357 20172419868761522475036971)
    ·
      refine ⟨30258629803142283712555457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172419868761522475036971 30258629803142283712555457)
      ·
        refine ⟨22693972352356712784416593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30258629803142283712555457 22693972352356712784416593)
        ·
          refine ⟨17020479264267534588312445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22693972352356712784416593 17020479264267534588312445)
          ·
            refine ⟨6382679724100325470617167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17020479264267534588312445 6382679724100325470617167)
            ·
              refine ⟨9574019586150488205925751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382679724100325470617167 9574019586150488205925751)
              ·
                refine ⟨14361029379225732308888627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9574019586150488205925751 14361029379225732308888627)
                ·
                  refine ⟨21541544068838598463332941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14361029379225732308888627 21541544068838598463332941)
                  ·
                    refine ⟨8078079025814474423749853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21541544068838598463332941 8078079025814474423749853)
                    ·
                      refine ⟨3029279634680427908906195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078079025814474423749853 3029279634680427908906195)
                      ·
                        rfl

theorem cell23_5899501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5899501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899501 prefixEnd_5899501 := by exact prefixLift 5899501
  have htrace : WordTrace (prefixWord ++ tailWord_5899501) baseStart_5899501 baseEnd_5899501 := by
    simpa [prefixWord, tailWord_5899501, baseEnd_5899501] using wordTrace_append hprefix tailTrace_5899501
  have hstable : (prefixWord ++ tailWord_5899501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899501).length < 2 ^ (prefixWord ++ tailWord_5899501).sum := by decide
  have hdescent : baseEnd_5899501 < baseStart_5899501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899541 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_5899541 : Nat := 118140960795 + 5899541 * 2 ^ 59
def prefixEnd_5899541 : Nat := 4983230072969 + 3 ^ 40 * 5899541 * 2
def baseEnd_5899541 : Nat := 3029300173906607752406011

theorem tailTrace_5899541 : CollatzResearch.WordTrace tailWord_5899541 prefixEnd_5899541 3029300173906607752406011 := by
  unfold tailWord_5899541
  simp only [CollatzResearch.WordTrace]
  refine ⟨215173937519977993231850477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143449291679985328821233651 215173937519977993231850477)
  ·
    refine ⟨80690226569991747461943929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215173937519977993231850477 80690226569991747461943929)
    ·
      refine ⟨60517669927493810596457947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80690226569991747461943929 60517669927493810596457947)
      ·
        refine ⟨90776504891240715894686921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60517669927493810596457947 90776504891240715894686921)
        ·
          refine ⟨68082378668430536921015191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90776504891240715894686921 68082378668430536921015191)
          ·
            refine ⟨102123568002645805381522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68082378668430536921015191 102123568002645805381522787)
            ·
              refine ⟨153185352003968708072284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102123568002645805381522787 153185352003968708072284181)
              ·
                refine ⟨7180563375186033190888321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153185352003968708072284181 7180563375186033190888321)
                ·
                  refine ⟨5385422531389524893166241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180563375186033190888321 5385422531389524893166241)
                  ·
                    refine ⟨4039066898542143669874681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385422531389524893166241 4039066898542143669874681)
                    ·
                      refine ⟨3029300173906607752406011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039066898542143669874681 3029300173906607752406011)
                      ·
                        rfl

theorem cell23_5899541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_5899541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899541 prefixEnd_5899541 := by exact prefixLift 5899541
  have htrace : WordTrace (prefixWord ++ tailWord_5899541) baseStart_5899541 baseEnd_5899541 := by
    simpa [prefixWord, tailWord_5899541, baseEnd_5899541] using wordTrace_append hprefix tailTrace_5899541
  have hstable : (prefixWord ++ tailWord_5899541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899541).length < 2 ^ (prefixWord ++ tailWord_5899541).sum := by decide
  have hdescent : baseEnd_5899541 < baseStart_5899541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899634 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_5899634 : Nat := 118140960795 + 5899634 * 2 ^ 59
def prefixEnd_5899634 : Nat := 4983230072969 + 3 ^ 40 * 5899634 * 2
def baseEnd_5899634 : Nat := 3029347927607475888543083

theorem tailTrace_5899634 : CollatzResearch.WordTrace tailWord_5899634 prefixEnd_5899634 3029347927607475888543083 := by
  unfold tailWord_5899634
  simp only [CollatzResearch.WordTrace]
  refine ⟨53794332377160267528746489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143451553005760713409990637 53794332377160267528746489)
  ·
    refine ⟨40345749282870200646559867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53794332377160267528746489 40345749282870200646559867)
    ·
      refine ⟨60518623924305300969839801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40345749282870200646559867 60518623924305300969839801)
      ·
        refine ⟨45388967943228975727379851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60518623924305300969839801 45388967943228975727379851)
        ·
          refine ⟨68083451914843463591069777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45388967943228975727379851 68083451914843463591069777)
          ·
            refine ⟨51062588936132597693302333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68083451914843463591069777 51062588936132597693302333)
            ·
              refine ⟨19148470851049724134988375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51062588936132597693302333 19148470851049724134988375)
              ·
                refine ⟨28722706276574586202482563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19148470851049724134988375 28722706276574586202482563)
                ·
                  refine ⟨43084059414861879303723845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28722706276574586202482563 43084059414861879303723845)
                  ·
                    refine ⟨8078261140286602369448221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43084059414861879303723845 8078261140286602369448221)
                    ·
                      refine ⟨3029347927607475888543083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078261140286602369448221 3029347927607475888543083)
                      ·
                        rfl

theorem cell23_5899634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_5899634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899634 prefixEnd_5899634 := by exact prefixLift 5899634
  have htrace : WordTrace (prefixWord ++ tailWord_5899634) baseStart_5899634 baseEnd_5899634 := by
    simpa [prefixWord, tailWord_5899634, baseEnd_5899634] using wordTrace_append hprefix tailTrace_5899634
  have hstable : (prefixWord ++ tailWord_5899634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899634).length < 2 ^ (prefixWord ++ tailWord_5899634).sum := by decide
  have hdescent : baseEnd_5899634 < baseStart_5899634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899641 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 1, 4]
def baseStart_5899641 : Nat := 118140960795 + 5899641 * 2 ^ 59
def prefixEnd_5899641 : Nat := 4983230072969 + 3 ^ 40 * 5899641 * 2
def baseEnd_5899641 : Nat := 1009783840657352453718517

theorem tailTrace_5899641 : CollatzResearch.WordTrace tailWord_5899641 prefixEnd_5899641 1009783840657352453718517 := by
  unfold tailWord_5899641
  simp only [CollatzResearch.WordTrace]
  refine ⟨215177584819615710310490777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143451723213077140206993851 215177584819615710310490777)
  ·
    refine ⟨161383188614711782732868083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215177584819615710310490777 161383188614711782732868083)
    ·
      refine ⟨242074782922067674099302125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161383188614711782732868083 242074782922067674099302125)
      ·
        refine ⟨90778043595775377787238297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242074782922067674099302125 90778043595775377787238297)
        ·
          refine ⟨68083532696831533340428723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90778043595775377787238297 68083532696831533340428723)
          ·
            refine ⟨102125299045247300010643085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68083532696831533340428723 102125299045247300010643085)
            ·
              refine ⟨38296987141967737503991157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102125299045247300010643085 38296987141967737503991157)
              ·
                refine ⟨3590342544559475390999171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38296987141967737503991157 3590342544559475390999171)
                ·
                  refine ⟨5385513816839213086498757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590342544559475390999171 5385513816839213086498757)
                  ·
                    refine ⟨1009783840657352453718517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385513816839213086498757 1009783840657352453718517)
                    ·
                      rfl

theorem cell23_5899641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_5899641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899641 prefixEnd_5899641 := by exact prefixLift 5899641
  have htrace : WordTrace (prefixWord ++ tailWord_5899641) baseStart_5899641 baseEnd_5899641 := by
    simpa [prefixWord, tailWord_5899641, baseEnd_5899641] using wordTrace_append hprefix tailTrace_5899641
  have hstable : (prefixWord ++ tailWord_5899641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899641).length < 2 ^ (prefixWord ++ tailWord_5899641).sum := by decide
  have hdescent : baseEnd_5899641 < baseStart_5899641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_5899698 : Nat := 118140960795 + 5899698 * 2 ^ 59
def prefixEnd_5899698 : Nat := 4983230072969 + 3 ^ 40 * 5899698 * 2
def baseEnd_5899698 : Nat := 3029380790369363638142789

theorem tailTrace_5899698 : CollatzResearch.WordTrace tailWord_5899698 prefixEnd_5899698 3029380790369363638142789 := by
  unfold tailWord_5899698
  simp only [CollatzResearch.WordTrace]
  refine ⟨53794915945102302261328937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143453109186939472696877165 53794915945102302261328937)
  ·
    refine ⟨40346186958826726695996703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53794915945102302261328937 40346186958826726695996703)
    ·
      refine ⟨60519280438240090043995055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40346186958826726695996703 60519280438240090043995055)
      ·
        refine ⟨90778920657360135065992583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60519280438240090043995055 90778920657360135065992583)
        ·
          refine ⟨136168380986040202598988875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90778920657360135065992583 136168380986040202598988875)
          ·
            refine ⟨204252571479060303898483313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136168380986040202598988875 204252571479060303898483313)
            ·
              refine ⟨153189428609295227923862485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204252571479060303898483313 153189428609295227923862485)
              ·
                refine ⟨3590377233030356904465527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153189428609295227923862485 3590377233030356904465527)
                ·
                  refine ⟨5385565849545535356698291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590377233030356904465527 5385565849545535356698291)
                  ·
                    refine ⟨8078348774318303035047437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385565849545535356698291 8078348774318303035047437)
                    ·
                      refine ⟨3029380790369363638142789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078348774318303035047437 3029380790369363638142789)
                      ·
                        rfl

theorem cell23_5899698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_5899698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899698 prefixEnd_5899698 := by exact prefixLift 5899698
  have htrace : WordTrace (prefixWord ++ tailWord_5899698) baseStart_5899698 baseEnd_5899698 := by
    simpa [prefixWord, tailWord_5899698, baseEnd_5899698] using wordTrace_append hprefix tailTrace_5899698
  have hstable : (prefixWord ++ tailWord_5899698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899698).length < 2 ^ (prefixWord ++ tailWord_5899698).sum := by decide
  have hdescent : baseEnd_5899698 < baseStart_5899698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899701 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5899701 : Nat := 118140960795 + 5899701 * 2 ^ 59
def prefixEnd_5899701 : Nat := 4983230072969 + 3 ^ 40 * 5899701 * 2
def baseEnd_5899701 : Nat := 1009794110270442375468425

theorem tailTrace_5899701 : CollatzResearch.WordTrace tailWord_5899701 prefixEnd_5899701 1009794110270442375468425 := by
  unfold tailWord_5899701
  simp only [CollatzResearch.WordTrace]
  refine ⟨215179773199398340557674957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143453182132932227038449971 215179773199398340557674957)
  ·
    refine ⟨80692414949774377709128109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215179773199398340557674957 80692414949774377709128109)
    ·
      refine ⟨30259655606165391640923041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80692414949774377709128109 30259655606165391640923041)
      ·
        refine ⟨22694741704624043730692281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30259655606165391640923041 22694741704624043730692281)
        ·
          refine ⟨17021056278468032798019211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22694741704624043730692281 17021056278468032798019211)
          ·
            refine ⟨25531584417702049197028817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17021056278468032798019211 25531584417702049197028817)
            ·
              refine ⟨19148688313276536897771613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25531584417702049197028817 19148688313276536897771613)
              ·
                refine ⟨7180758117478701336664355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19148688313276536897771613 7180758117478701336664355)
                ·
                  refine ⟨10771137176218052004996533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180758117478701336664355 10771137176218052004996533)
                  ·
                    refine ⟨1009794110270442375468425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10771137176218052004996533 1009794110270442375468425)
                    ·
                      rfl

theorem cell23_5899701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5899701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899701 prefixEnd_5899701 := by exact prefixLift 5899701
  have htrace : WordTrace (prefixWord ++ tailWord_5899701) baseStart_5899701 baseEnd_5899701 := by
    simpa [prefixWord, tailWord_5899701, baseEnd_5899701] using wordTrace_append hprefix tailTrace_5899701
  have hstable : (prefixWord ++ tailWord_5899701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899701).length < 2 ^ (prefixWord ++ tailWord_5899701).sum := by decide
  have hdescent : baseEnd_5899701 < baseStart_5899701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899727 : List Nat := [1, 1, 2, 1, 1, 4, 3, 10]
def baseStart_5899727 : Nat := 118140960795 + 5899727 * 2 ^ 59
def prefixEnd_5899727 : Nat := 4983230072969 + 3 ^ 40 * 5899727 * 2
def baseEnd_5899727 : Nat := 112199840048457186099265

theorem tailTrace_5899727 : CollatzResearch.WordTrace tailWord_5899727 prefixEnd_5899727 112199840048457186099265 := by
  unfold tailWord_5899727
  simp only [CollatzResearch.WordTrace]
  refine ⟨215180721497304146998121435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143453814331536097998747623 215180721497304146998121435)
  ·
    refine ⟨322771082245956220497182153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215180721497304146998121435 322771082245956220497182153)
    ·
      refine ⟨242078311684467165372886615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322771082245956220497182153 242078311684467165372886615)
      ·
        refine ⟨363117467526700748059329923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242078311684467165372886615 363117467526700748059329923)
        ·
          refine ⟨544676201290051122088994885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363117467526700748059329923 544676201290051122088994885)
          ·
            refine ⟨102126787741884585391686541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544676201290051122088994885 102126787741884585391686541)
            ·
              refine ⟨38297545403206719521882453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102126787741884585391686541 38297545403206719521882453)
              ·
                refine ⟨112199840048457186099265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38297545403206719521882453 112199840048457186099265)
                ·
                  rfl

theorem cell23_5899727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 10].length) (baseStart_5899727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899727 prefixEnd_5899727 := by exact prefixLift 5899727
  have htrace : WordTrace (prefixWord ++ tailWord_5899727) baseStart_5899727 baseEnd_5899727 := by
    simpa [prefixWord, tailWord_5899727, baseEnd_5899727] using wordTrace_append hprefix tailTrace_5899727
  have hstable : (prefixWord ++ tailWord_5899727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899727).length < 2 ^ (prefixWord ++ tailWord_5899727).sum := by decide
  have hdescent : baseEnd_5899727 < baseStart_5899727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899738 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_5899738 : Nat := 118140960795 + 5899738 * 2 ^ 59
def prefixEnd_5899738 : Nat := 4983230072969 + 3 ^ 40 * 5899738 * 2
def baseEnd_5899738 : Nat := 3029401329595543481642605

theorem tailTrace_5899738 : CollatzResearch.WordTrace tailWord_5899738 prefixEnd_5899738 3029401329595543481642605 := by
  unfold tailWord_5899738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53795280675066073969192967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143454081800176197251181245 53795280675066073969192967)
  ·
    refine ⟨80692921012599110953789451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53795280675066073969192967 80692921012599110953789451)
    ·
      refine ⟨121039381518898666430684177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80692921012599110953789451 121039381518898666430684177)
      ·
        refine ⟨90779536139173999823013133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121039381518898666430684177 90779536139173999823013133)
        ·
          refine ⟨34042326052190249933629925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90779536139173999823013133 34042326052190249933629925)
          ·
            refine ⟨6382936134785671862555611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34042326052190249933629925 6382936134785671862555611)
            ·
              refine ⟨9574404202178507793833417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382936134785671862555611 9574404202178507793833417)
              ·
                refine ⟨7180803151633880845375063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9574404202178507793833417 7180803151633880845375063)
                ·
                  refine ⟨10771204727450821268062595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180803151633880845375063 10771204727450821268062595)
                  ·
                    refine ⟨16156807091176231902093893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10771204727450821268062595 16156807091176231902093893)
                    ·
                      refine ⟨3029401329595543481642605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16156807091176231902093893 3029401329595543481642605)
                      ·
                        rfl

theorem cell23_5899738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_5899738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899738 prefixEnd_5899738 := by exact prefixLift 5899738
  have htrace : WordTrace (prefixWord ++ tailWord_5899738) baseStart_5899738 baseEnd_5899738 := by
    simpa [prefixWord, tailWord_5899738, baseEnd_5899738] using wordTrace_append hprefix tailTrace_5899738
  have hstable : (prefixWord ++ tailWord_5899738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899738).length < 2 ^ (prefixWord ++ tailWord_5899738).sum := by decide
  have hdescent : baseEnd_5899738 < baseStart_5899738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899751 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5899751 : Nat := 118140960795 + 5899751 * 2 ^ 59
def prefixEnd_5899751 : Nat := 4983230072969 + 3 ^ 40 * 5899751 * 2
def baseEnd_5899751 : Nat := 3029408004844051930780045

theorem tailTrace_5899751 : CollatzResearch.WordTrace tailWord_5899751 prefixEnd_5899751 3029408004844051930780045 := by
  unfold tailWord_5899751
  simp only [CollatzResearch.WordTrace]
  refine ⟨215181596849217199096995107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143454397899478132731330071 215181596849217199096995107)
  ·
    refine ⟨322772395273825798645492661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215181596849217199096995107 322772395273825798645492661)
    ·
      refine ⟨30259912056921168623014937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 322772395273825798645492661 30259912056921168623014937)
      ·
        refine ⟨22694934042690876467261203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30259912056921168623014937 22694934042690876467261203)
        ·
          refine ⟨34042401064036314700891805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22694934042690876467261203 34042401064036314700891805)
          ·
            refine ⟨12765900399013618012834427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34042401064036314700891805 12765900399013618012834427)
            ·
              refine ⟨19148850598520427019251641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765900399013618012834427 19148850598520427019251641)
              ·
                refine ⟨14361637948890320264438731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19148850598520427019251641 14361637948890320264438731)
                ·
                  refine ⟨21542456923335480396658097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14361637948890320264438731 21542456923335480396658097)
                  ·
                    refine ⟨16156842692501610297493573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21542456923335480396658097 16156842692501610297493573)
                    ·
                      refine ⟨3029408004844051930780045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16156842692501610297493573 3029408004844051930780045)
                      ·
                        rfl

theorem cell23_5899751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5899751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899751 prefixEnd_5899751 := by exact prefixLift 5899751
  have htrace : WordTrace (prefixWord ++ tailWord_5899751) baseStart_5899751 baseEnd_5899751 := by
    simpa [prefixWord, tailWord_5899751, baseEnd_5899751] using wordTrace_append hprefix tailTrace_5899751
  have hstable : (prefixWord ++ tailWord_5899751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899751).length < 2 ^ (prefixWord ++ tailWord_5899751).sum := by decide
  have hdescent : baseEnd_5899751 < baseStart_5899751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899765 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5899765 : Nat := 118140960795 + 5899765 * 2 ^ 59
def prefixEnd_5899765 : Nat := 4983230072969 + 3 ^ 40 * 5899765 * 2
def baseEnd_5899765 : Nat := 1009805064524404958668327

theorem tailTrace_5899765 : CollatzResearch.WordTrace tailWord_5899765 prefixEnd_5899765 1009805064524404958668327 := by
  unfold tailWord_5899765
  simp only [CollatzResearch.WordTrace]
  refine ⟨215182107471166479488004749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143454738314110986325336499 215182107471166479488004749)
  ·
    refine ⟨80693290301687429808001781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215182107471166479488004749 80693290301687429808001781)
    ·
      refine ⟨7564995965783196544500167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80693290301687429808001781 7564995965783196544500167)
      ·
        refine ⟨11347493948674794816750251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564995965783196544500167 11347493948674794816750251)
        ·
          refine ⟨17021240923012192225125377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347493948674794816750251 17021240923012192225125377)
          ·
            refine ⟨12765930692259144168844033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17021240923012192225125377 12765930692259144168844033)
            ·
              refine ⟨9574448019194358126633025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12765930692259144168844033 9574448019194358126633025)
              ·
                refine ⟨7180836014395768594974769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9574448019194358126633025 7180836014395768594974769)
                ·
                  refine ⟨5385627010796826446231077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180836014395768594974769 5385627010796826446231077)
                  ·
                    refine ⟨1009805064524404958668327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5385627010796826446231077 1009805064524404958668327)
                    ·
                      rfl

theorem cell23_5899765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5899765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899765 prefixEnd_5899765 := by exact prefixLift 5899765
  have htrace : WordTrace (prefixWord ++ tailWord_5899765) baseStart_5899765 baseEnd_5899765 := by
    simpa [prefixWord, tailWord_5899765, baseEnd_5899765] using wordTrace_append hprefix tailTrace_5899765
  have hstable : (prefixWord ++ tailWord_5899765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899765).length < 2 ^ (prefixWord ++ tailWord_5899765).sum := by decide
  have hdescent : baseEnd_5899765 < baseStart_5899765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899772 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_5899772 : Nat := 118140960795 + 5899772 * 2 ^ 59
def prefixEnd_5899772 : Nat := 4983230072969 + 3 ^ 40 * 5899772 * 2
def baseEnd_5899772 : Nat := 3029418787937796348617449

theorem tailTrace_5899772 : CollatzResearch.WordTrace tailWord_5899772 prefixEnd_5899772 3029418787937796348617449 := by
  unfold tailWord_5899772
  simp only [CollatzResearch.WordTrace]
  refine ⟨107591181391070559841754785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143454908521427413122339713 107591181391070559841754785)
  ·
    refine ⟨80693386043302919881316089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107591181391070559841754785 80693386043302919881316089)
    ·
      refine ⟨60520039532477189910987067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80693386043302919881316089 60520039532477189910987067)
      ·
        refine ⟨90780059298715784866480601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60520039532477189910987067 90780059298715784866480601)
        ·
          refine ⟨68085044474036838649860451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90780059298715784866480601 68085044474036838649860451)
          ·
            refine ⟨102127566711055257974790677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68085044474036838649860451 102127566711055257974790677)
            ·
              refine ⟨4787229689580715217568313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102127566711055257974790677 4787229689580715217568313)
              ·
                refine ⟨3590422267185536413176235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4787229689580715217568313 3590422267185536413176235)
                ·
                  refine ⟨5385633400778304619764353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590422267185536413176235 5385633400778304619764353)
                  ·
                    refine ⟨4039225050583728464823265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385633400778304619764353 4039225050583728464823265)
                    ·
                      refine ⟨3029418787937796348617449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039225050583728464823265 3029418787937796348617449)
                      ·
                        rfl

theorem cell23_5899772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_5899772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899772 prefixEnd_5899772 := by exact prefixLift 5899772
  have htrace : WordTrace (prefixWord ++ tailWord_5899772) baseStart_5899772 baseEnd_5899772 := by
    simpa [prefixWord, tailWord_5899772, baseEnd_5899772] using wordTrace_append hprefix tailTrace_5899772
  have hstable : (prefixWord ++ tailWord_5899772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899772).length < 2 ^ (prefixWord ++ tailWord_5899772).sum := by decide
  have hdescent : baseEnd_5899772 < baseStart_5899772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899778 : List Nat := [3, 4, 1, 2, 1, 3, 1, 8]
def baseStart_5899778 : Nat := 118140960795 + 5899778 * 2 ^ 59
def prefixEnd_5899778 : Nat := 4983230072969 + 3 ^ 40 * 5899778 * 2
def baseEnd_5899778 : Nat := 112200809956360123153423

theorem tailTrace_5899778 : CollatzResearch.WordTrace tailWord_5899778 prefixEnd_5899778 112200809956360123153423 := by
  unfold tailWord_5899778
  simp only [CollatzResearch.WordTrace]
  refine ⟨53795645405029845677056997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143455054413412921805485325 53795645405029845677056997)
  ·
    refine ⟨10086683513443096064448187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53795645405029845677056997 10086683513443096064448187)
    ·
      refine ⟨15130025270164644096672281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10086683513443096064448187 15130025270164644096672281)
      ·
        refine ⟨11347518952623483072504211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15130025270164644096672281 11347518952623483072504211)
        ·
          refine ⟨17021278428935224608756317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347518952623483072504211 17021278428935224608756317)
          ·
            refine ⟨6382979410850709228283619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17021278428935224608756317 6382979410850709228283619)
            ·
              refine ⟨9574469116276063842425429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382979410850709228283619 9574469116276063842425429)
              ·
                refine ⟨112200809956360123153423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9574469116276063842425429 112200809956360123153423)
                ·
                  rfl

theorem cell23_5899778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_5899778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899778 prefixEnd_5899778 := by exact prefixLift 5899778
  have htrace : WordTrace (prefixWord ++ tailWord_5899778) baseStart_5899778 baseEnd_5899778 := by
    simpa [prefixWord, tailWord_5899778, baseEnd_5899778] using wordTrace_append hprefix tailTrace_5899778
  have hstable : (prefixWord ++ tailWord_5899778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899778).length < 2 ^ (prefixWord ++ tailWord_5899778).sum := by decide
  have hdescent : baseEnd_5899778 < baseStart_5899778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899782 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5899782 : Nat := 118140960795 + 5899782 * 2 ^ 59
def prefixEnd_5899782 : Nat := 4983230072969 + 3 ^ 40 * 5899782 * 2
def baseEnd_5899782 : Nat := 1009807974248113769830801

theorem tailTrace_5899782 : CollatzResearch.WordTrace tailWord_5899782 prefixEnd_5899782 1009807974248113769830801 := by
  unfold tailWord_5899782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724460234753277855980425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143455151674736594260915733 6724460234753277855980425)
  ·
    refine ⟨5043345176064958391985319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6724460234753277855980425 5043345176064958391985319)
    ·
      refine ⟨7565017764097437587977979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043345176064958391985319 7565017764097437587977979)
      ·
        refine ⟨11347526646146156381966969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565017764097437587977979 11347526646146156381966969)
        ·
          refine ⟨8510644984609617286475227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11347526646146156381966969 8510644984609617286475227)
          ·
            refine ⟨12765967476914425929712841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510644984609617286475227 12765967476914425929712841)
            ·
              refine ⟨9574475607685819447284631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12765967476914425929712841 9574475607685819447284631)
              ·
                refine ⟨14361713411528729170926947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9574475607685819447284631 14361713411528729170926947)
                ·
                  refine ⟨21542570117293093756390421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14361713411528729170926947 21542570117293093756390421)
                  ·
                    refine ⟨1009807974248113769830801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21542570117293093756390421 1009807974248113769830801)
                    ·
                      rfl

theorem cell23_5899782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5899782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899782 prefixEnd_5899782 := by exact prefixLift 5899782
  have htrace : WordTrace (prefixWord ++ tailWord_5899782) baseStart_5899782 baseEnd_5899782 := by
    simpa [prefixWord, tailWord_5899782, baseEnd_5899782] using wordTrace_append hprefix tailTrace_5899782
  have hstable : (prefixWord ++ tailWord_5899782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899782).length < 2 ^ (prefixWord ++ tailWord_5899782).sum := by decide
  have hdescent : baseEnd_5899782 < baseStart_5899782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899788 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_5899788 : Nat := 118140960795 + 5899788 * 2 ^ 59
def prefixEnd_5899788 : Nat := 4983230072969 + 3 ^ 40 * 5899788 * 2
def baseEnd_5899788 : Nat := 3029427003628268286017375

theorem tailTrace_5899788 : CollatzResearch.WordTrace tailWord_5899788 prefixEnd_5899788 3029427003628268286017375 := by
  unfold tailWord_5899788
  simp only [CollatzResearch.WordTrace]
  refine ⟨107591473175041577208046009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143455297566722102944061345 107591473175041577208046009)
  ·
    refine ⟨80693604881281182906034507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107591473175041577208046009 80693604881281182906034507)
    ·
      refine ⟨121040407321921774359051761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80693604881281182906034507 121040407321921774359051761)
      ·
        refine ⟨90780305491441330769288821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121040407321921774359051761 90780305491441330769288821)
        ·
          refine ⟨8510653639822624759620827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90780305491441330769288821 8510653639822624759620827)
          ·
            refine ⟨12765980459733937139431241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510653639822624759620827 12765980459733937139431241)
            ·
              refine ⟨9574485344800452854573431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12765980459733937139431241 9574485344800452854573431)
              ·
                refine ⟨14361728017200679281860147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9574485344800452854573431 14361728017200679281860147)
                ·
                  refine ⟨21542592025801018922790221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14361728017200679281860147 21542592025801018922790221)
                  ·
                    refine ⟨8078472009675382096046333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21542592025801018922790221 8078472009675382096046333)
                    ·
                      refine ⟨3029427003628268286017375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078472009675382096046333 3029427003628268286017375)
                      ·
                        rfl

theorem cell23_5899788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_5899788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899788 prefixEnd_5899788 := by exact prefixLift 5899788
  have htrace : WordTrace (prefixWord ++ tailWord_5899788) baseStart_5899788 baseEnd_5899788 := by
    simpa [prefixWord, tailWord_5899788, baseEnd_5899788] using wordTrace_append hprefix tailTrace_5899788
  have hstable : (prefixWord ++ tailWord_5899788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899788).length < 2 ^ (prefixWord ++ tailWord_5899788).sum := by decide
  have hdescent : baseEnd_5899788 < baseStart_5899788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899789 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5899789 : Nat := 118140960795 + 5899789 * 2 ^ 59
def prefixEnd_5899789 : Nat := 4983230072969 + 3 ^ 40 * 5899789 * 2
def baseEnd_5899789 : Nat := 3029427517108922782104871

theorem tailTrace_5899789 : CollatzResearch.WordTrace tailWord_5899789 prefixEnd_5899789 3029427517108922782104871 := by
  unfold tailWord_5899789
  simp only [CollatzResearch.WordTrace]
  refine ⟨215182982823079531586878421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143455321882053021057918947 215182982823079531586878421)
  ·
    refine ⟨5043351159915926521567463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 215182982823079531586878421 5043351159915926521567463)
    ·
      refine ⟨7565026739873889782351195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043351159915926521567463 7565026739873889782351195)
      ·
        refine ⟨11347540109810834673526793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565026739873889782351195 11347540109810834673526793)
        ·
          refine ⟨8510655082358126005145095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11347540109810834673526793 8510655082358126005145095)
          ·
            refine ⟨12765982623537189007717643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510655082358126005145095 12765982623537189007717643)
            ·
              refine ⟨19148973935305783511576465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765982623537189007717643 19148973935305783511576465)
              ·
                refine ⟨14361730451479337633682349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19148973935305783511576465 14361730451479337633682349)
                ·
                  refine ⟨5385648919304751612630881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14361730451479337633682349 5385648919304751612630881)
                  ·
                    refine ⟨4039236689478563709473161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385648919304751612630881 4039236689478563709473161)
                    ·
                      refine ⟨3029427517108922782104871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039236689478563709473161 3029427517108922782104871)
                      ·
                        rfl

theorem cell23_5899789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5899789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899789 prefixEnd_5899789 := by exact prefixLift 5899789
  have htrace : WordTrace (prefixWord ++ tailWord_5899789) baseStart_5899789 baseEnd_5899789 := by
    simpa [prefixWord, tailWord_5899789, baseEnd_5899789] using wordTrace_append hprefix tailTrace_5899789
  have hstable : (prefixWord ++ tailWord_5899789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899789).length < 2 ^ (prefixWord ++ tailWord_5899789).sum := by decide
  have hdescent : baseEnd_5899789 < baseStart_5899789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899804 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_5899804 : Nat := 118140960795 + 5899804 * 2 ^ 59
def prefixEnd_5899804 : Nat := 4983230072969 + 3 ^ 40 * 5899804 * 2
def baseEnd_5899804 : Nat := 1009811739772913407805767

theorem tailTrace_5899804 : CollatzResearch.WordTrace tailWord_5899804 prefixEnd_5899804 1009811739772913407805767 := by
  unfold tailWord_5899804
  simp only [CollatzResearch.WordTrace]
  refine ⟨107591764959012594574337233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143455686612016792765782977 107591764959012594574337233)
  ·
    refine ⟨80693823719259445930752925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107591764959012594574337233 80693823719259445930752925)
    ·
      refine ⟨30260183894722292224032347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80693823719259445930752925 30260183894722292224032347)
      ·
        refine ⟨45390275842083438336048521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30260183894722292224032347 45390275842083438336048521)
        ·
          refine ⟨34042706881562578752036391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45390275842083438336048521 34042706881562578752036391)
          ·
            refine ⟨51064060322343868128054587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34042706881562578752036391 51064060322343868128054587)
            ·
              refine ⟨76596090483515802192081881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51064060322343868128054587 76596090483515802192081881)
              ·
                refine ⟨57447067862636851644061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76596090483515802192081881 57447067862636851644061411)
                ·
                  refine ⟨86170601793955277466092117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57447067862636851644061411 86170601793955277466092117)
                  ·
                    refine ⟨1009811739772913407805767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86170601793955277466092117 1009811739772913407805767)
                    ·
                      rfl

theorem cell23_5899804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_5899804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899804 prefixEnd_5899804 := by exact prefixLift 5899804
  have htrace : WordTrace (prefixWord ++ tailWord_5899804) baseStart_5899804 baseEnd_5899804 := by
    simpa [prefixWord, tailWord_5899804, baseEnd_5899804] using wordTrace_append hprefix tailTrace_5899804
  have hstable : (prefixWord ++ tailWord_5899804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899804).length < 2 ^ (prefixWord ++ tailWord_5899804).sum := by decide
  have hdescent : baseEnd_5899804 < baseStart_5899804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899806 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5899806 : Nat := 118140960795 + 5899806 * 2 ^ 59
def prefixEnd_5899806 : Nat := 4983230072969 + 3 ^ 40 * 5899806 * 2
def baseEnd_5899806 : Nat := 3029436246280049215592293

theorem tailTrace_5899806 : CollatzResearch.WordTrace tailWord_5899806 prefixEnd_5899806 3029436246280049215592293 := by
  unfold tailWord_5899806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26897950358002242936280909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143455735242678628993498181 26897950358002242936280909)
  ·
    refine ⟨10086731384250841101105341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26897950358002242936280909 10086731384250841101105341)
    ·
      refine ⟨3782524269094065412914503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10086731384250841101105341 3782524269094065412914503)
      ·
        refine ⟨5673786403641098119371755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782524269094065412914503 5673786403641098119371755)
        ·
          refine ⟨8510679605461647179057633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673786403641098119371755 8510679605461647179057633)
          ·
            refine ⟨6383009704096235384293225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8510679605461647179057633 6383009704096235384293225)
            ·
              refine ⟨4787257278072176538219919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6383009704096235384293225 4787257278072176538219919)
              ·
                refine ⟨7180885917108264807329879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787257278072176538219919 7180885917108264807329879)
                ·
                  refine ⟨10771328875662397210994819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180885917108264807329879 10771328875662397210994819)
                  ·
                    refine ⟨16156993313493595816492229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10771328875662397210994819 16156993313493595816492229)
                    ·
                      refine ⟨3029436246280049215592293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16156993313493595816492229 3029436246280049215592293)
                      ·
                        rfl

theorem cell23_5899806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5899806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899806 prefixEnd_5899806 := by exact prefixLift 5899806
  have htrace : WordTrace (prefixWord ++ tailWord_5899806) baseStart_5899806 baseEnd_5899806 := by
    simpa [prefixWord, tailWord_5899806, baseEnd_5899806] using wordTrace_append hprefix tailTrace_5899806
  have hstable : (prefixWord ++ tailWord_5899806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899806).length < 2 ^ (prefixWord ++ tailWord_5899806).sum := by decide
  have hdescent : baseEnd_5899806 < baseStart_5899806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899822 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5899822 : Nat := 118140960795 + 5899822 * 2 ^ 59
def prefixEnd_5899822 : Nat := 4983230072969 + 3 ^ 40 * 5899822 * 2
def baseEnd_5899822 : Nat := 3029444461970521152992219

theorem tailTrace_5899822 : CollatzResearch.WordTrace tailWord_5899822 prefixEnd_5899822 3029444461970521152992219 := by
  unfold tailWord_5899822
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898023303994997277853715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143456124287973318815219813 26898023303994997277853715)
  ·
    refine ⟨40347034955992495916780573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26898023303994997277853715 40347034955992495916780573)
    ·
      refine ⟨15130138108497185968792715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40347034955992495916780573 15130138108497185968792715)
      ·
        refine ⟨22695207162745778953189073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130138108497185968792715 22695207162745778953189073)
        ·
          refine ⟨17021405372059334214891805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22695207162745778953189073 17021405372059334214891805)
          ·
            refine ⟨6383027014522250330584427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17021405372059334214891805 6383027014522250330584427)
            ·
              refine ⟨9574540521783375495876641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383027014522250330584427 9574540521783375495876641)
              ·
                refine ⟨7180905391337531621907481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9574540521783375495876641 7180905391337531621907481)
                ·
                  refine ⟨5385679043503148716430611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7180905391337531621907481 5385679043503148716430611)
                  ·
                    refine ⟨8078518565254723074645917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385679043503148716430611 8078518565254723074645917)
                    ·
                      refine ⟨3029444461970521152992219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078518565254723074645917 3029444461970521152992219)
                      ·
                        rfl

theorem cell23_5899822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5899822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899822 prefixEnd_5899822 := by exact prefixLift 5899822
  have htrace : WordTrace (prefixWord ++ tailWord_5899822) baseStart_5899822 baseEnd_5899822 := by
    simpa [prefixWord, tailWord_5899822, baseEnd_5899822] using wordTrace_append hprefix tailTrace_5899822
  have hstable : (prefixWord ++ tailWord_5899822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899822).length < 2 ^ (prefixWord ++ tailWord_5899822).sum := by decide
  have hdescent : baseEnd_5899822 < baseStart_5899822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899841 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5899841 : Nat := 118140960795 + 5899841 * 2 ^ 59
def prefixEnd_5899841 : Nat := 4983230072969 + 3 ^ 40 * 5899841 * 2
def baseEnd_5899841 : Nat := 3029454218102956578654631

theorem tailTrace_5899841 : CollatzResearch.WordTrace tailWord_5899841 prefixEnd_5899841 3029454218102956578654631 := by
  unfold tailWord_5899841
  simp only [CollatzResearch.WordTrace]
  refine ⟨215184879418891144467771377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143456586279260762978514251 215184879418891144467771377)
  ·
    refine ⟨161388659564168358350828533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215184879418891144467771377 161388659564168358350828533)
    ·
      refine ⟨15130186834140783595390175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161388659564168358350828533 15130186834140783595390175)
      ·
        refine ⟨22695280251211175393085263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130186834140783595390175 22695280251211175393085263)
        ·
          refine ⟨34042920376816763089627895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22695280251211175393085263 34042920376816763089627895)
          ·
            refine ⟨51064380565225144634441843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34042920376816763089627895 51064380565225144634441843)
            ·
              refine ⟨76596570847837716951662765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51064380565225144634441843 76596570847837716951662765)
              ·
                refine ⟨28723714067939143856873537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76596570847837716951662765 28723714067939143856873537)
                ·
                  refine ⟨21542785550954357892655153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28723714067939143856873537 21542785550954357892655153)
                  ·
                    refine ⟨16157089163215768419491365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21542785550954357892655153 16157089163215768419491365)
                    ·
                      refine ⟨3029454218102956578654631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16157089163215768419491365 3029454218102956578654631)
                      ·
                        rfl

theorem cell23_5899841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5899841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899841 prefixEnd_5899841 := by exact prefixLift 5899841
  have htrace : WordTrace (prefixWord ++ tailWord_5899841) baseStart_5899841 baseEnd_5899841 := by
    simpa [prefixWord, tailWord_5899841, baseEnd_5899841] using wordTrace_append hprefix tailTrace_5899841
  have hstable : (prefixWord ++ tailWord_5899841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899841).length < 2 ^ (prefixWord ++ tailWord_5899841).sum := by decide
  have hdescent : baseEnd_5899841 < baseStart_5899841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899871 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 7, 2]
def baseStart_5899871 : Nat := 118140960795 + 5899871 * 2 ^ 59
def prefixEnd_5899871 : Nat := 4983230072969 + 3 ^ 40 * 5899871 * 2
def baseEnd_5899871 : Nat := 3029469622522591461279493

theorem tailTrace_5899871 : CollatzResearch.WordTrace tailWord_5899871 prefixEnd_5899871 3029469622522591461279493 := by
  unfold tailWord_5899871
  simp only [CollatzResearch.WordTrace]
  refine ⟨215185973608782459591363467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143457315739188306394242311 215185973608782459591363467)
  ·
    refine ⟨322778960413173689387045201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215185973608782459591363467 322778960413173689387045201)
    ·
      refine ⟨242084220309880267040283901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322778960413173689387045201 242084220309880267040283901)
      ·
        refine ⟨90781582616205100140106463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242084220309880267040283901 90781582616205100140106463)
        ·
          refine ⟨136172373924307650210159695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90781582616205100140106463 136172373924307650210159695)
          ·
            refine ⟨204258560886461475315239543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136172373924307650210159695 204258560886461475315239543)
            ·
              refine ⟨306387841329692212972859315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204258560886461475315239543 306387841329692212972859315)
              ·
                refine ⟨459581761994538319459288973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306387841329692212972859315 459581761994538319459288973)
                ·
                  refine ⟨172343160747951869797233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459581761994538319459288973 172343160747951869797233365)
                  ·
                    refine ⟨4039292830030121948372657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172343160747951869797233365 4039292830030121948372657)
                    ·
                      refine ⟨3029469622522591461279493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039292830030121948372657 3029469622522591461279493)
                      ·
                        rfl

theorem cell23_5899871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_5899871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899871 prefixEnd_5899871 := by exact prefixLift 5899871
  have htrace : WordTrace (prefixWord ++ tailWord_5899871) baseStart_5899871 baseEnd_5899871 := by
    simpa [prefixWord, tailWord_5899871, baseEnd_5899871] using wordTrace_append hprefix tailTrace_5899871
  have hstable : (prefixWord ++ tailWord_5899871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899871).length < 2 ^ (prefixWord ++ tailWord_5899871).sum := by decide
  have hdescent : baseEnd_5899871 < baseStart_5899871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899885 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 7]
def baseStart_5899885 : Nat := 118140960795 + 5899885 * 2 ^ 59
def prefixEnd_5899885 : Nat := 4983230072969 + 3 ^ 40 * 5899885 * 2
def baseEnd_5899885 : Nat := 336608534583528267389381

theorem tailTrace_5899885 : CollatzResearch.WordTrace tailWord_5899885 prefixEnd_5899885 336608534583528267389381 := by
  unfold tailWord_5899885
  simp only [CollatzResearch.WordTrace]
  refine ⟨215186484230731739982373109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143457656153821159988248739 215186484230731739982373109)
  ·
    refine ⟨20173732896631100623347479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215186484230731739982373109 20173732896631100623347479)
    ·
      refine ⟨30260599344946650935021219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20173732896631100623347479 30260599344946650935021219)
      ·
        refine ⟨45390899017419976402531829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30260599344946650935021219 45390899017419976402531829)
        ·
          refine ⟨4255396782883122787737359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45390899017419976402531829 4255396782883122787737359)
          ·
            refine ⟨6383095174324684181606039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255396782883122787737359 6383095174324684181606039)
            ·
              refine ⟨9574642761487026272409059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383095174324684181606039 9574642761487026272409059)
              ·
                refine ⟨14361964142230539408613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9574642761487026272409059 14361964142230539408613589)
                ·
                  refine ⟨336608534583528267389381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14361964142230539408613589 336608534583528267389381)
                  ·
                    rfl

theorem cell23_5899885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_5899885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899885 prefixEnd_5899885 := by exact prefixLift 5899885
  have htrace : WordTrace (prefixWord ++ tailWord_5899885) baseStart_5899885 baseEnd_5899885 := by
    simpa [prefixWord, tailWord_5899885, baseEnd_5899885] using wordTrace_append hprefix tailTrace_5899885
  have hstable : (prefixWord ++ tailWord_5899885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899885).length < 2 ^ (prefixWord ++ tailWord_5899885).sum := by decide
  have hdescent : baseEnd_5899885 < baseStart_5899885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899918 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5899918 : Nat := 118140960795 + 5899918 * 2 ^ 59
def prefixEnd_5899918 : Nat := 4983230072969 + 3 ^ 40 * 5899918 * 2
def baseEnd_5899918 : Nat := 3029493756113352777391777

theorem tailTrace_5899918 : CollatzResearch.WordTrace tailWord_5899918 prefixEnd_5899918 3029493756113352777391777 := by
  unfold tailWord_5899918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898460979951523327290551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143458458559741457745549605 26898460979951523327290551)
  ·
    refine ⟨40347691469927284990935827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26898460979951523327290551 40347691469927284990935827)
    ·
      refine ⟨60521537204890927486403741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40347691469927284990935827 60521537204890927486403741)
      ·
        refine ⟨22695576451834097807401403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60521537204890927486403741 22695576451834097807401403)
        ·
          refine ⟨34043364677751146711102105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22695576451834097807401403 34043364677751146711102105)
          ·
            refine ⟨25532523508313360033326579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34043364677751146711102105 25532523508313360033326579)
            ·
              refine ⟨38298785262470040049989869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25532523508313360033326579 38298785262470040049989869)
              ·
                refine ⟨14362044473426265018746201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38298785262470040049989869 14362044473426265018746201)
                ·
                  refine ⟨10771533355069698764059651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14362044473426265018746201 10771533355069698764059651)
                  ·
                    refine ⟨16157300032604548146089477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10771533355069698764059651 16157300032604548146089477)
                    ·
                      refine ⟨3029493756113352777391777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16157300032604548146089477 3029493756113352777391777)
                      ·
                        rfl

theorem cell23_5899918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5899918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899918 prefixEnd_5899918 := by exact prefixLift 5899918
  have htrace : WordTrace (prefixWord ++ tailWord_5899918) baseStart_5899918 baseEnd_5899918 := by
    simpa [prefixWord, tailWord_5899918, baseEnd_5899918] using wordTrace_append hprefix tailTrace_5899918
  have hstable : (prefixWord ++ tailWord_5899918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899918).length < 2 ^ (prefixWord ++ tailWord_5899918).sum := by decide
  have hdescent : baseEnd_5899918 < baseStart_5899918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5899941 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 6]
def baseStart_5899941 : Nat := 118140960795 + 5899941 * 2 ^ 59
def prefixEnd_5899941 : Nat := 4983230072969 + 3 ^ 40 * 5899941 * 2
def baseEnd_5899941 : Nat := 336611729574267354156019

theorem tailTrace_5899941 : CollatzResearch.WordTrace tailWord_5899941 prefixEnd_5899941 336611729574267354156019 := by
  unfold tailWord_5899941
  simp only [CollatzResearch.WordTrace]
  refine ⟨215188526718528861546411677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143459017812352574364274451 215188526718528861546411677)
  ·
    refine ⟨80695697519448323079904379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215188526718528861546411677 80695697519448323079904379)
    ·
      refine ⟨121043546279172484619856569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80695697519448323079904379 121043546279172484619856569)
      ·
        refine ⟨90782659709379363464892427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121043546279172484619856569 90782659709379363464892427)
        ·
          refine ⟨136173989564069045197338641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90782659709379363464892427 136173989564069045197338641)
          ·
            refine ⟨102130492173051783898003981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136173989564069045197338641 102130492173051783898003981)
            ·
              refine ⟨38298934564894418961751493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102130492173051783898003981 38298934564894418961751493)
              ·
                refine ⟨7181050230917703555328405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38298934564894418961751493 7181050230917703555328405)
                ·
                  refine ⟨336611729574267354156019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7181050230917703555328405 336611729574267354156019)
                  ·
                    rfl

theorem cell23_5899941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_5899941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5899941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5899941 prefixEnd_5899941 := by exact prefixLift 5899941
  have htrace : WordTrace (prefixWord ++ tailWord_5899941) baseStart_5899941 baseEnd_5899941 := by
    simpa [prefixWord, tailWord_5899941, baseEnd_5899941] using wordTrace_append hprefix tailTrace_5899941
  have hstable : (prefixWord ++ tailWord_5899941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5899941).length < 2 ^ (prefixWord ++ tailWord_5899941).sum := by decide
  have hdescent : baseEnd_5899941 < baseStart_5899941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5899941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900011 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_5900011 : Nat := 118140960795 + 5900011 * 2 ^ 59
def prefixEnd_5900011 : Nat := 4983230072969 + 3 ^ 40 * 5900011 * 2
def baseEnd_5900011 : Nat := 3029541509814220913528849

theorem tailTrace_5900011 : CollatzResearch.WordTrace tailWord_5900011 prefixEnd_5900011 3029541509814220913528849 := by
  unfold tailWord_5900011
  simp only [CollatzResearch.WordTrace]
  refine ⟨215191079828275263501459887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143460719885516842334306591 215191079828275263501459887)
  ·
    refine ⟨322786619742412895252189831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215191079828275263501459887 322786619742412895252189831)
    ·
      refine ⟨484179929613619342878284747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322786619742412895252189831 484179929613619342878284747)
      ·
        refine ⟨726269894420429014317427121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484179929613619342878284747 726269894420429014317427121)
        ·
          refine ⟨544702420815321760738070341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726269894420429014317427121 544702420815321760738070341)
          ·
            refine ⟨102131703902872830138388189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544702420815321760738070341 102131703902872830138388189)
            ·
              refine ⟨38299388963577311301895571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102131703902872830138388189 38299388963577311301895571)
              ·
                refine ⟨57449083445365966952843357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38299388963577311301895571 57449083445365966952843357)
                ·
                  refine ⟨21543406292012237607316259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57449083445365966952843357 21543406292012237607316259)
                  ·
                    refine ⟨32315109438018356410974389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21543406292012237607316259 32315109438018356410974389)
                    ·
                      refine ⟨3029541509814220913528849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32315109438018356410974389 3029541509814220913528849)
                      ·
                        rfl

theorem cell23_5900011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_5900011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900011 prefixEnd_5900011 := by exact prefixLift 5900011
  have htrace : WordTrace (prefixWord ++ tailWord_5900011) baseStart_5900011 baseEnd_5900011 := by
    simpa [prefixWord, tailWord_5900011, baseEnd_5900011] using wordTrace_append hprefix tailTrace_5900011
  have hstable : (prefixWord ++ tailWord_5900011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900011).length < 2 ^ (prefixWord ++ tailWord_5900011).sum := by decide
  have hdescent : baseEnd_5900011 < baseStart_5900011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900109 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5900109 : Nat := 118140960795 + 5900109 * 2 ^ 59
def prefixEnd_5900109 : Nat := 4983230072969 + 3 ^ 40 * 5900109 * 2
def baseEnd_5900109 : Nat := 3029591830918361530103399

theorem tailTrace_5900109 : CollatzResearch.WordTrace tailWord_5900109 prefixEnd_5900109 3029591830918361530103399 := by
  unfold tailWord_5900109
  simp only [CollatzResearch.WordTrace]
  refine ⟨215194654181920226238527381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143463102787946817492351587 215194654181920226238527381)
  ·
    refine ⟨10087249414777510604930971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215194654181920226238527381 10087249414777510604930971)
    ·
      refine ⟨15130874122166265907396457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087249414777510604930971 15130874122166265907396457)
      ·
        refine ⟨11348155591624699430547343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15130874122166265907396457 11348155591624699430547343)
        ·
          refine ⟨17022233387437049145821015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11348155591624699430547343 17022233387437049145821015)
          ·
            refine ⟨25533350081155573718731523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17022233387437049145821015 25533350081155573718731523)
            ·
              refine ⟨38300025121733360578097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25533350081155573718731523 38300025121733360578097285)
              ·
                refine ⟨7181254710325005108393241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38300025121733360578097285 7181254710325005108393241)
                ·
                  refine ⟨5385941032743753831294931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181254710325005108393241 5385941032743753831294931)
                  ·
                    refine ⟨8078911549115630746942397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385941032743753831294931 8078911549115630746942397)
                    ·
                      refine ⟨3029591830918361530103399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8078911549115630746942397 3029591830918361530103399)
                      ·
                        rfl

theorem cell23_5900109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5900109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900109 prefixEnd_5900109 := by exact prefixLift 5900109
  have htrace : WordTrace (prefixWord ++ tailWord_5900109) baseStart_5900109 baseEnd_5900109 := by
    simpa [prefixWord, tailWord_5900109, baseEnd_5900109] using wordTrace_append hprefix tailTrace_5900109
  have hstable : (prefixWord ++ tailWord_5900109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900109).length < 2 ^ (prefixWord ++ tailWord_5900109).sum := by decide
  have hdescent : baseEnd_5900109 < baseStart_5900109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900128 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_5900128 : Nat := 118140960795 + 5900128 * 2 ^ 59
def prefixEnd_5900128 : Nat := 4983230072969 + 3 ^ 40 * 5900128 * 2
def baseEnd_5900128 : Nat := 3029601587050796955765811

theorem tailTrace_5900128 : CollatzResearch.WordTrace tailWord_5900128 prefixEnd_5900128 3029601587050796955765811 := by
  unfold tailWord_5900128
  simp only [CollatzResearch.WordTrace]
  refine ⟨107597673584425696241734519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143463564779234261655646025 107597673584425696241734519)
  ·
    refine ⟨161396510376638544362601779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107597673584425696241734519 161396510376638544362601779)
    ·
      refine ⟨242094765564957816543902669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161396510376638544362601779 242094765564957816543902669)
      ·
        refine ⟨90785537086859181203963501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242094765564957816543902669 90785537086859181203963501)
        ·
          refine ⟨34044576407572192951486313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90785537086859181203963501 34044576407572192951486313)
          ·
            refine ⟨25533432305679144713614735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34044576407572192951486313 25533432305679144713614735)
            ·
              refine ⟨38300148458518717070422103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25533432305679144713614735 38300148458518717070422103)
              ·
                refine ⟨57450222687778075605633155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38300148458518717070422103 57450222687778075605633155)
                ·
                  refine ⟨86175334031667113408449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57450222687778075605633155 86175334031667113408449733)
                  ·
                    refine ⟨16157875130937583764084325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86175334031667113408449733 16157875130937583764084325)
                    ·
                      refine ⟨3029601587050796955765811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16157875130937583764084325 3029601587050796955765811)
                      ·
                        rfl

theorem cell23_5900128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_5900128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900128 prefixEnd_5900128 := by exact prefixLift 5900128
  have htrace : WordTrace (prefixWord ++ tailWord_5900128) baseStart_5900128 baseEnd_5900128 := by
    simpa [prefixWord, tailWord_5900128, baseEnd_5900128] using wordTrace_append hprefix tailTrace_5900128
  have hstable : (prefixWord ++ tailWord_5900128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900128).length < 2 ^ (prefixWord ++ tailWord_5900128).sum := by decide
  have hdescent : baseEnd_5900128 < baseStart_5900128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900218 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_5900218 : Nat := 118140960795 + 5900218 * 2 ^ 59
def prefixEnd_5900218 : Nat := 4983230072969 + 3 ^ 40 * 5900218 * 2
def baseEnd_5900218 : Nat := 3029647800309701603640397

theorem tailTrace_5900218 : CollatzResearch.WordTrace tailWord_5900218 prefixEnd_5900218 3029647800309701603640397 := by
  unfold tailWord_5900218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53799657434631334463561327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143465753159016891902830205 53799657434631334463561327)
  ·
    refine ⟨80699486151947001695341991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53799657434631334463561327 80699486151947001695341991)
    ·
      refine ⟨121049229227920502543012987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80699486151947001695341991 121049229227920502543012987)
      ·
        refine ⟨181573843841880753814519481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121049229227920502543012987 181573843841880753814519481)
        ·
          refine ⟨136180382881410565360889611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181573843841880753814519481 136180382881410565360889611)
          ·
            refine ⟨204270574322115848041334417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136180382881410565360889611 204270574322115848041334417)
            ·
              refine ⟨153202930741586886031000813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204270574322115848041334417 153202930741586886031000813)
              ·
                refine ⟨57451099028095082261625305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153202930741586886031000813 57451099028095082261625305)
                ·
                  refine ⟨43088324271071311696218979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57451099028095082261625305 43088324271071311696218979)
                  ·
                    refine ⟨64632486406606967544328469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43088324271071311696218979 64632486406606967544328469)
                    ·
                      refine ⟨3029647800309701603640397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64632486406606967544328469 3029647800309701603640397)
                      ·
                        rfl

theorem cell23_5900218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_5900218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900218 prefixEnd_5900218 := by exact prefixLift 5900218
  have htrace : WordTrace (prefixWord ++ tailWord_5900218) baseStart_5900218 baseEnd_5900218 := by
    simpa [prefixWord, tailWord_5900218, baseEnd_5900218] using wordTrace_append hprefix tailTrace_5900218
  have hstable : (prefixWord ++ tailWord_5900218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900218).length < 2 ^ (prefixWord ++ tailWord_5900218).sum := by decide
  have hdescent : baseEnd_5900218 < baseStart_5900218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900222 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5900222 : Nat := 118140960795 + 5900222 * 2 ^ 59
def prefixEnd_5900222 : Nat := 4983230072969 + 3 ^ 40 * 5900222 * 2
def baseEnd_5900222 : Nat := 3029649854232319587990379

theorem tailTrace_5900222 : CollatzResearch.WordTrace tailWord_5900222 prefixEnd_5900222 3029649854232319587990379 := by
  unfold tailWord_5900222
  simp only [CollatzResearch.WordTrace]
  refine ⟨26899846953813855817173865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143465850420340564358260613 26899846953813855817173865)
  ·
    refine ⟨20174885215360391862880399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26899846953813855817173865 20174885215360391862880399)
    ·
      refine ⟨30262327823040587794320599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20174885215360391862880399 30262327823040587794320599)
      ·
        refine ⟨45393491734560881691480899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30262327823040587794320599 45393491734560881691480899)
        ·
          refine ⟨68090237601841322537221349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45393491734560881691480899 68090237601841322537221349)
          ·
            refine ⟨12766919550345247975729003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68090237601841322537221349 12766919550345247975729003)
            ·
              refine ⟨19150379325517871963593505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12766919550345247975729003 19150379325517871963593505)
              ·
                refine ⟨14362784494138403972695129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19150379325517871963593505 14362784494138403972695129)
                ·
                  refine ⟨10772088370603802979521347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14362784494138403972695129 10772088370603802979521347)
                  ·
                    refine ⟨16158132555905704469282021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10772088370603802979521347 16158132555905704469282021)
                    ·
                      refine ⟨3029649854232319587990379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16158132555905704469282021 3029649854232319587990379)
                      ·
                        rfl

theorem cell23_5900222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5900222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900222 prefixEnd_5900222 := by exact prefixLift 5900222
  have htrace : WordTrace (prefixWord ++ tailWord_5900222) baseStart_5900222 baseEnd_5900222 := by
    simpa [prefixWord, tailWord_5900222, baseEnd_5900222] using wordTrace_append hprefix tailTrace_5900222
  have hstable : (prefixWord ++ tailWord_5900222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900222).length < 2 ^ (prefixWord ++ tailWord_5900222).sum := by decide
  have hdescent : baseEnd_5900222 < baseStart_5900222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900232 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_5900232 : Nat := 118140960795 + 5900232 * 2 ^ 59
def prefixEnd_5900232 : Nat := 4983230072969 + 3 ^ 40 * 5900232 * 2
def baseEnd_5900232 : Nat := 1009884996346288182955111

theorem tailTrace_5900232 : CollatzResearch.WordTrace tailWord_5900232 prefixEnd_5900232 1009884996346288182955111 := by
  unfold tailWord_5900232
  simp only [CollatzResearch.WordTrace]
  refine ⟨107599570180237309122627475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143466093573649745496836633 107599570180237309122627475)
  ·
    refine ⟨161399355270355963683941213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107599570180237309122627475 161399355270355963683941213)
    ·
      refine ⟨60524758226383486381477955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161399355270355963683941213 60524758226383486381477955)
      ·
        refine ⟨90787137339575229572216933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60524758226383486381477955 90787137339575229572216933)
        ·
          refine ⟨17022588251170355544790675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90787137339575229572216933 17022588251170355544790675)
          ·
            refine ⟨25533882376755533317186013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17022588251170355544790675 25533882376755533317186013)
            ·
              refine ⟨9575205891283324993944755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25533882376755533317186013 9575205891283324993944755)
              ·
                refine ⟨14362808836924987490917133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9575205891283324993944755 14362808836924987490917133)
                ·
                  refine ⟨5386053313846870309093925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14362808836924987490917133 5386053313846870309093925)
                  ·
                    refine ⟨1009884996346288182955111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386053313846870309093925 1009884996346288182955111)
                    ·
                      rfl

theorem cell23_5900232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_5900232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900232 prefixEnd_5900232 := by exact prefixLift 5900232
  have htrace : WordTrace (prefixWord ++ tailWord_5900232) baseStart_5900232 baseEnd_5900232 := by
    simpa [prefixWord, tailWord_5900232, baseEnd_5900232] using wordTrace_append hprefix tailTrace_5900232
  have hstable : (prefixWord ++ tailWord_5900232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900232).length < 2 ^ (prefixWord ++ tailWord_5900232).sum := by decide
  have hdescent : baseEnd_5900232 < baseStart_5900232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900268 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_5900268 : Nat := 118140960795 + 5900268 * 2 ^ 59
def prefixEnd_5900268 : Nat := 4983230072969 + 3 ^ 40 * 5900268 * 2
def baseEnd_5900268 : Nat := 3029673474342426408015167

theorem tailTrace_5900268 : CollatzResearch.WordTrace tailWord_5900268 prefixEnd_5900268 3029673474342426408015167 := by
  unfold tailWord_5900268
  simp only [CollatzResearch.WordTrace]
  refine ⟨107600226694172098196782729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143466968925562797595710305 107600226694172098196782729)
  ·
    refine ⟨80700170020629073647587047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107600226694172098196782729 80700170020629073647587047)
    ·
      refine ⟨121050255030943610471380571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80700170020629073647587047 121050255030943610471380571)
      ·
        refine ⟨181575382546415415707070857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121050255030943610471380571 181575382546415415707070857)
        ·
          refine ⟨136181536909811561780303143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181575382546415415707070857 136181536909811561780303143)
          ·
            refine ⟨204272305364717342670454715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136181536909811561780303143 204272305364717342670454715)
            ·
              refine ⟨306408458047076014005682073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204272305364717342670454715 306408458047076014005682073)
              ·
                refine ⟨229806343535307010504261555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306408458047076014005682073 229806343535307010504261555)
                ·
                  refine ⟨344709515302960515756392333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229806343535307010504261555 344709515302960515756392333)
                  ·
                    refine ⟨129266068238610193408647125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344709515302960515756392333 129266068238610193408647125)
                    ·
                      refine ⟨3029673474342426408015167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129266068238610193408647125 3029673474342426408015167)
                      ·
                        rfl

theorem cell23_5900268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_5900268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900268 prefixEnd_5900268 := by exact prefixLift 5900268
  have htrace : WordTrace (prefixWord ++ tailWord_5900268) baseStart_5900268 baseEnd_5900268 := by
    simpa [prefixWord, tailWord_5900268, baseEnd_5900268] using wordTrace_append hprefix tailTrace_5900268
  have hstable : (prefixWord ++ tailWord_5900268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900268).length < 2 ^ (prefixWord ++ tailWord_5900268).sum := by decide
  have hdescent : baseEnd_5900268 < baseStart_5900268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900275 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 1, 5]
def baseStart_5900275 : Nat := 118140960795 + 5900275 * 2 ^ 59
def prefixEnd_5900275 : Nat := 4983230072969 + 3 ^ 40 * 5900275 * 2
def baseEnd_5900275 : Nat := 1009892356235669293542545

theorem tailTrace_5900275 : CollatzResearch.WordTrace tailWord_5900275 prefixEnd_5900275 1009892356235669293542545 := by
  unfold tailWord_5900275
  simp only [CollatzResearch.WordTrace]
  refine ⟨215200708699318836589070279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143467139132879224392713519 215200708699318836589070279)
  ·
    refine ⟨322801063048978254883605419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215200708699318836589070279 322801063048978254883605419)
    ·
      refine ⟨484201594573467382325408129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322801063048978254883605419 484201594573467382325408129)
      ·
        refine ⟨363151195930100536744056097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484201594573467382325408129 363151195930100536744056097)
        ·
          refine ⟨272363396947575402558042073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363151195930100536744056097 272363396947575402558042073)
          ·
            refine ⟨204272547710681551918531555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272363396947575402558042073 204272547710681551918531555)
            ·
              refine ⟨306408821566022327877797333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204272547710681551918531555 306408821566022327877797333)
              ·
                refine ⟨7181456755453648309635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 306408821566022327877797333 7181456755453648309635875)
                ·
                  refine ⟨10772185133180472464453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181456755453648309635875 10772185133180472464453813)
                  ·
                    refine ⟨1009892356235669293542545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10772185133180472464453813 1009892356235669293542545)
                    ·
                      rfl

theorem cell23_5900275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 5].length) (baseStart_5900275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900275 prefixEnd_5900275 := by exact prefixLift 5900275
  have htrace : WordTrace (prefixWord ++ tailWord_5900275) baseStart_5900275 baseEnd_5900275 := by
    simpa [prefixWord, tailWord_5900275, baseEnd_5900275] using wordTrace_append hprefix tailTrace_5900275
  have hstable : (prefixWord ++ tailWord_5900275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900275).length < 2 ^ (prefixWord ++ tailWord_5900275).sum := by decide
  have hdescent : baseEnd_5900275 < baseStart_5900275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900305 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_5900305 : Nat := 118140960795 + 5900305 * 2 ^ 59
def prefixEnd_5900305 : Nat := 4983230072969 + 3 ^ 40 * 5900305 * 2
def baseEnd_5900305 : Nat := 1009897491042214254417499

theorem tailTrace_5900305 : CollatzResearch.WordTrace tailWord_5900305 prefixEnd_5900305 1009897491042214254417499 := by
  unfold tailWord_5900305
  simp only [CollatzResearch.WordTrace]
  refine ⟨215201802889210151712662369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143467868592806767808441579 215201802889210151712662369)
  ·
    refine ⟨161401352166907613784496777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215201802889210151712662369 161401352166907613784496777)
    ·
      refine ⟨121051014125180710338372583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161401352166907613784496777 121051014125180710338372583)
      ·
        refine ⟨181576521187771065507558875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121051014125180710338372583 181576521187771065507558875)
        ·
          refine ⟨272364781781656598261338313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181576521187771065507558875 272364781781656598261338313)
          ·
            refine ⟨204273586336242448696003735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272364781781656598261338313 204273586336242448696003735)
            ·
              refine ⟨306410379504363673044005603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204273586336242448696003735 306410379504363673044005603)
              ·
                refine ⟨459615569256545509566008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306410379504363673044005603 459615569256545509566008405)
                ·
                  refine ⟨5386119952225142690226661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 459615569256545509566008405 5386119952225142690226661)
                  ·
                    refine ⟨1009897491042214254417499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386119952225142690226661 1009897491042214254417499)
                    ·
                      rfl

theorem cell23_5900305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_5900305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900305 prefixEnd_5900305 := by exact prefixLift 5900305
  have htrace : WordTrace (prefixWord ++ tailWord_5900305) baseStart_5900305 baseEnd_5900305 := by
    simpa [prefixWord, tailWord_5900305, baseEnd_5900305] using wordTrace_append hprefix tailTrace_5900305
  have hstable : (prefixWord ++ tailWord_5900305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900305).length < 2 ^ (prefixWord ++ tailWord_5900305).sum := by decide
  have hdescent : baseEnd_5900305 < baseStart_5900305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900312 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_5900312 : Nat := 118140960795 + 5900312 * 2 ^ 59
def prefixEnd_5900312 : Nat := 4983230072969 + 3 ^ 40 * 5900312 * 2
def baseEnd_5900312 : Nat := 3029696067491224235864965

theorem tailTrace_5900312 : CollatzResearch.WordTrace tailWord_5900312 prefixEnd_5900312 3029696067491224235864965 := by
  unfold tailWord_5900312
  simp only [CollatzResearch.WordTrace]
  refine ⟨107601029100092395954083595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143468038800123194605444793 107601029100092395954083595)
  ·
    refine ⟨161401543650138593931125393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107601029100092395954083595 161401543650138593931125393)
    ·
      refine ⟨121051157737603945448344045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161401543650138593931125393 121051157737603945448344045)
      ·
        refine ⟨45394184151601479543129017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121051157737603945448344045 45394184151601479543129017)
        ·
          refine ⟨34045638113701109657346763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45394184151601479543129017 34045638113701109657346763)
          ·
            refine ⟨51068457170551664486020145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34045638113701109657346763 51068457170551664486020145)
            ·
              refine ⟨38301342877913748364515109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51068457170551664486020145 38301342877913748364515109)
              ·
                refine ⟨7181501789608827818346583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38301342877913748364515109 7181501789608827818346583)
                ·
                  refine ⟨10772252684413241727519875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181501789608827818346583 10772252684413241727519875)
                  ·
                    refine ⟨16158379026619862591279813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10772252684413241727519875 16158379026619862591279813)
                    ·
                      refine ⟨3029696067491224235864965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16158379026619862591279813 3029696067491224235864965)
                      ·
                        rfl

theorem cell23_5900312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_5900312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900312 prefixEnd_5900312 := by exact prefixLift 5900312
  have htrace : WordTrace (prefixWord ++ tailWord_5900312) baseStart_5900312 baseEnd_5900312 := by
    simpa [prefixWord, tailWord_5900312, baseEnd_5900312] using wordTrace_append hprefix tailTrace_5900312
  have hstable : (prefixWord ++ tailWord_5900312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900312).length < 2 ^ (prefixWord ++ tailWord_5900312).sum := by decide
  have hdescent : baseEnd_5900312 < baseStart_5900312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900316 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5900316 : Nat := 118140960795 + 5900316 * 2 ^ 59
def prefixEnd_5900316 : Nat := 4983230072969 + 3 ^ 40 * 5900316 * 2
def baseEnd_5900316 : Nat := 3029698121413842220214947

theorem tailTrace_5900316 : CollatzResearch.WordTrace tailWord_5900316 prefixEnd_5900316 3029698121413842220214947 := by
  unfold tailWord_5900316
  simp only [CollatzResearch.WordTrace]
  refine ⟨107601102046085150295656401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143468136061446867060875201 107601102046085150295656401)
  ·
    refine ⟨80700826534563862721742301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107601102046085150295656401 80700826534563862721742301)
    ·
      refine ⟨30262809950461448520653363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80700826534563862721742301 30262809950461448520653363)
      ·
        refine ⟨45394214925692172780980045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30262809950461448520653363 45394214925692172780980045)
        ·
          refine ⟨17022830597134564792867517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45394214925692172780980045 17022830597134564792867517)
          ·
            refine ⟨6383561473925461797325319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17022830597134564792867517 6383561473925461797325319)
            ·
              refine ⟨9575342210888192695987979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383561473925461797325319 9575342210888192695987979)
              ·
                refine ⟨14363013316332289043981969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9575342210888192695987979 14363013316332289043981969)
                ·
                  refine ⟨10772259987249216782986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14363013316332289043981969 10772259987249216782986477)
                  ·
                    refine ⟨4039597495218456293619929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10772259987249216782986477 4039597495218456293619929)
                    ·
                      refine ⟨3029698121413842220214947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039597495218456293619929 3029698121413842220214947)
                      ·
                        rfl

theorem cell23_5900316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5900316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900316 prefixEnd_5900316 := by exact prefixLift 5900316
  have htrace : WordTrace (prefixWord ++ tailWord_5900316) baseStart_5900316 baseEnd_5900316 := by
    simpa [prefixWord, tailWord_5900316, baseEnd_5900316] using wordTrace_append hprefix tailTrace_5900316
  have hstable : (prefixWord ++ tailWord_5900316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900316).length < 2 ^ (prefixWord ++ tailWord_5900316).sum := by decide
  have hdescent : baseEnd_5900316 < baseStart_5900316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900322 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5900322 : Nat := 118140960795 + 5900322 * 2 ^ 59
def prefixEnd_5900322 : Nat := 4983230072969 + 3 ^ 40 * 5900322 * 2
def baseEnd_5900322 : Nat := 1009900400765923065579973

theorem tailTrace_5900322 : CollatzResearch.WordTrace tailWord_5900322 prefixEnd_5900322 1009900400765923065579973 := by
  unfold tailWord_5900322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800605732537140904007805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143468281953432375744020813 53800605732537140904007805)
  ·
    refine ⟨20175227149701427839002927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53800605732537140904007805 20175227149701427839002927)
    ·
      refine ⟨30262840724552141758504391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20175227149701427839002927 30262840724552141758504391)
      ·
        refine ⟨45394261086828212637756587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30262840724552141758504391 45394261086828212637756587)
        ·
          refine ⟨68091391630242318956634881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45394261086828212637756587 68091391630242318956634881)
          ·
            refine ⟨51068543722681739217476161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68091391630242318956634881 51068543722681739217476161)
            ·
              refine ⟨38301407792011304413107121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51068543722681739217476161 38301407792011304413107121)
              ·
                refine ⟨28726055844008478309830341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38301407792011304413107121 28726055844008478309830341)
                ·
                  refine ⟨5386135470751589683093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28726055844008478309830341 5386135470751589683093189)
                  ·
                    refine ⟨1009900400765923065579973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386135470751589683093189 1009900400765923065579973)
                    ·
                      rfl

theorem cell23_5900322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5900322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900322 prefixEnd_5900322 := by exact prefixLift 5900322
  have htrace : WordTrace (prefixWord ++ tailWord_5900322) baseStart_5900322 baseEnd_5900322 := by
    simpa [prefixWord, tailWord_5900322, baseEnd_5900322] using wordTrace_append hprefix tailTrace_5900322
  have hstable : (prefixWord ++ tailWord_5900322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900322).length < 2 ^ (prefixWord ++ tailWord_5900322).sum := by decide
  have hdescent : baseEnd_5900322 < baseStart_5900322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900342 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5900342 : Nat := 118140960795 + 5900342 * 2 ^ 59
def prefixEnd_5900342 : Nat := 4983230072969 + 3 ^ 40 * 5900342 * 2
def baseEnd_5900342 : Nat := 3029711471910859118489827

theorem tailTrace_5900342 : CollatzResearch.WordTrace tailWord_5900342 prefixEnd_5900342 3029711471910859118489827 := by
  unfold tailWord_5900342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450197024379756689484955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143468768260050738021172853 13450197024379756689484955)
  ·
    refine ⟨20175295536569635034227433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13450197024379756689484955 20175295536569635034227433)
    ·
      refine ⟨15131471652427226275670575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20175295536569635034227433 15131471652427226275670575)
      ·
        refine ⟨22697207478640839413505863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131471652427226275670575 22697207478640839413505863)
        ·
          refine ⟨34045811217961259120258795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22697207478640839413505863 34045811217961259120258795)
          ·
            refine ⟨51068716826941888680388193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34045811217961259120258795 51068716826941888680388193)
            ·
              refine ⟨38301537620206416510291145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51068716826941888680388193 38301537620206416510291145)
              ·
                refine ⟨28726153215154812382718359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38301537620206416510291145 28726153215154812382718359)
                ·
                  refine ⟨43089229822732218574077539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28726153215154812382718359 43089229822732218574077539)
                  ·
                    refine ⟨64633844734098327861116309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43089229822732218574077539 64633844734098327861116309)
                    ·
                      refine ⟨3029711471910859118489827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64633844734098327861116309 3029711471910859118489827)
                      ·
                        rfl

theorem cell23_5900342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5900342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900342 prefixEnd_5900342 := by exact prefixLift 5900342
  have htrace : WordTrace (prefixWord ++ tailWord_5900342) baseStart_5900342 baseEnd_5900342 := by
    simpa [prefixWord, tailWord_5900342, baseEnd_5900342] using wordTrace_append hprefix tailTrace_5900342
  have hstable : (prefixWord ++ tailWord_5900342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900342).length < 2 ^ (prefixWord ++ tailWord_5900342).sum := by decide
  have hdescent : baseEnd_5900342 < baseStart_5900342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900375 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5900375 : Nat := 118140960795 + 5900375 * 2 ^ 59
def prefixEnd_5900375 : Nat := 4983230072969 + 3 ^ 40 * 5900375 * 2
def baseEnd_5900375 : Nat := 3029728416772457489377175

theorem tailTrace_5900375 : CollatzResearch.WordTrace tailWord_5900375 prefixEnd_5900375 3029728416772457489377175 := by
  unfold tailWord_5900375
  simp only [CollatzResearch.WordTrace]
  refine ⟨215204355998956553667710579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143469570665971035778473719 215204355998956553667710579)
  ·
    refine ⟨322806533998434830501565869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215204355998956553667710579 322806533998434830501565869)
    ·
      refine ⟨121052450249413061438087201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322806533998434830501565869 121052450249413061438087201)
      ·
        refine ⟨90789337687059796078565401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121052450249413061438087201 90789337687059796078565401)
        ·
          refine ⟨68092003265294847058924051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90789337687059796078565401 68092003265294847058924051)
          ·
            refine ⟨102138004897942270588386077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68092003265294847058924051 102138004897942270588386077)
            ·
              refine ⟨38301751836728351470644779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102138004897942270588386077 38301751836728351470644779)
              ·
                refine ⟨57452627755092527205967169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38301751836728351470644779 57452627755092527205967169)
                ·
                  refine ⟨43089470816319395404475377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57452627755092527205967169 43089470816319395404475377)
                  ·
                    refine ⟨32317103112239546553356533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43089470816319395404475377 32317103112239546553356533)
                    ·
                      refine ⟨3029728416772457489377175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32317103112239546553356533 3029728416772457489377175)
                      ·
                        rfl

theorem cell23_5900375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5900375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900375 prefixEnd_5900375 := by exact prefixLift 5900375
  have htrace : WordTrace (prefixWord ++ tailWord_5900375) baseStart_5900375 baseEnd_5900375 := by
    simpa [prefixWord, tailWord_5900375, baseEnd_5900375] using wordTrace_append hprefix tailTrace_5900375
  have hstable : (prefixWord ++ tailWord_5900375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900375).length < 2 ^ (prefixWord ++ tailWord_5900375).sum := by decide
  have hdescent : baseEnd_5900375 < baseStart_5900375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900380 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5900380 : Nat := 118140960795 + 5900380 * 2 ^ 59
def prefixEnd_5900380 : Nat := 4983230072969 + 3 ^ 40 * 5900380 * 2
def baseEnd_5900380 : Nat := 3029730984175729969814653

theorem tailTrace_5900380 : CollatzResearch.WordTrace tailWord_5900380 prefixEnd_5900380 3029730984175729969814653 := by
  unfold tailWord_5900380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107602269181969219760821297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143469692242625626347761729 107602269181969219760821297)
  ·
    refine ⟨80701701886476914820615973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107602269181969219760821297 80701701886476914820615973)
    ·
      refine ⟨15131569103714421528865495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80701701886476914820615973 15131569103714421528865495)
      ·
        refine ⟨22697353655571632293298243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131569103714421528865495 22697353655571632293298243)
        ·
          refine ⟨34046030483357448439947365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22697353655571632293298243 34046030483357448439947365)
          ·
            refine ⟨6383630715629521582490131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34046030483357448439947365 6383630715629521582490131)
            ·
              refine ⟨9575446073444282373735197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383630715629521582490131 9575446073444282373735197)
              ·
                refine ⟨3590792277541605890150699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9575446073444282373735197 3590792277541605890150699)
                ·
                  refine ⟨5386188416312408835226049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590792277541605890150699 5386188416312408835226049)
                  ·
                    refine ⟨4039641312234306626419537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386188416312408835226049 4039641312234306626419537)
                    ·
                      refine ⟨3029730984175729969814653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039641312234306626419537 3029730984175729969814653)
                      ·
                        rfl

theorem cell23_5900380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5900380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900380 prefixEnd_5900380 := by exact prefixLift 5900380
  have htrace : WordTrace (prefixWord ++ tailWord_5900380) baseStart_5900380 baseEnd_5900380 := by
    simpa [prefixWord, tailWord_5900380, baseEnd_5900380] using wordTrace_append hprefix tailTrace_5900380
  have hstable : (prefixWord ++ tailWord_5900380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900380).length < 2 ^ (prefixWord ++ tailWord_5900380).sum := by decide
  have hdescent : baseEnd_5900380 < baseStart_5900380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900385 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5900385 : Nat := 118140960795 + 5900385 * 2 ^ 59
def prefixEnd_5900385 : Nat := 4983230072969 + 3 ^ 40 * 5900385 * 2
def baseEnd_5900385 : Nat := 3029733551579002450252129

theorem tailTrace_5900385 : CollatzResearch.WordTrace tailWord_5900385 prefixEnd_5900385 3029733551579002450252129 := by
  unfold tailWord_5900385
  simp only [CollatzResearch.WordTrace]
  refine ⟨215204720728920325375574609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143469813819280216917049739 215204720728920325375574609)
  ·
    refine ⟨161403540546690244031680957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215204720728920325375574609 161403540546690244031680957)
    ·
      refine ⟨60526327705008841511880359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161403540546690244031680957 60526327705008841511880359)
      ·
        refine ⟨90789491557513262267820539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60526327705008841511880359 90789491557513262267820539)
        ·
          refine ⟨136184237336269893401730809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90789491557513262267820539 136184237336269893401730809)
          ·
            refine ⟨102138178002202420051298107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136184237336269893401730809 102138178002202420051298107)
            ·
              refine ⟨153207267003303630076947161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102138178002202420051298107 153207267003303630076947161)
              ·
                refine ⟨114905450252477722557710371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153207267003303630076947161 114905450252477722557710371)
                ·
                  refine ⟨172358175378716583836565557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114905450252477722557710371 172358175378716583836565557)
                  ·
                    refine ⟨16158578941754679734678021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172358175378716583836565557 16158578941754679734678021)
                    ·
                      refine ⟨3029733551579002450252129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16158578941754679734678021 3029733551579002450252129)
                      ·
                        rfl

theorem cell23_5900385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5900385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900385 prefixEnd_5900385 := by exact prefixLift 5900385
  have htrace : WordTrace (prefixWord ++ tailWord_5900385) baseStart_5900385 baseEnd_5900385 := by
    simpa [prefixWord, tailWord_5900385, baseEnd_5900385] using wordTrace_append hprefix tailTrace_5900385
  have hstable : (prefixWord ++ tailWord_5900385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900385).length < 2 ^ (prefixWord ++ tailWord_5900385).sum := by decide
  have hdescent : baseEnd_5900385 < baseStart_5900385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900413 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_5900413 : Nat := 118140960795 + 5900413 * 2 ^ 59
def prefixEnd_5900413 : Nat := 4983230072969 + 3 ^ 40 * 5900413 * 2
def baseEnd_5900413 : Nat := 3029747929037328340702001

theorem tailTrace_5900413 : CollatzResearch.WordTrace tailWord_5900413 prefixEnd_5900413 3029747929037328340702001 := by
  unfold tailWord_5900413
  simp only [CollatzResearch.WordTrace]
  refine ⟨215205741972818886157593893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143470494648545924105062595 215205741972818886157593893)
  ·
    refine ⟨40351076619903541154548855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215205741972818886157593893 40351076619903541154548855)
    ·
      refine ⟨60526614929855311731823283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40351076619903541154548855 60526614929855311731823283)
      ·
        refine ⟨90789922394782967597734925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60526614929855311731823283 90789922394782967597734925)
        ·
          refine ⟨34046220898043612849150597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90789922394782967597734925 34046220898043612849150597)
          ·
            refine ⟨6383666418383177409215737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34046220898043612849150597 6383666418383177409215737)
            ·
              refine ⟨4787749813787383056911803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6383666418383177409215737 4787749813787383056911803)
              ·
                refine ⟨7181624720681074585367705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787749813787383056911803 7181624720681074585367705)
                ·
                  refine ⟨5386218540510805939025779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181624720681074585367705 5386218540510805939025779)
                  ·
                    refine ⟨8079327810766208908538669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386218540510805939025779 8079327810766208908538669)
                    ·
                      refine ⟨3029747929037328340702001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8079327810766208908538669 3029747929037328340702001)
                      ·
                        rfl

theorem cell23_5900413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_5900413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900413 prefixEnd_5900413 := by exact prefixLift 5900413
  have htrace : WordTrace (prefixWord ++ tailWord_5900413) baseStart_5900413 baseEnd_5900413 := by
    simpa [prefixWord, tailWord_5900413, baseEnd_5900413] using wordTrace_append hprefix tailTrace_5900413
  have hstable : (prefixWord ++ tailWord_5900413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900413).length < 2 ^ (prefixWord ++ tailWord_5900413).sum := by decide
  have hdescent : baseEnd_5900413 < baseStart_5900413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900425 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 9]
def baseStart_5900425 : Nat := 118140960795 + 5900425 * 2 ^ 59
def prefixEnd_5900425 : Nat := 4983230072969 + 3 ^ 40 * 5900425 * 2
def baseEnd_5900425 : Nat := 336639343422798032639105

theorem tailTrace_5900425 : CollatzResearch.WordTrace tailWord_5900425 prefixEnd_5900425 336639343422798032639105 := by
  unfold tailWord_5900425
  simp only [CollatzResearch.WordTrace]
  refine ⟨215206179648775412207030729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143470786432516941471353819 215206179648775412207030729)
  ·
    refine ⟨161404634736581559155273047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215206179648775412207030729 161404634736581559155273047)
    ·
      refine ⟨242106952104872338732909571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161404634736581559155273047 242106952104872338732909571)
      ·
        refine ⟨363160428157308508099364357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242106952104872338732909571 363160428157308508099364357)
        ·
          refine ⟨68092580279495345268630817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363160428157308508099364357 68092580279495345268630817)
          ·
            refine ⟨51069435209621508951473113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68092580279495345268630817 51069435209621508951473113)
            ·
              refine ⟨38302076407216131713604835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51069435209621508951473113 38302076407216131713604835)
              ·
                refine ⟨57453114610824197570407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38302076407216131713604835 57453114610824197570407253)
                ·
                  refine ⟨336639343422798032639105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57453114610824197570407253 336639343422798032639105)
                  ·
                    rfl

theorem cell23_5900425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_5900425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900425 prefixEnd_5900425 := by exact prefixLift 5900425
  have htrace : WordTrace (prefixWord ++ tailWord_5900425) baseStart_5900425 baseEnd_5900425 := by
    simpa [prefixWord, tailWord_5900425, baseEnd_5900425] using wordTrace_append hprefix tailTrace_5900425
  have hstable : (prefixWord ++ tailWord_5900425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900425).length < 2 ^ (prefixWord ++ tailWord_5900425).sum := by decide
  have hdescent : baseEnd_5900425 < baseStart_5900425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900522 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5900522 : Nat := 118140960795 + 5900522 * 2 ^ 59
def prefixEnd_5900522 : Nat := 4983230072969 + 3 ^ 40 * 5900522 * 2
def baseEnd_5900522 : Nat := 3029803898428668414238999

theorem tailTrace_5900522 : CollatzResearch.WordTrace tailWord_5900522 prefixEnd_5900522 3029803898428668414238999 := by
  unfold tailWord_5900522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53802429382355999443327955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143473145019615998515541213 53802429382355999443327955)
  ·
    refine ⟨80703644073533999164991933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53802429382355999443327955 80703644073533999164991933)
    ·
      refine ⟨30263866527575249686871975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80703644073533999164991933 30263866527575249686871975)
      ·
        refine ⟨45395799791362874530307963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30263866527575249686871975 45395799791362874530307963)
        ·
          refine ⟨68093699687044311795461945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45395799791362874530307963 68093699687044311795461945)
          ·
            refine ⟨51070274765283233846596459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68093699687044311795461945 51070274765283233846596459)
            ·
              refine ⟨76605412147924850769894689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51070274765283233846596459 76605412147924850769894689)
              ·
                refine ⟨57454059110943638077421017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76605412147924850769894689 57454059110943638077421017)
                ·
                  refine ⟨43090544333207728558065763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57454059110943638077421017 43090544333207728558065763)
                  ·
                    refine ⟨64635816499811592837098645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43090544333207728558065763 64635816499811592837098645)
                    ·
                      refine ⟨3029803898428668414238999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64635816499811592837098645 3029803898428668414238999)
                      ·
                        rfl

theorem cell23_5900522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5900522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900522 prefixEnd_5900522 := by exact prefixLift 5900522
  have htrace : WordTrace (prefixWord ++ tailWord_5900522) baseStart_5900522 baseEnd_5900522 := by
    simpa [prefixWord, tailWord_5900522, baseEnd_5900522] using wordTrace_append hprefix tailTrace_5900522
  have hstable : (prefixWord ++ tailWord_5900522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900522).length < 2 ^ (prefixWord ++ tailWord_5900522).sum := by decide
  have hdescent : baseEnd_5900522 < baseStart_5900522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900546 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_5900546 : Nat := 118140960795 + 5900546 * 2 ^ 59
def prefixEnd_5900546 : Nat := 4983230072969 + 3 ^ 40 * 5900546 * 2
def baseEnd_5900546 : Nat := 3029816221964376320338889

theorem tailTrace_5900546 : CollatzResearch.WordTrace tailWord_5900546 prefixEnd_5900546 3029816221964376320338889 := by
  unfold tailWord_5900546
  simp only [CollatzResearch.WordTrace]
  refine ⟨53802648220334262468046373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143473728587558033248123661 53802648220334262468046373)
  ·
    refine ⟨10087996541312674212758695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53802648220334262468046373 10087996541312674212758695)
    ·
      refine ⟨15131994811969011319138043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087996541312674212758695 15131994811969011319138043)
      ·
        refine ⟨22697992217953516978707065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131994811969011319138043 22697992217953516978707065)
        ·
          refine ⟨17023494163465137734030299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22697992217953516978707065 17023494163465137734030299)
          ·
            refine ⟨25535241245197706601045449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17023494163465137734030299 25535241245197706601045449)
            ·
              refine ⟨19151430933898279950784087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25535241245197706601045449 19151430933898279950784087)
              ·
                refine ⟨28727146400847419926176131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19151430933898279950784087 28727146400847419926176131)
                ·
                  refine ⟨43090719601271129889264197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28727146400847419926176131 43090719601271129889264197)
                  ·
                    refine ⟨8079509925238336854237037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43090719601271129889264197 8079509925238336854237037)
                    ·
                      refine ⟨3029816221964376320338889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8079509925238336854237037 3029816221964376320338889)
                      ·
                        rfl

theorem cell23_5900546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_5900546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900546 prefixEnd_5900546 := by exact prefixLift 5900546
  have htrace : WordTrace (prefixWord ++ tailWord_5900546) baseStart_5900546 baseEnd_5900546 := by
    simpa [prefixWord, tailWord_5900546, baseEnd_5900546] using wordTrace_append hprefix tailTrace_5900546
  have hstable : (prefixWord ++ tailWord_5900546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900546).length < 2 ^ (prefixWord ++ tailWord_5900546).sum := by decide
  have hdescent : baseEnd_5900546 < baseStart_5900546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900553 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 1, 4]
def baseStart_5900553 : Nat := 118140960795 + 5900553 * 2 ^ 59
def prefixEnd_5900553 : Nat := 4983230072969 + 3 ^ 40 * 5900553 * 2
def baseEnd_5900553 : Nat := 1009939938776319264317119

theorem tailTrace_5900553 : CollatzResearch.WordTrace tailWord_5900553 prefixEnd_5900553 1009939938776319264317119 := by
  unfold tailWord_5900553
  simp only [CollatzResearch.WordTrace]
  refine ⟨215210848192311690067690313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143473898794874460045126875 215210848192311690067690313)
  ·
    refine ⟨161408136144233767550767735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215210848192311690067690313 161408136144233767550767735)
    ·
      refine ⟨242112204216350651326151603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161408136144233767550767735 242112204216350651326151603)
      ·
        refine ⟨363168306324525976989227405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242112204216350651326151603 363168306324525976989227405)
        ·
          refine ⟨136188114871697241370960277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363168306324525976989227405 136188114871697241370960277)
          ·
            refine ⟨6383817884610808189263763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136188114871697241370960277 6383817884610808189263763)
            ·
              refine ⟨9575726826916212283895645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383817884610808189263763 9575726826916212283895645)
              ·
                refine ⟨3590897560093579606460867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9575726826916212283895645 3590897560093579606460867)
                ·
                  refine ⟨5386346340140369409691301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590897560093579606460867 5386346340140369409691301)
                  ·
                    refine ⟨1009939938776319264317119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386346340140369409691301 1009939938776319264317119)
                    ·
                      rfl

theorem cell23_5900553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 4].length) (baseStart_5900553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900553 prefixEnd_5900553 := by exact prefixLift 5900553
  have htrace : WordTrace (prefixWord ++ tailWord_5900553) baseStart_5900553 baseEnd_5900553 := by
    simpa [prefixWord, tailWord_5900553, baseEnd_5900553] using wordTrace_append hprefix tailTrace_5900553
  have hstable : (prefixWord ++ tailWord_5900553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900553).length < 2 ^ (prefixWord ++ tailWord_5900553).sum := by decide
  have hdescent : baseEnd_5900553 < baseStart_5900553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900559 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_5900559 : Nat := 118140960795 + 5900559 * 2 ^ 59
def prefixEnd_5900559 : Nat := 4983230072969 + 3 ^ 40 * 5900559 * 2
def baseEnd_5900559 : Nat := 3029822897212884769476329

theorem tailTrace_5900559 : CollatzResearch.WordTrace tailWord_5900559 prefixEnd_5900559 3029822897212884769476329 := by
  unfold tailWord_5900559
  simp only [CollatzResearch.WordTrace]
  refine ⟨215211067030289953092408731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143474044686859968728272487 215211067030289953092408731)
  ·
    refine ⟨322816600545434929638613097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215211067030289953092408731 322816600545434929638613097)
    ·
      refine ⟨242112450409076197228959823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322816600545434929638613097 242112450409076197228959823)
      ·
        refine ⟨363168675613614295843439735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242112450409076197228959823 363168675613614295843439735)
        ·
          refine ⟨544753013420421443765159603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363168675613614295843439735 544753013420421443765159603)
          ·
            refine ⟨817129520130632165647739405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544753013420421443765159603 817129520130632165647739405)
            ·
              refine ⟨306423570048987062117902277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817129520130632165647739405 306423570048987062117902277)
              ·
                refine ⟨57454419384185074147106677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306423570048987062117902277 57454419384185074147106677)
                ·
                  refine ⟨5386351817267350701291251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57454419384185074147106677 5386351817267350701291251)
                  ·
                    refine ⟨8079527725901026051936877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386351817267350701291251 8079527725901026051936877)
                    ·
                      refine ⟨3029822897212884769476329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8079527725901026051936877 3029822897212884769476329)
                      ·
                        rfl

theorem cell23_5900559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_5900559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900559 prefixEnd_5900559 := by exact prefixLift 5900559
  have htrace : WordTrace (prefixWord ++ tailWord_5900559) baseStart_5900559 baseEnd_5900559 := by
    simpa [prefixWord, tailWord_5900559, baseEnd_5900559] using wordTrace_append hprefix tailTrace_5900559
  have hstable : (prefixWord ++ tailWord_5900559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900559).length < 2 ^ (prefixWord ++ tailWord_5900559).sum := by decide
  have hdescent : baseEnd_5900559 < baseStart_5900559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900570 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_5900570 : Nat := 118140960795 + 5900570 * 2 ^ 59
def prefixEnd_5900570 : Nat := 4983230072969 + 3 ^ 40 * 5900570 * 2
def baseEnd_5900570 : Nat := 1009942848500028075479593

theorem tailTrace_5900570 : CollatzResearch.WordTrace tailWord_5900570 prefixEnd_5900570 1009942848500028075479593 := by
  unfold tailWord_5900570
  simp only [CollatzResearch.WordTrace]
  refine ⟨53802867058312525492764791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143474312155500067980706109 53802867058312525492764791)
  ·
    refine ⟨80704300587468788239147187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53802867058312525492764791 80704300587468788239147187)
    ·
      refine ⟨121056450881203182358720781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80704300587468788239147187 121056450881203182358720781)
      ·
        refine ⟨45396169080451193384520293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121056450881203182358720781 45396169080451193384520293)
        ·
          refine ⟨8511781702584598759597555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45396169080451193384520293 8511781702584598759597555)
          ·
            refine ⟨12767672553876898139396333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511781702584598759597555 12767672553876898139396333)
            ·
              refine ⟨4787877207703836802273625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12767672553876898139396333 4787877207703836802273625)
              ·
                refine ⟨3590907905777877601705219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4787877207703836802273625 3590907905777877601705219)
                ·
                  refine ⟨5386361858666816402557829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590907905777877601705219 5386361858666816402557829)
                  ·
                    refine ⟨1009942848500028075479593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386361858666816402557829 1009942848500028075479593)
                    ·
                      rfl

theorem cell23_5900570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_5900570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900570 prefixEnd_5900570 := by exact prefixLift 5900570
  have htrace : WordTrace (prefixWord ++ tailWord_5900570) baseStart_5900570 baseEnd_5900570 := by
    simpa [prefixWord, tailWord_5900570, baseEnd_5900570] using wordTrace_append hprefix tailTrace_5900570
  have hstable : (prefixWord ++ tailWord_5900570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900570).length < 2 ^ (prefixWord ++ tailWord_5900570).sum := by decide
  have hdescent : baseEnd_5900570 < baseStart_5900570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900572 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5900572 : Nat := 118140960795 + 5900572 * 2 ^ 59
def prefixEnd_5900572 : Nat := 4983230072969 + 3 ^ 40 * 5900572 * 2
def baseEnd_5900572 : Nat := 3029829572461393218613769

theorem tailTrace_5900572 : CollatzResearch.WordTrace tailWord_5900572 prefixEnd_5900572 3029829572461393218613769 := by
  unfold tailWord_5900572
  simp only [CollatzResearch.WordTrace]
  refine ⟨107605770589621428156315985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143474360786161904208421313 107605770589621428156315985)
  ·
    refine ⟨80704327942216071117236989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107605770589621428156315985 80704327942216071117236989)
    ·
      refine ⟨30264122978331026668963871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80704327942216071117236989 30264122978331026668963871)
      ·
        refine ⟨45396184467496540003445807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30264122978331026668963871 45396184467496540003445807)
        ·
          refine ⟨68094276701244810005168711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45396184467496540003445807 68094276701244810005168711)
          ·
            refine ⟨102141415051867215007753067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68094276701244810005168711 102141415051867215007753067)
            ·
              refine ⟨153212122577800822511629601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102141415051867215007753067 153212122577800822511629601)
              ·
                refine ⟨114909091933350616883722201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153212122577800822511629601 114909091933350616883722201)
                ·
                  refine ⟨86181818950012962662791651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114909091933350616883722201 86181818950012962662791651)
                  ·
                    refine ⟨129272728425019443994187477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86181818950012962662791651 129272728425019443994187477)
                    ·
                      refine ⟨3029829572461393218613769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129272728425019443994187477 3029829572461393218613769)
                      ·
                        rfl

theorem cell23_5900572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5900572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900572 prefixEnd_5900572 := by exact prefixLift 5900572
  have htrace : WordTrace (prefixWord ++ tailWord_5900572) baseStart_5900572 baseEnd_5900572 := by
    simpa [prefixWord, tailWord_5900572, baseEnd_5900572] using wordTrace_append hprefix tailTrace_5900572
  have hstable : (prefixWord ++ tailWord_5900572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900572).length < 2 ^ (prefixWord ++ tailWord_5900572).sum := by decide
  have hdescent : baseEnd_5900572 < baseStart_5900572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900596 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_5900596 : Nat := 118140960795 + 5900596 * 2 ^ 59
def prefixEnd_5900596 : Nat := 4983230072969 + 3 ^ 40 * 5900596 * 2
def baseEnd_5900596 : Nat := 1009947298665700374904553

theorem tailTrace_5900596 : CollatzResearch.WordTrace tailWord_5900596 prefixEnd_5900596 1009947298665700374904553 := by
  unfold tailWord_5900596
  simp only [CollatzResearch.WordTrace]
  refine ⟨107606208265577954205752821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143474944354103938941003761 107606208265577954205752821)
  ·
    refine ⟨10088082024897933206789327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107606208265577954205752821 10088082024897933206789327)
    ·
      refine ⟨15132123037346899810183991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088082024897933206789327 15132123037346899810183991)
      ·
        refine ⟨22698184556020349715275987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132123037346899810183991 22698184556020349715275987)
        ·
          refine ⟨34047276834030524572913981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22698184556020349715275987 34047276834030524572913981)
          ·
            refine ⟨12767728812761446714842743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34047276834030524572913981 12767728812761446714842743)
            ·
              refine ⟨19151593219142170072264115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767728812761446714842743 19151593219142170072264115)
              ·
                refine ⟨28727389828713255108396173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19151593219142170072264115 28727389828713255108396173)
                ·
                  refine ⟨10772771185767470665648565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28727389828713255108396173 10772771185767470665648565)
                  ·
                    refine ⟨1009947298665700374904553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10772771185767470665648565 1009947298665700374904553)
                    ·
                      rfl

theorem cell23_5900596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_5900596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900596 prefixEnd_5900596 := by exact prefixLift 5900596
  have htrace : WordTrace (prefixWord ++ tailWord_5900596) baseStart_5900596 baseEnd_5900596 := by
    simpa [prefixWord, tailWord_5900596, baseEnd_5900596] using wordTrace_append hprefix tailTrace_5900596
  have hstable : (prefixWord ++ tailWord_5900596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900596).length < 2 ^ (prefixWord ++ tailWord_5900596).sum := by decide
  have hdescent : baseEnd_5900596 < baseStart_5900596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900599 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_5900599 : Nat := 118140960795 + 5900599 * 2 ^ 59
def prefixEnd_5900599 : Nat := 4983230072969 + 3 ^ 40 * 5900599 * 2
def baseEnd_5900599 : Nat := 3029843436439064612976145

theorem tailTrace_5900599 : CollatzResearch.WordTrace tailWord_5900599 prefixEnd_5900599 3029843436439064612976145 := by
  unfold tailWord_5900599
  simp only [CollatzResearch.WordTrace]
  refine ⟨215212525950145039923864851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143475017300096693282576567 215212525950145039923864851)
  ·
    refine ⟨322818788925217559885797277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215212525950145039923864851 322818788925217559885797277)
    ·
      refine ⟨121057045846956584957173979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322818788925217559885797277 121057045846956584957173979)
      ·
        refine ⟨181585568770434877435760969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121057045846956584957173979 181585568770434877435760969)
        ·
          refine ⟨136189176577826158076820727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181585568770434877435760969 136189176577826158076820727)
          ·
            refine ⟨204283764866739237115231091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136189176577826158076820727 204283764866739237115231091)
            ·
              refine ⟨306425647300108855672846637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204283764866739237115231091 306425647300108855672846637)
              ·
                refine ⟨114909617737540820877317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306425647300108855672846637 114909617737540820877317489)
                ·
                  refine ⟨86182213303155615657988117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114909617737540820877317489 86182213303155615657988117)
                  ·
                    refine ⟨4039791248585419483968193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86182213303155615657988117 4039791248585419483968193)
                    ·
                      refine ⟨3029843436439064612976145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039791248585419483968193 3029843436439064612976145)
                      ·
                        rfl

theorem cell23_5900599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_5900599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900599 prefixEnd_5900599 := by exact prefixLift 5900599
  have htrace : WordTrace (prefixWord ++ tailWord_5900599) baseStart_5900599 baseEnd_5900599 := by
    simpa [prefixWord, tailWord_5900599, baseEnd_5900599] using wordTrace_append hprefix tailTrace_5900599
  have hstable : (prefixWord ++ tailWord_5900599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900599).length < 2 ^ (prefixWord ++ tailWord_5900599).sum := by decide
  have hdescent : baseEnd_5900599 < baseStart_5900599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900626 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_5900626 : Nat := 118140960795 + 5900626 * 2 ^ 59
def prefixEnd_5900626 : Nat := 4983230072969 + 3 ^ 40 * 5900626 * 2
def baseEnd_5900626 : Nat := 1009952433472245335779507

theorem tailTrace_5900626 : CollatzResearch.WordTrace tailWord_5900626 prefixEnd_5900626 1009952433472245335779507 := by
  unfold tailWord_5900626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53803377680261805883774433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143475673814031482356731821 53803377680261805883774433)
  ·
    refine ⟨40352533260196354412830825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53803377680261805883774433 40352533260196354412830825)
    ·
      refine ⟨30264399945147265809623119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40352533260196354412830825 30264399945147265809623119)
      ·
        refine ⟨45396599917720898714434679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30264399945147265809623119 45396599917720898714434679)
        ·
          refine ⟨68094899876581348071652019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45396599917720898714434679 68094899876581348071652019)
          ·
            refine ⟨102142349814872022107478029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68094899876581348071652019 102142349814872022107478029)
            ·
              refine ⟨38303381180577008290304261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102142349814872022107478029 38303381180577008290304261)
              ·
                refine ⟨7181883971358189054432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38303381180577008290304261 7181883971358189054432049)
                ·
                  refine ⟨5386412978518641790824037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181883971358189054432049 5386412978518641790824037)
                  ·
                    refine ⟨1009952433472245335779507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386412978518641790824037 1009952433472245335779507)
                    ·
                      rfl

theorem cell23_5900626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_5900626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900626 prefixEnd_5900626 := by exact prefixLift 5900626
  have htrace : WordTrace (prefixWord ++ tailWord_5900626) baseStart_5900626 baseEnd_5900626 := by
    simpa [prefixWord, tailWord_5900626, baseEnd_5900626] using wordTrace_append hprefix tailTrace_5900626
  have hstable : (prefixWord ++ tailWord_5900626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900626).length < 2 ^ (prefixWord ++ tailWord_5900626).sum := by decide
  have hdescent : baseEnd_5900626 < baseStart_5900626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900632 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_5900632 : Nat := 118140960795 + 5900632 * 2 ^ 59
def prefixEnd_5900632 : Nat := 4983230072969 + 3 ^ 40 * 5900632 * 2
def baseEnd_5900632 : Nat := 3029860381300662983863493

theorem tailTrace_5900632 : CollatzResearch.WordTrace tailWord_5900632 prefixEnd_5900632 3029860381300662983863493 := by
  unfold tailWord_5900632
  simp only [CollatzResearch.WordTrace]
  refine ⟨107606864779512743279908075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143475819706016991039877433 107606864779512743279908075)
  ·
    refine ⟨161410297169269114919862113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107606864779512743279908075 161410297169269114919862113)
    ·
      refine ⟨121057722876951836189896585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161410297169269114919862113 121057722876951836189896585)
      ·
        refine ⟨90793292157713877142422439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121057722876951836189896585 90793292157713877142422439)
        ·
          refine ⟨136189938236570815713633659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90793292157713877142422439 136189938236570815713633659)
          ·
            refine ⟨204284907354856223570450489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136189938236570815713633659 204284907354856223570450489)
            ·
              refine ⟨153213680516142167677837867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204284907354856223570450489 153213680516142167677837867)
              ·
                refine ⟨229820520774213251516756801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153213680516142167677837867 229820520774213251516756801)
                ·
                  refine ⟨172365390580659938637567601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229820520774213251516756801 172365390580659938637567601)
                  ·
                    refine ⟨129274042935494953978175701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172365390580659938637567601 129274042935494953978175701)
                    ·
                      refine ⟨3029860381300662983863493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129274042935494953978175701 3029860381300662983863493)
                      ·
                        rfl

theorem cell23_5900632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_5900632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900632 prefixEnd_5900632 := by exact prefixLift 5900632
  have htrace : WordTrace (prefixWord ++ tailWord_5900632) baseStart_5900632 baseEnd_5900632 := by
    simpa [prefixWord, tailWord_5900632, baseEnd_5900632] using wordTrace_append hprefix tailTrace_5900632
  have hstable : (prefixWord ++ tailWord_5900632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900632).length < 2 ^ (prefixWord ++ tailWord_5900632).sum := by decide
  have hdescent : baseEnd_5900632 < baseStart_5900632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900650 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5900650 : Nat := 118140960795 + 5900650 * 2 ^ 59
def prefixEnd_5900650 : Nat := 4983230072969 + 3 ^ 40 * 5900650 * 2
def baseEnd_5900650 : Nat := 3029869623952443913438411

theorem tailTrace_5900650 : CollatzResearch.WordTrace tailWord_5900650 prefixEnd_5900650 3029869623952443913438411 := by
  unfold tailWord_5900650
  simp only [CollatzResearch.WordTrace]
  refine ⟨53803596518240068908492851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143476257381973517089314269 53803596518240068908492851)
  ·
    refine ⟨80705394777360103362739277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53803596518240068908492851 80705394777360103362739277)
    ·
      refine ⟨30264523041510038761027229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80705394777360103362739277 30264523041510038761027229)
      ·
        refine ⟨11349196140566264535385211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30264523041510038761027229 11349196140566264535385211)
        ·
          refine ⟨17023794210849396803077817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11349196140566264535385211 17023794210849396803077817)
          ·
            refine ⟨12767845658137047602308363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023794210849396803077817 12767845658137047602308363)
            ·
              refine ⟨19151768487205571403462545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767845658137047602308363 19151768487205571403462545)
              ·
                refine ⟨14363826365404178552596909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19151768487205571403462545 14363826365404178552596909)
                ·
                  refine ⟨5386434887026566957223841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14363826365404178552596909 5386434887026566957223841)
                  ·
                    refine ⟨4039826165269925217917881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386434887026566957223841 4039826165269925217917881)
                    ·
                      refine ⟨3029869623952443913438411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039826165269925217917881 3029869623952443913438411)
                      ·
                        rfl

theorem cell23_5900650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5900650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900650 prefixEnd_5900650 := by exact prefixLift 5900650
  have htrace : WordTrace (prefixWord ++ tailWord_5900650) baseStart_5900650 baseEnd_5900650 := by
    simpa [prefixWord, tailWord_5900650, baseEnd_5900650] using wordTrace_append hprefix tailTrace_5900650
  have hstable : (prefixWord ++ tailWord_5900650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900650).length < 2 ^ (prefixWord ++ tailWord_5900650).sum := by decide
  have hdescent : baseEnd_5900650 < baseStart_5900650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900683 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 3]
def baseStart_5900683 : Nat := 118140960795 + 5900683 * 2 ^ 59
def prefixEnd_5900683 : Nat := 4983230072969 + 3 ^ 40 * 5900683 * 2
def baseEnd_5900683 : Nat := 3029886568814042284325759

theorem tailTrace_5900683 : CollatzResearch.WordTrace tailWord_5900683 prefixEnd_5900683 3029886568814042284325759 := by
  unfold tailWord_5900683
  simp only [CollatzResearch.WordTrace]
  refine ⟨215215589681840722269922703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143477059787893814846615135 215215589681840722269922703)
  ·
    refine ⟨322823384522761083404884055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215215589681840722269922703 322823384522761083404884055)
    ·
      refine ⟨484235076784141625107326083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322823384522761083404884055 484235076784141625107326083)
      ·
        refine ⟨726352615176212437660989125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484235076784141625107326083 726352615176212437660989125)
        ·
          refine ⟨136191115345539832061435461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 726352615176212437660989125 136191115345539832061435461)
          ·
            refine ⟨25535834127288718511519149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136191115345539832061435461 25535834127288718511519149)
            ·
              refine ⟨9575937797733269441819681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25535834127288718511519149 9575937797733269441819681)
              ·
                refine ⟨7181953348299952081364761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9575937797733269441819681 7181953348299952081364761)
                ·
                  refine ⟨5386465011224964061023571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181953348299952081364761 5386465011224964061023571)
                  ·
                    refine ⟨8079697516837446091535357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386465011224964061023571 8079697516837446091535357)
                    ·
                      refine ⟨3029886568814042284325759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8079697516837446091535357 3029886568814042284325759)
                      ·
                        rfl

theorem cell23_5900683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 3].length) (baseStart_5900683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900683 prefixEnd_5900683 := by exact prefixLift 5900683
  have htrace : WordTrace (prefixWord ++ tailWord_5900683) baseStart_5900683 baseEnd_5900683 := by
    simpa [prefixWord, tailWord_5900683, baseEnd_5900683] using wordTrace_append hprefix tailTrace_5900683
  have hstable : (prefixWord ++ tailWord_5900683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900683).length < 2 ^ (prefixWord ++ tailWord_5900683).sum := by decide
  have hdescent : baseEnd_5900683 < baseStart_5900683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900694 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5900694 : Nat := 118140960795 + 5900694 * 2 ^ 59
def prefixEnd_5900694 : Nat := 4983230072969 + 3 ^ 40 * 5900694 * 2
def baseEnd_5900694 : Nat := 1009964072367080580429403

theorem tailTrace_5900694 : CollatzResearch.WordTrace tailWord_5900694 prefixEnd_5900694 1009964072367080580429403 := by
  unfold tailWord_5900694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450999430300054446785821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143477327256533914099048757 13450999430300054446785821)
  ·
    refine ⟨5044124786362520417544683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13450999430300054446785821 5044124786362520417544683)
    ·
      refine ⟨7566187179543780626317025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5044124786362520417544683 7566187179543780626317025)
      ·
        refine ⟨5674640384657835469737769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7566187179543780626317025 5674640384657835469737769)
        ·
          refine ⟨4255980288493376602303327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5674640384657835469737769 4255980288493376602303327)
          ·
            refine ⟨6383970432740064903454991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255980288493376602303327 6383970432740064903454991)
            ·
              refine ⟨9575955649110097355182487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383970432740064903454991 9575955649110097355182487)
              ·
                refine ⟨14363933473665146032773731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9575955649110097355182487 14363933473665146032773731)
                ·
                  refine ⟨21545900210497719049160597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14363933473665146032773731 21545900210497719049160597)
                  ·
                    refine ⟨1009964072367080580429403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21545900210497719049160597 1009964072367080580429403)
                    ·
                      rfl

theorem cell23_5900694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5900694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900694 prefixEnd_5900694 := by exact prefixLift 5900694
  have htrace : WordTrace (prefixWord ++ tailWord_5900694) baseStart_5900694 baseEnd_5900694 := by
    simpa [prefixWord, tailWord_5900694, baseEnd_5900694] using wordTrace_append hprefix tailTrace_5900694
  have hstable : (prefixWord ++ tailWord_5900694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900694).length < 2 ^ (prefixWord ++ tailWord_5900694).sum := by decide
  have hdescent : baseEnd_5900694 < baseStart_5900694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900709 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_5900709 : Nat := 118140960795 + 5900709 * 2 ^ 59
def prefixEnd_5900709 : Nat := 4983230072969 + 3 ^ 40 * 5900709 * 2
def baseEnd_5900709 : Nat := 3029899919311059182600639

theorem tailTrace_5900709 : CollatzResearch.WordTrace tailWord_5900709 prefixEnd_5900709 3029899919311059182600639 := by
  unfold tailWord_5900709
  simp only [CollatzResearch.WordTrace]
  refine ⟨215216537979746528710369181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143477691986497685806912787 215216537979746528710369181)
  ·
    refine ⟨80706201742404948266388443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215216537979746528710369181 80706201742404948266388443)
    ·
      refine ⟨121059302613607422399582665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80706201742404948266388443 121059302613607422399582665)
      ·
        refine ⟨90794476960205566799686999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121059302613607422399582665 90794476960205566799686999)
        ·
          refine ⟨136191715440308350199530499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90794476960205566799686999 136191715440308350199530499)
          ·
            refine ⟨204287573160462525299295749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136191715440308350199530499 204287573160462525299295749)
            ·
              refine ⟨38303919967586723493617953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204287573160462525299295749 38303919967586723493617953)
              ·
                refine ⟨28727939975690042620213465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38303919967586723493617953 28727939975690042620213465)
                ·
                  refine ⟨21545954981767531965160099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28727939975690042620213465 21545954981767531965160099)
                  ·
                    refine ⟨32318932472651297947740149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21545954981767531965160099 32318932472651297947740149)
                    ·
                      refine ⟨3029899919311059182600639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32318932472651297947740149 3029899919311059182600639)
                      ·
                        rfl

theorem cell23_5900709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_5900709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900709 prefixEnd_5900709 := by exact prefixLift 5900709
  have htrace : WordTrace (prefixWord ++ tailWord_5900709) baseStart_5900709 baseEnd_5900709 := by
    simpa [prefixWord, tailWord_5900709, baseEnd_5900709] using wordTrace_append hprefix tailTrace_5900709
  have hstable : (prefixWord ++ tailWord_5900709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900709).length < 2 ^ (prefixWord ++ tailWord_5900709).sum := by decide
  have hdescent : baseEnd_5900709 < baseStart_5900709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900757 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5900757 : Nat := 118140960795 + 5900757 * 2 ^ 59
def prefixEnd_5900757 : Nat := 4983230072969 + 3 ^ 40 * 5900757 * 2
def baseEnd_5900757 : Nat := 3029924566382474994800419

theorem tailTrace_5900757 : CollatzResearch.WordTrace tailWord_5900757 prefixEnd_5900757 3029924566382474994800419 := by
  unfold tailWord_5900757
  simp only [CollatzResearch.WordTrace]
  refine ⟨215218288683572632908116525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143478859122381755272077683 215218288683572632908116525)
  ·
    refine ⟨80706858256339737340543697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215218288683572632908116525 80706858256339737340543697)
    ·
      refine ⟨60530143692254803005407773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80706858256339737340543697 60530143692254803005407773)
      ·
        refine ⟨22698803884595551127027915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60530143692254803005407773 22698803884595551127027915)
        ·
          refine ⟨34048205826893326690541873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22698803884595551127027915 34048205826893326690541873)
          ·
            refine ⟨25536154370169995017906405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34048205826893326690541873 25536154370169995017906405)
            ·
              refine ⟨4788028944406874065857451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25536154370169995017906405 4788028944406874065857451)
              ·
                refine ⟨7182043416610311098786177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788028944406874065857451 7182043416610311098786177)
                ·
                  refine ⟨5386532562457733324089633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182043416610311098786177 5386532562457733324089633)
                  ·
                    refine ⟨4039899421843299993067225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386532562457733324089633 4039899421843299993067225)
                    ·
                      refine ⟨3029924566382474994800419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4039899421843299993067225 3029924566382474994800419)
                      ·
                        rfl

theorem cell23_5900757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5900757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900757 prefixEnd_5900757 := by exact prefixLift 5900757
  have htrace : WordTrace (prefixWord ++ tailWord_5900757) baseStart_5900757 baseEnd_5900757 := by
    simpa [prefixWord, tailWord_5900757, baseEnd_5900757] using wordTrace_append hprefix tailTrace_5900757
  have hstable : (prefixWord ++ tailWord_5900757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900757).length < 2 ^ (prefixWord ++ tailWord_5900757).sum := by decide
  have hdescent : baseEnd_5900757 < baseStart_5900757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900769 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5900769 : Nat := 118140960795 + 5900769 * 2 ^ 59
def prefixEnd_5900769 : Nat := 4983230072969 + 3 ^ 40 * 5900769 * 2
def baseEnd_5900769 : Nat := 3029930728150328947850363

theorem tailTrace_5900769 : CollatzResearch.WordTrace tailWord_5900769 prefixEnd_5900769 3029930728150328947850363 := by
  unfold tailWord_5900769
  simp only [CollatzResearch.WordTrace]
  refine ⟨215218726359529158957553361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143479150906352772638368907 215218726359529158957553361)
  ·
    refine ⟨161414044769646869218165021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215218726359529158957553361 161414044769646869218165021)
    ·
      refine ⟨60530266788617575956811883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161414044769646869218165021 60530266788617575956811883)
      ·
        refine ⟨90795400182926363935217825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60530266788617575956811883 90795400182926363935217825)
        ·
          refine ⟨68096550137194772951413369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90795400182926363935217825 68096550137194772951413369)
          ·
            refine ⟨51072412602896079713560027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68096550137194772951413369 51072412602896079713560027)
            ·
              refine ⟨76608618904344119570340041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51072412602896079713560027 76608618904344119570340041)
              ·
                refine ⟨57456464178258089677755031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76608618904344119570340041 57456464178258089677755031)
                ·
                  refine ⟨86184696267387134516632547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57456464178258089677755031 86184696267387134516632547)
                  ·
                    refine ⟨129277044401080701774948821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86184696267387134516632547 129277044401080701774948821)
                    ·
                      refine ⟨3029930728150328947850363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129277044401080701774948821 3029930728150328947850363)
                      ·
                        rfl

theorem cell23_5900769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5900769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900769 prefixEnd_5900769 := by exact prefixLift 5900769
  have htrace : WordTrace (prefixWord ++ tailWord_5900769) baseStart_5900769 baseEnd_5900769 := by
    simpa [prefixWord, tailWord_5900769, baseEnd_5900769] using wordTrace_append hprefix tailTrace_5900769
  have hstable : (prefixWord ++ tailWord_5900769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900769).length < 2 ^ (prefixWord ++ tailWord_5900769).sum := by decide
  have hdescent : baseEnd_5900769 < baseStart_5900769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900776 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5900776 : Nat := 118140960795 + 5900776 * 2 ^ 59
def prefixEnd_5900776 : Nat := 4983230072969 + 3 ^ 40 * 5900776 * 2
def baseEnd_5900776 : Nat := 1009978107504970140154277

theorem tailTrace_5900776 : CollatzResearch.WordTrace tailWord_5900776 prefixEnd_5900776 1009978107504970140154277 := by
  unfold tailWord_5900776
  simp only [CollatzResearch.WordTrace]
  refine ⟨107609490835251899576529091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143479321113669199435372121 107609490835251899576529091)
  ·
    refine ⟨161414236252877849364793637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107609490835251899576529091 161414236252877849364793637)
    ·
      refine ⟨30265169297414596755898807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161414236252877849364793637 30265169297414596755898807)
      ·
        refine ⟨45397753946121895133848211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30265169297414596755898807 45397753946121895133848211)
        ·
          refine ⟨68096630919182842700772317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45397753946121895133848211 68096630919182842700772317)
          ·
            refine ⟨25536236594693566012789619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68096630919182842700772317 25536236594693566012789619)
            ·
              refine ⟨38304354892040349019184429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25536236594693566012789619 38304354892040349019184429)
              ·
                refine ⟨14364133084515130882194161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38304354892040349019184429 14364133084515130882194161)
                ·
                  refine ⟨10773099813386348161645621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14364133084515130882194161 10773099813386348161645621)
                  ·
                    refine ⟨1009978107504970140154277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10773099813386348161645621 1009978107504970140154277)
                    ·
                      rfl

theorem cell23_5900776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5900776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900776 prefixEnd_5900776 := by exact prefixLift 5900776
  have htrace : WordTrace (prefixWord ++ tailWord_5900776) baseStart_5900776 baseEnd_5900776 := by
    simpa [prefixWord, tailWord_5900776, baseEnd_5900776] using wordTrace_append hprefix tailTrace_5900776
  have hstable : (prefixWord ++ tailWord_5900776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900776).length < 2 ^ (prefixWord ++ tailWord_5900776).sum := by decide
  have hdescent : baseEnd_5900776 < baseStart_5900776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900799 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_5900799 : Nat := 118140960795 + 5900799 * 2 ^ 59
def prefixEnd_5900799 : Nat := 4983230072969 + 3 ^ 40 * 5900799 * 2
def baseEnd_5900799 : Nat := 3029946132569963830475225

theorem tailTrace_5900799 : CollatzResearch.WordTrace tailWord_5900799 prefixEnd_5900799 3029946132569963830475225 := by
  unfold tailWord_5900799
  simp only [CollatzResearch.WordTrace]
  refine ⟨215219820549420474081145451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143479880366280316054096967 215219820549420474081145451)
  ·
    refine ⟨322829730824130711121718177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215219820549420474081145451 322829730824130711121718177)
    ·
      refine ⟨242122298118098033341288633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322829730824130711121718177 242122298118098033341288633)
      ·
        refine ⟨181591723588573525005966475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242122298118098033341288633 181591723588573525005966475)
        ·
          refine ⟨272387585382860287508949713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181591723588573525005966475 272387585382860287508949713)
          ·
            refine ⟨204290689037145215631712285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272387585382860287508949713 204290689037145215631712285)
            ·
              refine ⟨76609008388929455861892107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204290689037145215631712285 76609008388929455861892107)
              ·
                refine ⟨114913512583394183792838161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76609008388929455861892107 114913512583394183792838161)
                ·
                  refine ⟨86185134437545637844628621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114913512583394183792838161 86185134437545637844628621)
                  ·
                    refine ⟨32319425414079614191735733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86185134437545637844628621 32319425414079614191735733)
                    ·
                      refine ⟨3029946132569963830475225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32319425414079614191735733 3029946132569963830475225)
                      ·
                        rfl

theorem cell23_5900799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_5900799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900799 prefixEnd_5900799 := by exact prefixLift 5900799
  have htrace : WordTrace (prefixWord ++ tailWord_5900799) baseStart_5900799 baseEnd_5900799 := by
    simpa [prefixWord, tailWord_5900799, baseEnd_5900799] using wordTrace_append hprefix tailTrace_5900799
  have hstable : (prefixWord ++ tailWord_5900799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900799).length < 2 ^ (prefixWord ++ tailWord_5900799).sum := by decide
  have hdescent : baseEnd_5900799 < baseStart_5900799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900809 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_5900809 : Nat := 118140960795 + 5900809 * 2 ^ 59
def prefixEnd_5900809 : Nat := 4983230072969 + 3 ^ 40 * 5900809 * 2
def baseEnd_5900809 : Nat := 3029951267376508791350179

theorem tailTrace_5900809 : CollatzResearch.WordTrace tailWord_5900809 prefixEnd_5900809 3029951267376508791350179 := by
  unfold tailWord_5900809
  simp only [CollatzResearch.WordTrace]
  refine ⟨215220185279384245789009481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143480123519589497192672987 215220185279384245789009481)
  ·
    refine ⟨161415138959538184341757111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215220185279384245789009481 161415138959538184341757111)
    ·
      refine ⟨242122708439307276512635667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161415138959538184341757111 242122708439307276512635667)
      ·
        refine ⟨363184062658960914768953501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242122708439307276512635667 363184062658960914768953501)
        ·
          refine ⟨136194023497110343038357563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363184062658960914768953501 136194023497110343038357563)
          ·
            refine ⟨204291035245665514557536345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136194023497110343038357563 204291035245665514557536345)
            ·
              refine ⟨153218276434249135918152259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204291035245665514557536345 153218276434249135918152259)
              ·
                refine ⟨229827414651373703877228389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153218276434249135918152259 229827414651373703877228389)
                ·
                  refine ⟨43092640247132569476980323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229827414651373703877228389 43092640247132569476980323)
                  ·
                    refine ⟨64638960370698854215470485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43092640247132569476980323 64638960370698854215470485)
                    ·
                      refine ⟨3029951267376508791350179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64638960370698854215470485 3029951267376508791350179)
                      ·
                        rfl

theorem cell23_5900809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_5900809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900809 prefixEnd_5900809 := by exact prefixLift 5900809
  have htrace : WordTrace (prefixWord ++ tailWord_5900809) baseStart_5900809 baseEnd_5900809 := by
    simpa [prefixWord, tailWord_5900809, baseEnd_5900809] using wordTrace_append hprefix tailTrace_5900809
  have hstable : (prefixWord ++ tailWord_5900809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900809).length < 2 ^ (prefixWord ++ tailWord_5900809).sum := by decide
  have hdescent : baseEnd_5900809 < baseStart_5900809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_5900859 : Nat := 118140960795 + 5900859 * 2 ^ 59
def prefixEnd_5900859 : Nat := 4983230072969 + 3 ^ 40 * 5900859 * 2
def baseEnd_5900859 : Nat := 3029976941409233595724949

theorem tailTrace_5900859 : CollatzResearch.WordTrace tailWord_5900859 prefixEnd_5900859 3029976941409233595724949 := by
  unfold tailWord_5900859
  simp only [CollatzResearch.WordTrace]
  refine ⟨215222008929203104328329631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143481339286135402885553087 215222008929203104328329631)
  ·
    refine ⟨322833013393804656492494447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215222008929203104328329631 322833013393804656492494447)
    ·
      refine ⟨484249520090706984738741671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322833013393804656492494447 484249520090706984738741671)
      ·
        refine ⟨726374280136060477108112507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484249520090706984738741671 726374280136060477108112507)
        ·
          refine ⟨1089561420204090715662168761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726374280136060477108112507 1089561420204090715662168761)
          ·
            refine ⟨817171065153068036746626571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089561420204090715662168761 817171065153068036746626571)
            ·
              refine ⟨1225756597729602055119939857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817171065153068036746626571 1225756597729602055119939857)
              ·
                refine ⟨919317448297201541339954893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225756597729602055119939857 919317448297201541339954893)
                ·
                  refine ⟨344744043111450578002483085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919317448297201541339954893 344744043111450578002483085)
                  ·
                    refine ⟨129279016166793966750931157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344744043111450578002483085 129279016166793966750931157)
                    ·
                      refine ⟨3029976941409233595724949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129279016166793966750931157 3029976941409233595724949)
                      ·
                        rfl

theorem cell23_5900859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_5900859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900859 prefixEnd_5900859 := by exact prefixLift 5900859
  have htrace : WordTrace (prefixWord ++ tailWord_5900859) baseStart_5900859 baseEnd_5900859 := by
    simpa [prefixWord, tailWord_5900859, baseEnd_5900859] using wordTrace_append hprefix tailTrace_5900859
  have hstable : (prefixWord ++ tailWord_5900859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900859).length < 2 ^ (prefixWord ++ tailWord_5900859).sum := by decide
  have hdescent : baseEnd_5900859 < baseStart_5900859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900896 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_5900896 : Nat := 118140960795 + 5900896 * 2 ^ 59
def prefixEnd_5900896 : Nat := 4983230072969 + 3 ^ 40 * 5900896 * 2
def baseEnd_5900896 : Nat := 1009998646731149983654093

theorem tailTrace_5900896 : CollatzResearch.WordTrace tailWord_5900896 prefixEnd_5900896 1009998646731149983654093 := by
  unfold tailWord_5900896
  simp only [CollatzResearch.WordTrace]
  refine ⟨107611679215034529823713271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143482238953379373098284361 107611679215034529823713271)
  ·
    refine ⟨161417518822551794735569907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107611679215034529823713271 161417518822551794735569907)
    ·
      refine ⟨242126278233827692103354861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161417518822551794735569907 242126278233827692103354861)
      ·
        refine ⟨90797354337685384538758073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242126278233827692103354861 90797354337685384538758073)
        ·
          refine ⟨68098015753264038404068555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90797354337685384538758073 68098015753264038404068555)
          ·
            refine ⟨102147023629896057606102833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68098015753264038404068555 102147023629896057606102833)
            ·
              refine ⟨76610267722422043204577125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102147023629896057606102833 76610267722422043204577125)
              ·
                refine ⟨14364425197954133100858211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76610267722422043204577125 14364425197954133100858211)
                ·
                  refine ⟨21546637796931199651287317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14364425197954133100858211 21546637796931199651287317)
                  ·
                    refine ⟨1009998646731149983654093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21546637796931199651287317 1009998646731149983654093)
                    ·
                      rfl

theorem cell23_5900896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_5900896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900896 prefixEnd_5900896 := by exact prefixLift 5900896
  have htrace : WordTrace (prefixWord ++ tailWord_5900896) baseStart_5900896 baseEnd_5900896 := by
    simpa [prefixWord, tailWord_5900896, baseEnd_5900896] using wordTrace_append hprefix tailTrace_5900896
  have hstable : (prefixWord ++ tailWord_5900896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900896).length < 2 ^ (prefixWord ++ tailWord_5900896).sum := by decide
  have hdescent : baseEnd_5900896 < baseStart_5900896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900897 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_5900897 : Nat := 118140960795 + 5900897 * 2 ^ 59
def prefixEnd_5900897 : Nat := 4983230072969 + 3 ^ 40 * 5900897 * 2
def baseEnd_5900897 : Nat := 3029996453674104447049775

theorem tailTrace_5900897 : CollatzResearch.WordTrace tailWord_5900897 prefixEnd_5900897 3029996453674104447049775 := by
  unfold tailWord_5900897
  simp only [CollatzResearch.WordTrace]
  refine ⟨215223394903065436818212945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143482263268710291212141963 215223394903065436818212945)
  ·
    refine ⟨161417546177299077613659709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215223394903065436818212945 161417546177299077613659709)
    ·
      refine ⟨60531579816487154105122391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161417546177299077613659709 60531579816487154105122391)
      ·
        refine ⟨90797369724730731157683587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60531579816487154105122391 90797369724730731157683587)
        ·
          refine ⟨136196054587096096736525381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90797369724730731157683587 136196054587096096736525381)
          ·
            refine ⟨25536760235080518138098509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136196054587096096736525381 25536760235080518138098509)
            ·
              refine ⟨9576285088155194301786941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25536760235080518138098509 9576285088155194301786941)
              ·
                refine ⟨3591106908058197863170103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9576285088155194301786941 3591106908058197863170103)
                ·
                  refine ⟨5386660362087296794755155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591106908058197863170103 5386660362087296794755155)
                  ·
                    refine ⟨8079990543130945192132733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386660362087296794755155 8079990543130945192132733)
                    ·
                      refine ⟨3029996453674104447049775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8079990543130945192132733 3029996453674104447049775)
                      ·
                        rfl

theorem cell23_5900897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_5900897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900897 prefixEnd_5900897 := by exact prefixLift 5900897
  have htrace : WordTrace (prefixWord ++ tailWord_5900897) baseStart_5900897 baseEnd_5900897 := by
    simpa [prefixWord, tailWord_5900897, baseEnd_5900897] using wordTrace_append hprefix tailTrace_5900897
  have hstable : (prefixWord ++ tailWord_5900897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900897).length < 2 ^ (prefixWord ++ tailWord_5900897).sum := by decide
  have hdescent : baseEnd_5900897 < baseStart_5900897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900914 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_5900914 : Nat := 118140960795 + 5900914 * 2 ^ 59
def prefixEnd_5900914 : Nat := 4983230072969 + 3 ^ 40 * 5900914 * 2
def baseEnd_5900914 : Nat := 3030005182845230880537197

theorem tailTrace_5900914 : CollatzResearch.WordTrace tailWord_5900914 prefixEnd_5900914 3030005182845230880537197 := by
  unfold tailWord_5900914
  simp only [CollatzResearch.WordTrace]
  refine ⟨53806003736000962180395449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143482676629335899147721197 53806003736000962180395449)
  ·
    refine ⟨40354502802000721635296587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53806003736000962180395449 40354502802000721635296587)
    ·
      refine ⟨60531754203001082452944881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40354502802000721635296587 60531754203001082452944881)
      ·
        refine ⟨45398815652250811839708661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60531754203001082452944881 45398815652250811839708661)
        ·
          refine ⟨4256138967398513609972687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45398815652250811839708661 4256138967398513609972687)
          ·
            refine ⟨6384208451097770414959031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256138967398513609972687 6384208451097770414959031)
            ·
              refine ⟨9576312676646655622438547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384208451097770414959031 9576312676646655622438547)
              ·
                refine ⟨14364469014969983433657821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9576312676646655622438547 14364469014969983433657821)
                ·
                  refine ⟨5386675880613743787621683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14364469014969983433657821 5386675880613743787621683)
                  ·
                    refine ⟨8080013820920615681432525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386675880613743787621683 8080013820920615681432525)
                    ·
                      refine ⟨3030005182845230880537197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8080013820920615681432525 3030005182845230880537197)
                      ·
                        rfl

theorem cell23_5900914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_5900914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900914 prefixEnd_5900914 := by exact prefixLift 5900914
  have htrace : WordTrace (prefixWord ++ tailWord_5900914) baseStart_5900914 baseEnd_5900914 := by
    simpa [prefixWord, tailWord_5900914, baseEnd_5900914] using wordTrace_append hprefix tailTrace_5900914
  have hstable : (prefixWord ++ tailWord_5900914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900914).length < 2 ^ (prefixWord ++ tailWord_5900914).sum := by decide
  have hdescent : baseEnd_5900914 < baseStart_5900914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900953 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_5900953 : Nat := 118140960795 + 5900953 * 2 ^ 59
def prefixEnd_5900953 : Nat := 4983230072969 + 3 ^ 40 * 5900953 * 2
def baseEnd_5900953 : Nat := 3030025208590756227949517

theorem tailTrace_5900953 : CollatzResearch.WordTrace tailWord_5900953 prefixEnd_5900953 3030025208590756227949517 := by
  unfold tailWord_5900953
  simp only [CollatzResearch.WordTrace]
  refine ⟨215225437390862558382251513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143483624927241705588167675 215225437390862558382251513)
  ·
    refine ⟨161419078043146918786688635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215225437390862558382251513 161419078043146918786688635)
    ·
      refine ⟨242128617064720378180032953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161419078043146918786688635 242128617064720378180032953)
      ·
        refine ⟨181596462798540283635024715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242128617064720378180032953 181596462798540283635024715)
        ·
          refine ⟨272394694197810425452537073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181596462798540283635024715 272394694197810425452537073)
          ·
            refine ⟨204296020648357819089402805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272394694197810425452537073 204296020648357819089402805)
            ·
              refine ⟨19152751935783545539631513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204296020648357819089402805 19152751935783545539631513)
              ·
                refine ⟨14364563951837659154723635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19152751935783545539631513 14364563951837659154723635)
                ·
                  refine ⟨21546845927756488732085453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14364563951837659154723635 21546845927756488732085453)
                  ·
                    refine ⟨8080067222908683274532045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21546845927756488732085453 8080067222908683274532045)
                    ·
                      refine ⟨3030025208590756227949517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8080067222908683274532045 3030025208590756227949517)
                      ·
                        rfl

theorem cell23_5900953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_5900953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900953 prefixEnd_5900953 := by exact prefixLift 5900953
  have htrace : WordTrace (prefixWord ++ tailWord_5900953) baseStart_5900953 baseEnd_5900953 := by
    simpa [prefixWord, tailWord_5900953, baseEnd_5900953] using wordTrace_append hprefix tailTrace_5900953
  have hstable : (prefixWord ++ tailWord_5900953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900953).length < 2 ^ (prefixWord ++ tailWord_5900953).sum := by decide
  have hdescent : baseEnd_5900953 < baseStart_5900953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900954 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5900954 : Nat := 118140960795 + 5900954 * 2 ^ 59
def prefixEnd_5900954 : Nat := 4983230072969 + 3 ^ 40 * 5900954 * 2
def baseEnd_5900954 : Nat := 3030025722071410724037013

theorem tailTrace_5900954 : CollatzResearch.WordTrace tailWord_5900954 prefixEnd_5900954 3030025722071410724037013 := by
  unfold tailWord_5900954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53806368465964733888259479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143483649242572623702025277 53806368465964733888259479)
  ·
    refine ⟨80709552698947100832389219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53806368465964733888259479 80709552698947100832389219)
    ·
      refine ⟨121064329048420651248583829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80709552698947100832389219 121064329048420651248583829)
      ·
        refine ⟨5674890424144718027277367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121064329048420651248583829 5674890424144718027277367)
        ·
          refine ⟨8512335636217077040916051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674890424144718027277367 8512335636217077040916051)
          ·
            refine ⟨12768503454325615561374077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8512335636217077040916051 12768503454325615561374077)
            ·
              refine ⟨4788188795372105835515279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12768503454325615561374077 4788188795372105835515279)
              ·
                refine ⟨7182283193058158753272919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788188795372105835515279 7182283193058158753272919)
                ·
                  refine ⟨10773424789587238129909379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182283193058158753272919 10773424789587238129909379)
                  ·
                    refine ⟨16160137184380857194864069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10773424789587238129909379 16160137184380857194864069)
                    ·
                      refine ⟨3030025722071410724037013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16160137184380857194864069 3030025722071410724037013)
                      ·
                        rfl

theorem cell23_5900954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5900954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900954 prefixEnd_5900954 := by exact prefixLift 5900954
  have htrace : WordTrace (prefixWord ++ tailWord_5900954) baseStart_5900954 baseEnd_5900954 := by
    simpa [prefixWord, tailWord_5900954, baseEnd_5900954] using wordTrace_append hprefix tailTrace_5900954
  have hstable : (prefixWord ++ tailWord_5900954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900954).length < 2 ^ (prefixWord ++ tailWord_5900954).sum := by decide
  have hdescent : baseEnd_5900954 < baseStart_5900954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900973 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5900973 : Nat := 118140960795 + 5900973 * 2 ^ 59
def prefixEnd_5900973 : Nat := 4983230072969 + 3 ^ 40 * 5900973 * 2
def baseEnd_5900973 : Nat := 1010011826067948716566475

theorem tailTrace_5900973 : CollatzResearch.WordTrace tailWord_5900973 prefixEnd_5900973 1010011826067948716566475 := by
  unfold tailWord_5900973
  simp only [CollatzResearch.WordTrace]
  refine ⟨215226166850790101797979573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143484111233860067865319715 215226166850790101797979573)
  ·
    refine ⟨20177453142261572043560585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215226166850790101797979573 20177453142261572043560585)
    ·
      refine ⟨15133089856696179032670439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20177453142261572043560585 15133089856696179032670439)
      ·
        refine ⟨22699634785044268549005659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15133089856696179032670439 22699634785044268549005659)
        ·
          refine ⟨34049452177566402823508489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22699634785044268549005659 34049452177566402823508489)
          ·
            refine ⟨25537089133174802117631367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34049452177566402823508489 25537089133174802117631367)
            ·
              refine ⟨38305633699762203176447051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25537089133174802117631367 38305633699762203176447051)
              ·
                refine ⟨57458450549643304764670577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38305633699762203176447051 57458450549643304764670577)
                ·
                  refine ⟨43093837912232478573502933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57458450549643304764670577 43093837912232478573502933)
                  ·
                    refine ⟨1010011826067948716566475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43093837912232478573502933 1010011826067948716566475)
                    ·
                      rfl

theorem cell23_5900973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5900973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900973 prefixEnd_5900973 := by exact prefixLift 5900973
  have htrace : WordTrace (prefixWord ++ tailWord_5900973) baseStart_5900973 baseEnd_5900973 := by
    simpa [prefixWord, tailWord_5900973, baseEnd_5900973] using wordTrace_append hprefix tailTrace_5900973
  have hstable : (prefixWord ++ tailWord_5900973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900973).length < 2 ^ (prefixWord ++ tailWord_5900973).sum := by decide
  have hdescent : baseEnd_5900973 < baseStart_5900973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5900977 : List Nat := [1, 2, 2, 6, 2, 1, 1, 8]
def baseStart_5900977 : Nat := 118140960795 + 5900977 * 2 ^ 59
def prefixEnd_5900977 : Nat := 4983230072969 + 3 ^ 40 * 5900977 * 2
def baseEnd_5900977 : Nat := 112223612300980153112941

theorem tailTrace_5900977 : CollatzResearch.WordTrace tailWord_5900977 prefixEnd_5900977 112223612300980153112941 := by
  unfold tailWord_5900977
  simp only [CollatzResearch.WordTrace]
  refine ⟨215226312742775610481125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143484208495183740320750123 215226312742775610481125185)
  ·
    refine ⟨161419734557081707860843889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215226312742775610481125185 161419734557081707860843889)
    ·
      refine ⟨121064800917811280895632917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161419734557081707860843889 121064800917811280895632917)
      ·
        refine ⟨5674912543022403791982793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121064800917811280895632917 5674912543022403791982793)
        ·
          refine ⟨4256184407266802843987095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5674912543022403791982793 4256184407266802843987095)
          ·
            refine ⟨6384276610900204265980643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256184407266802843987095 6384276610900204265980643)
            ·
              refine ⟨9576414916350306398970965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384276610900204265980643 9576414916350306398970965)
              ·
                refine ⟨112223612300980153112941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9576414916350306398970965 112223612300980153112941)
                ·
                  rfl

theorem cell23_5900977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 8].length) (baseStart_5900977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5900977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5900977 prefixEnd_5900977 := by exact prefixLift 5900977
  have htrace : WordTrace (prefixWord ++ tailWord_5900977) baseStart_5900977 baseEnd_5900977 := by
    simpa [prefixWord, tailWord_5900977, baseEnd_5900977] using wordTrace_append hprefix tailTrace_5900977
  have hstable : (prefixWord ++ tailWord_5900977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5900977).length < 2 ^ (prefixWord ++ tailWord_5900977).sum := by decide
  have hdescent : baseEnd_5900977 < baseStart_5900977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5900977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901020 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5901020 : Nat := 118140960795 + 5901020 * 2 ^ 59
def prefixEnd_5901020 : Nat := 4983230072969 + 3 ^ 40 * 5901020 * 2
def baseEnd_5901020 : Nat := 1010019870598202488603903

theorem tailTrace_5901020 : CollatzResearch.WordTrace tailWord_5901020 prefixEnd_5901020 1010019870598202488603903 := by
  unfold tailWord_5901020
  simp only [CollatzResearch.WordTrace]
  refine ⟨107613940540809914412470257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143485254054413219216627009 107613940540809914412470257)
  ·
    refine ⟨80710455405607435809352693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107613940540809914412470257 80710455405607435809352693)
    ·
      refine ⟨7566605194275697107126815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80710455405607435809352693 7566605194275697107126815)
      ·
        refine ⟨11349907791413545660690223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7566605194275697107126815 11349907791413545660690223)
        ·
          refine ⟨17024861687120318491035335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11349907791413545660690223 17024861687120318491035335)
          ·
            refine ⟨25537292530680477736553003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17024861687120318491035335 25537292530680477736553003)
            ·
              refine ⟨38305938796020716604829505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25537292530680477736553003 38305938796020716604829505)
              ·
                refine ⟨28729454097015537453622129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38305938796020716604829505 28729454097015537453622129)
                ·
                  refine ⟨21547090572761653090216597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28729454097015537453622129 21547090572761653090216597)
                  ·
                    refine ⟨1010019870598202488603903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21547090572761653090216597 1010019870598202488603903)
                    ·
                      rfl

theorem cell23_5901020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5901020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901020 prefixEnd_5901020 := by exact prefixLift 5901020
  have htrace : WordTrace (prefixWord ++ tailWord_5901020) baseStart_5901020 baseEnd_5901020 := by
    simpa [prefixWord, tailWord_5901020, baseEnd_5901020] using wordTrace_append hprefix tailTrace_5901020
  have hstable : (prefixWord ++ tailWord_5901020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901020).length < 2 ^ (prefixWord ++ tailWord_5901020).sum := by decide
  have hdescent : baseEnd_5901020 < baseStart_5901020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901023 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_5901023 : Nat := 118140960795 + 5901023 * 2 ^ 59
def prefixEnd_5901023 : Nat := 4983230072969 + 3 ^ 40 * 5901023 * 2
def baseEnd_5901023 : Nat := 3030061152236570954074195

theorem tailTrace_5901023 : CollatzResearch.WordTrace tailWord_5901023 prefixEnd_5901023 3030061152236570954074195 := by
  unfold tailWord_5901023
  simp only [CollatzResearch.WordTrace]
  refine ⟨215227990500608960337299723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143485327000405973558199815 215227990500608960337299723)
  ·
    refine ⟨322841985750913440505949585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215227990500608960337299723 322841985750913440505949585)
    ·
      refine ⟨242131489313185080379462189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322841985750913440505949585 242131489313185080379462189)
      ·
        refine ⟨90799308492444405142298321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242131489313185080379462189 90799308492444405142298321)
        ·
          refine ⟨68099481369333303856723741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90799308492444405142298321 68099481369333303856723741)
          ·
            refine ⟨25537305513499988946271403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68099481369333303856723741 25537305513499988946271403)
            ·
              refine ⟨38305958270249983419407105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25537305513499988946271403 38305958270249983419407105)
              ·
                refine ⟨28729468702687487564555329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38305958270249983419407105 28729468702687487564555329)
                ·
                  refine ⟨21547101527015615673416497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28729468702687487564555329 21547101527015615673416497)
                  ·
                    refine ⟨16160326145261711755062373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21547101527015615673416497 16160326145261711755062373)
                    ·
                      refine ⟨3030061152236570954074195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16160326145261711755062373 3030061152236570954074195)
                      ·
                        rfl

theorem cell23_5901023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_5901023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901023 prefixEnd_5901023 := by exact prefixLift 5901023
  have htrace : WordTrace (prefixWord ++ tailWord_5901023) baseStart_5901023 baseEnd_5901023 := by
    simpa [prefixWord, tailWord_5901023, baseEnd_5901023] using wordTrace_append hprefix tailTrace_5901023
  have hstable : (prefixWord ++ tailWord_5901023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901023).length < 2 ^ (prefixWord ++ tailWord_5901023).sum := by decide
  have hdescent : baseEnd_5901023 < baseStart_5901023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901070 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5901070 : Nat := 118140960795 + 5901070 * 2 ^ 59
def prefixEnd_5901070 : Nat := 4983230072969 + 3 ^ 40 * 5901070 * 2
def baseEnd_5901070 : Nat := 3030085285827332270186479

theorem tailTrace_5901070 : CollatzResearch.WordTrace tailWord_5901070 prefixEnd_5901070 3030085285827332270186479 := by
  unfold tailWord_5901070
  simp only [CollatzResearch.WordTrace]
  refine ⟨26903713091429835920532583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143486469820959124909507109 26903713091429835920532583)
  ·
    refine ⟨40355569637144753880798875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26903713091429835920532583 40355569637144753880798875)
    ·
      refine ⟨60533354455717130821198313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40355569637144753880798875 60533354455717130821198313)
      ·
        refine ⟨45400015841787848115898735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60533354455717130821198313 45400015841787848115898735)
        ·
          refine ⟨68100023762681772173848103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45400015841787848115898735 68100023762681772173848103)
          ·
            refine ⟨102150035644022658260772155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68100023762681772173848103 102150035644022658260772155)
            ·
              refine ⟨153225053466033987391158233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102150035644022658260772155 153225053466033987391158233)
              ·
                refine ⟨114918790099525490543368675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153225053466033987391158233 114918790099525490543368675)
                ·
                  refine ⟨172378185149288235815053013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114918790099525490543368675 172378185149288235815053013)
                  ·
                    refine ⟨4040113714436443026915305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172378185149288235815053013 4040113714436443026915305)
                    ·
                      refine ⟨3030085285827332270186479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040113714436443026915305 3030085285827332270186479)
                      ·
                        rfl

theorem cell23_5901070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5901070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901070 prefixEnd_5901070 := by exact prefixLift 5901070
  have htrace : WordTrace (prefixWord ++ tailWord_5901070) baseStart_5901070 baseEnd_5901070 := by
    simpa [prefixWord, tailWord_5901070, baseEnd_5901070] using wordTrace_append hprefix tailTrace_5901070
  have hstable : (prefixWord ++ tailWord_5901070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901070).length < 2 ^ (prefixWord ++ tailWord_5901070).sum := by decide
  have hdescent : baseEnd_5901070 < baseStart_5901070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901090 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5901090 : Nat := 118140960795 + 5901090 * 2 ^ 59
def prefixEnd_5901090 : Nat := 4983230072969 + 3 ^ 40 * 5901090 * 2
def baseEnd_5901090 : Nat := 3030095555440422191936387

theorem tailTrace_5901090 : CollatzResearch.WordTrace tailWord_5901090 prefixEnd_5901090 3030095555440422191936387 := by
  unfold tailWord_5901090
  simp only [CollatzResearch.WordTrace]
  refine ⟨53807608547841557694997181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143486956127577487186659149 53807608547841557694997181)
  ·
    refine ⟨20177853205440584135623943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53807608547841557694997181 20177853205440584135623943)
    ·
      refine ⟨30266779808160876203435915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20177853205440584135623943 30266779808160876203435915)
      ·
        refine ⟨45400169712241314305153873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30266779808160876203435915 45400169712241314305153873)
        ·
          refine ⟨34050127284180985728865405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45400169712241314305153873 34050127284180985728865405)
          ·
            refine ⟨12768797731567869648324527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34050127284180985728865405 12768797731567869648324527)
            ·
              refine ⟨19153196597351804472486791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12768797731567869648324527 19153196597351804472486791)
              ·
                refine ⟨28729794896027706708730187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19153196597351804472486791 28729794896027706708730187)
                ·
                  refine ⟨43094692344041560063095281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28729794896027706708730187 43094692344041560063095281)
                  ·
                    refine ⟨32321019258031170047321461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43094692344041560063095281 32321019258031170047321461)
                    ·
                      refine ⟨3030095555440422191936387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32321019258031170047321461 3030095555440422191936387)
                      ·
                        rfl

theorem cell23_5901090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5901090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901090 prefixEnd_5901090 := by exact prefixLift 5901090
  have htrace : WordTrace (prefixWord ++ tailWord_5901090) baseStart_5901090 baseEnd_5901090 := by
    simpa [prefixWord, tailWord_5901090, baseEnd_5901090] using wordTrace_append hprefix tailTrace_5901090
  have hstable : (prefixWord ++ tailWord_5901090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901090).length < 2 ^ (prefixWord ++ tailWord_5901090).sum := by decide
  have hdescent : baseEnd_5901090 < baseStart_5901090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901100 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_5901100 : Nat := 118140960795 + 5901100 * 2 ^ 59
def prefixEnd_5901100 : Nat := 4983230072969 + 3 ^ 40 * 5901100 * 2
def baseEnd_5901100 : Nat := 3030100690246967152811341

theorem tailTrace_5901100 : CollatzResearch.WordTrace tailWord_5901100 prefixEnd_5901100 3030100690246967152811341 := by
  unfold tailWord_5901100
  simp only [CollatzResearch.WordTrace]
  refine ⟨107615399460665001243926377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143487199280886668325235169 107615399460665001243926377)
  ·
    refine ⟨80711549595498750932944783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107615399460665001243926377 80711549595498750932944783)
    ·
      refine ⟨121067324393248126399417175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80711549595498750932944783 121067324393248126399417175)
      ·
        refine ⟨181600986589872189599125763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121067324393248126399417175 181600986589872189599125763)
        ·
          refine ⟨272401479884808284398688645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181600986589872189599125763 272401479884808284398688645)
          ·
            refine ⟨51075277478401553324754121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272401479884808284398688645 51075277478401553324754121)
            ·
              refine ⟨38306458108801164993565591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51075277478401553324754121 38306458108801164993565591)
              ·
                refine ⟨57459687163201747490348387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38306458108801164993565591 57459687163201747490348387)
                ·
                  refine ⟨86189530744802621235522581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57459687163201747490348387 86189530744802621235522581)
                  ·
                    refine ⟨4040134253662622870415121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86189530744802621235522581 4040134253662622870415121)
                    ·
                      refine ⟨3030100690246967152811341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040134253662622870415121 3030100690246967152811341)
                      ·
                        rfl

theorem cell23_5901100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_5901100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901100 prefixEnd_5901100 := by exact prefixLift 5901100
  have htrace : WordTrace (prefixWord ++ tailWord_5901100) baseStart_5901100 baseEnd_5901100 := by
    simpa [prefixWord, tailWord_5901100, baseEnd_5901100] using wordTrace_append hprefix tailTrace_5901100
  have hstable : (prefixWord ++ tailWord_5901100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901100).length < 2 ^ (prefixWord ++ tailWord_5901100).sum := by decide
  have hdescent : baseEnd_5901100 < baseStart_5901100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901127 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 1, 4]
def baseStart_5901127 : Nat := 118140960795 + 5901127 * 2 ^ 59
def prefixEnd_5901127 : Nat := 4983230072969 + 3 ^ 40 * 5901127 * 2
def baseEnd_5901127 : Nat := 1010038184741546182391239

theorem tailTrace_5901127 : CollatzResearch.WordTrace tailWord_5901127 prefixEnd_5901127 1010038184741546182391239 := by
  unfold tailWord_5901127
  simp only [CollatzResearch.WordTrace]
  refine ⟨215231783692232186099085635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143487855794821457399390423 215231783692232186099085635)
  ·
    refine ⟨322847675538348279148628453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215231783692232186099085635 322847675538348279148628453)
    ·
      refine ⟨60533939163440302340367835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322847675538348279148628453 60533939163440302340367835)
      ·
        refine ⟨90800908745160453510551753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60533939163440302340367835 90800908745160453510551753)
        ·
          refine ⟨68100681558870340132913815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90800908745160453510551753 68100681558870340132913815)
          ·
            refine ⟨102151022338305510199370723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68100681558870340132913815 102151022338305510199370723)
            ·
              refine ⟨153226533507458265299056085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102151022338305510199370723 153226533507458265299056085)
              ·
                refine ⟨3591246879081053092946627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153226533507458265299056085 3591246879081053092946627)
                ·
                  refine ⟨5386870318621579639419941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591246879081053092946627 5386870318621579639419941)
                  ·
                    refine ⟨1010038184741546182391239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386870318621579639419941 1010038184741546182391239)
                    ·
                      rfl

theorem cell23_5901127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_5901127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901127 prefixEnd_5901127 := by exact prefixLift 5901127
  have htrace : WordTrace (prefixWord ++ tailWord_5901127) baseStart_5901127 baseEnd_5901127 := by
    simpa [prefixWord, tailWord_5901127, baseEnd_5901127] using wordTrace_append hprefix tailTrace_5901127
  have hstable : (prefixWord ++ tailWord_5901127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901127).length < 2 ^ (prefixWord ++ tailWord_5901127).sum := by decide
  have hdescent : baseEnd_5901127 < baseStart_5901127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901170 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_5901170 : Nat := 118140960795 + 5901170 * 2 ^ 59
def prefixEnd_5901170 : Nat := 4983230072969 + 3 ^ 40 * 5901170 * 2
def baseEnd_5901170 : Nat := 1010045544630927292978673

theorem tailTrace_5901170 : CollatzResearch.WordTrace tailWord_5901170 prefixEnd_5901170 1010045544630927292978673 := by
  unfold tailWord_5901170
  simp only [CollatzResearch.WordTrace]
  refine ⟨53808338007769101110725241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143488901354050936295267309 53808338007769101110725241)
  ·
    refine ⟨40356253505826825833043931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53808338007769101110725241 40356253505826825833043931)
    ·
      refine ⟨60534380258740238749565897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40356253505826825833043931 60534380258740238749565897)
      ·
        refine ⟨45400785194055179062174423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60534380258740238749565897 45400785194055179062174423)
        ·
          refine ⟨68101177791082768593261635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45400785194055179062174423 68101177791082768593261635)
          ·
            refine ⟨102151766686624152889892453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68101177791082768593261635 102151766686624152889892453)
            ·
              refine ⟨19153456253742028666854835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102151766686624152889892453 19153456253742028666854835)
              ·
                refine ⟨28730184380613043000282253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19153456253742028666854835 28730184380613043000282253)
                ·
                  refine ⟨10773819142729891125105845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28730184380613043000282253 10773819142729891125105845)
                  ·
                    refine ⟨1010045544630927292978673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10773819142729891125105845 1010045544630927292978673)
                    ·
                      rfl

theorem cell23_5901170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_5901170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901170 prefixEnd_5901170 := by exact prefixLift 5901170
  have htrace : WordTrace (prefixWord ++ tailWord_5901170) baseStart_5901170 baseEnd_5901170 := by
    simpa [prefixWord, tailWord_5901170, baseEnd_5901170] using wordTrace_append hprefix tailTrace_5901170
  have hstable : (prefixWord ++ tailWord_5901170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901170).length < 2 ^ (prefixWord ++ tailWord_5901170).sum := by decide
  have hdescent : baseEnd_5901170 < baseStart_5901170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901177 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 5, 2]
def baseStart_5901177 : Nat := 118140960795 + 5901177 * 2 ^ 59
def prefixEnd_5901177 : Nat := 4983230072969 + 3 ^ 40 * 5901177 * 2
def baseEnd_5901177 : Nat := 3030140228257363351548487

theorem tailTrace_5901177 : CollatzResearch.WordTrace tailWord_5901177 prefixEnd_5901177 3030140228257363351548487 := by
  unfold tailWord_5901177
  simp only [CollatzResearch.WordTrace]
  refine ⟨215233607342051044638405785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143489071561367363092270523 215233607342051044638405785)
  ·
    refine ⟨161425205506538283478804339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215233607342051044638405785 161425205506538283478804339)
    ·
      refine ⟨242137808259807425218206509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161425205506538283478804339 242137808259807425218206509)
      ·
        refine ⟨90801678097427784456827441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242137808259807425218206509 90801678097427784456827441)
        ·
          refine ⟨68101258573070838342620581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90801678097427784456827441 68101258573070838342620581)
          ·
            refine ⟨12768985982450782189241359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68101258573070838342620581 12768985982450782189241359)
            ·
              refine ⟨19153478973676173283862039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12768985982450782189241359 19153478973676173283862039)
              ·
                refine ⟨28730218460514259925793059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19153478973676173283862039 28730218460514259925793059)
                ·
                  refine ⟨43095327690771389888689589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28730218460514259925793059 43095327690771389888689589)
                  ·
                    refine ⟨4040186971009817802064649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43095327690771389888689589 4040186971009817802064649)
                    ·
                      refine ⟨3030140228257363351548487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040186971009817802064649 3030140228257363351548487)
                      ·
                        rfl

theorem cell23_5901177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_5901177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901177 prefixEnd_5901177 := by exact prefixLift 5901177
  have htrace : WordTrace (prefixWord ++ tailWord_5901177) baseStart_5901177 baseEnd_5901177 := by
    simpa [prefixWord, tailWord_5901177, baseEnd_5901177] using wordTrace_append hprefix tailTrace_5901177
  have hstable : (prefixWord ++ tailWord_5901177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901177).length < 2 ^ (prefixWord ++ tailWord_5901177).sum := by decide
  have hdescent : baseEnd_5901177 < baseStart_5901177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901217 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_5901217 : Nat := 118140960795 + 5901217 * 2 ^ 59
def prefixEnd_5901217 : Nat := 4983230072969 + 3 ^ 40 * 5901217 * 2
def baseEnd_5901217 : Nat := 1010053589161181065016101

theorem tailTrace_5901217 : CollatzResearch.WordTrace tailWord_5901217 prefixEnd_5901217 1010053589161181065016101 := by
  unfold tailWord_5901217
  simp only [CollatzResearch.WordTrace]
  refine ⟨215235066261906131469861905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143490044174604087646574603 215235066261906131469861905)
  ·
    refine ⟨161426299696429598602396429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215235066261906131469861905 161426299696429598602396429)
    ·
      refine ⟨60534862386161099475898661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161426299696429598602396429 60534862386161099475898661)
      ·
        refine ⟨11350286697405206151730999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60534862386161099475898661 11350286697405206151730999)
        ·
          refine ⟨17025430046107809227596499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11350286697405206151730999 17025430046107809227596499)
          ·
            refine ⟨25538145069161713841394749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17025430046107809227596499 25538145069161713841394749)
            ·
              refine ⟨9576804400935642690523031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25538145069161713841394749 9576804400935642690523031)
              ·
                refine ⟨14365206601403464035784547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9576804400935642690523031 14365206601403464035784547)
                ·
                  refine ⟨21547809902105196053676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14365206601403464035784547 21547809902105196053676821)
                  ·
                    refine ⟨1010053589161181065016101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21547809902105196053676821 1010053589161181065016101)
                    ·
                      rfl

theorem cell23_5901217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_5901217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901217 prefixEnd_5901217 := by exact prefixLift 5901217
  have htrace : WordTrace (prefixWord ++ tailWord_5901217) baseStart_5901217 baseEnd_5901217 := by
    simpa [prefixWord, tailWord_5901217, baseEnd_5901217] using wordTrace_append hprefix tailTrace_5901217
  have hstable : (prefixWord ++ tailWord_5901217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901217).length < 2 ^ (prefixWord ++ tailWord_5901217).sum := by decide
  have hdescent : baseEnd_5901217 < baseStart_5901217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901220 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_5901220 : Nat := 118140960795 + 5901220 * 2 ^ 59
def prefixEnd_5901220 : Nat := 4983230072969 + 3 ^ 40 * 5901220 * 2
def baseEnd_5901220 : Nat := 3030162307925506683310789

theorem tailTrace_5901220 : CollatzResearch.WordTrace tailWord_5901220 prefixEnd_5901220 3030162307925506683310789 := by
  unfold tailWord_5901220
  simp only [CollatzResearch.WordTrace]
  refine ⟨107617587840447631491110557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143490117120596841988147409 107617587840447631491110557)
  ·
    refine ⟨40356595440167861809166459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107617587840447631491110557 40356595440167861809166459)
    ·
      refine ⟨60534893160251792713749689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40356595440167861809166459 60534893160251792713749689)
      ·
        refine ⟨45401169870188844535312267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60534893160251792713749689 45401169870188844535312267)
        ·
          refine ⟨68101754805283266802968401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45401169870188844535312267 68101754805283266802968401)
          ·
            refine ⟨51076316103962450102226301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68101754805283266802968401 51076316103962450102226301)
            ·
              refine ⟨19153618538985918788334863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51076316103962450102226301 19153618538985918788334863)
              ·
                refine ⟨28730427808478878182502295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19153618538985918788334863 28730427808478878182502295)
                ·
                  refine ⟨43095641712718317273753443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28730427808478878182502295 43095641712718317273753443)
                  ·
                    refine ⟨64643462569077475910630165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43095641712718317273753443 64643462569077475910630165)
                    ·
                      refine ⟨3030162307925506683310789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64643462569077475910630165 3030162307925506683310789)
                      ·
                        rfl

theorem cell23_5901220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_5901220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901220 prefixEnd_5901220 := by exact prefixLift 5901220
  have htrace : WordTrace (prefixWord ++ tailWord_5901220) baseStart_5901220 baseEnd_5901220 := by
    simpa [prefixWord, tailWord_5901220, baseEnd_5901220] using wordTrace_append hprefix tailTrace_5901220
  have hstable : (prefixWord ++ tailWord_5901220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901220).length < 2 ^ (prefixWord ++ tailWord_5901220).sum := by decide
  have hdescent : baseEnd_5901220 < baseStart_5901220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901260 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_5901260 : Nat := 118140960795 + 5901260 * 2 ^ 59
def prefixEnd_5901260 : Nat := 4983230072969 + 3 ^ 40 * 5901260 * 2
def baseEnd_5901260 : Nat := 1010060949050562175603535

theorem tailTrace_5901260 : CollatzResearch.WordTrace tailWord_5901260 prefixEnd_5901260 1010060949050562175603535 := by
  unfold tailWord_5901260
  simp only [CollatzResearch.WordTrace]
  refine ⟨107618317300375174906838617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143491089733833566542451489 107618317300375174906838617)
  ·
    refine ⟨80713737975281381180128963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107618317300375174906838617 80713737975281381180128963)
    ·
      refine ⟨121070606962922071770193445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80713737975281381180128963 121070606962922071770193445)
      ·
        refine ⟨22700738805547888456911271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121070606962922071770193445 22700738805547888456911271)
        ·
          refine ⟨34051108208321832685366907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22700738805547888456911271 34051108208321832685366907)
          ·
            refine ⟨51076662312482749028050361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34051108208321832685366907 51076662312482749028050361)
            ·
              refine ⟨38307496734362061771037771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51076662312482749028050361 38307496734362061771037771)
              ·
                refine ⟨57461245101543092656556657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38307496734362061771037771 57461245101543092656556657)
                ·
                  refine ⟨43095933826157319492417493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57461245101543092656556657 43095933826157319492417493)
                  ·
                    refine ⟨1010060949050562175603535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43095933826157319492417493 1010060949050562175603535)
                    ·
                      rfl

theorem cell23_5901260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_5901260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901260 prefixEnd_5901260 := by exact prefixLift 5901260
  have htrace : WordTrace (prefixWord ++ tailWord_5901260) baseStart_5901260 baseEnd_5901260 := by
    simpa [prefixWord, tailWord_5901260, baseEnd_5901260] using wordTrace_append hprefix tailTrace_5901260
  have hstable : (prefixWord ++ tailWord_5901260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901260).length < 2 ^ (prefixWord ++ tailWord_5901260).sum := by decide
  have hdescent : baseEnd_5901260 < baseStart_5901260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901284 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_5901284 : Nat := 118140960795 + 5901284 * 2 ^ 59
def prefixEnd_5901284 : Nat := 4983230072969 + 3 ^ 40 * 5901284 * 2
def baseEnd_5901284 : Nat := 3030195170687394432910495

theorem tailTrace_5901284 : CollatzResearch.WordTrace tailWord_5901284 prefixEnd_5901284 3030195170687394432910495 := by
  unfold tailWord_5901284
  simp only [CollatzResearch.WordTrace]
  refine ⟨107618754976331700956275453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143491673301775601275033937 107618754976331700956275453)
  ·
    refine ⟨40357033116124387858603295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107618754976331700956275453 40357033116124387858603295)
    ·
      refine ⟨60535549674186581787904943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40357033116124387858603295 60535549674186581787904943)
      ·
        refine ⟨90803324511279872681857415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60535549674186581787904943 90803324511279872681857415)
        ·
          refine ⟨136204986766919809022786123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90803324511279872681857415 136204986766919809022786123)
          ·
            refine ⟨204307480150379713534179185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136204986766919809022786123 204307480150379713534179185)
            ·
              refine ⟨153230610112784785150634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204307480150379713534179185 153230610112784785150634389)
              ·
                refine ⟨7182684849036786803935987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153230610112784785150634389 7182684849036786803935987)
                ·
                  refine ⟨10774027273555180205903981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182684849036786803935987 10774027273555180205903981)
                  ·
                    refine ⟨4040260227583192577213993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10774027273555180205903981 4040260227583192577213993)
                    ·
                      refine ⟨3030195170687394432910495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040260227583192577213993 3030195170687394432910495)
                      ·
                        rfl

theorem cell23_5901284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_5901284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901284 prefixEnd_5901284 := by exact prefixLift 5901284
  have htrace : WordTrace (prefixWord ++ tailWord_5901284) baseStart_5901284 baseEnd_5901284 := by
    simpa [prefixWord, tailWord_5901284, baseEnd_5901284] using wordTrace_append hprefix tailTrace_5901284
  have hstable : (prefixWord ++ tailWord_5901284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901284).length < 2 ^ (prefixWord ++ tailWord_5901284).sum := by decide
  have hdescent : baseEnd_5901284 < baseStart_5901284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901382 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5901382 : Nat := 118140960795 + 5901382 * 2 ^ 59
def prefixEnd_5901382 : Nat := 4983230072969 + 3 ^ 40 * 5901382 * 2
def baseEnd_5901382 : Nat := 3030245491791535049485045

theorem tailTrace_5901382 : CollatzResearch.WordTrace tailWord_5901382 prefixEnd_5901382 3030245491791535049485045 := by
  unfold tailWord_5901382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726283884572136395300575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143494056204205576433078933 6726283884572136395300575)
  ·
    refine ⟨10089425826858204592950863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726283884572136395300575 10089425826858204592950863)
    ·
      refine ⟨15134138740287306889426295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089425826858204592950863 15134138740287306889426295)
      ·
        refine ⟨22701208110430960334139443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15134138740287306889426295 22701208110430960334139443)
        ·
          refine ⟨34051812165646440501209165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22701208110430960334139443 34051812165646440501209165)
          ·
            refine ⟨12769429562117415187953437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34051812165646440501209165 12769429562117415187953437)
            ·
              refine ⟨4788536085794030695482539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12769429562117415187953437 4788536085794030695482539)
              ·
                refine ⟨7182804128691046043223809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788536085794030695482539 7182804128691046043223809)
                ·
                  refine ⟨5387103096518284532417857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182804128691046043223809 5387103096518284532417857)
                  ·
                    refine ⟨4040327322388713399313393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387103096518284532417857 4040327322388713399313393)
                    ·
                      refine ⟨3030245491791535049485045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040327322388713399313393 3030245491791535049485045)
                      ·
                        rfl

theorem cell23_5901382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5901382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901382 prefixEnd_5901382 := by exact prefixLift 5901382
  have htrace : WordTrace (prefixWord ++ tailWord_5901382) baseStart_5901382 baseEnd_5901382 := by
    simpa [prefixWord, tailWord_5901382, baseEnd_5901382] using wordTrace_append hprefix tailTrace_5901382
  have hstable : (prefixWord ++ tailWord_5901382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901382).length < 2 ^ (prefixWord ++ tailWord_5901382).sum := by decide
  have hdescent : baseEnd_5901382 < baseStart_5901382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901404 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5901404 : Nat := 118140960795 + 5901404 * 2 ^ 59
def prefixEnd_5901404 : Nat := 4983230072969 + 3 ^ 40 * 5901404 * 2
def baseEnd_5901404 : Nat := 3030256788365933963409943

theorem tailTrace_5901404 : CollatzResearch.WordTrace tailWord_5901404 prefixEnd_5901404 3030256788365933963409943 := by
  unfold tailWord_5901404
  simp only [CollatzResearch.WordTrace]
  refine ⟨107620943356114331203459633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143494591141485774937946177 107620943356114331203459633)
  ·
    refine ⟨80715707517085748402594725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107620943356114331203459633 80715707517085748402594725)
    ·
      refine ⟨15134195159453577825486511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80715707517085748402594725 15134195159453577825486511)
      ·
        refine ⟨22701292739180366738229767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15134195159453577825486511 22701292739180366738229767)
        ·
          refine ⟨34051939108770550107344651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22701292739180366738229767 34051939108770550107344651)
          ·
            refine ⟨51077908663155825161016977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34051939108770550107344651 51077908663155825161016977)
            ·
              refine ⟨38308431497366868870762733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51077908663155825161016977 38308431497366868870762733)
              ·
                refine ⟨14365661811512575826536025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38308431497366868870762733 14365661811512575826536025)
                ·
                  refine ⟨10774246358634431869902019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14365661811512575826536025 10774246358634431869902019)
                  ·
                    refine ⟨16161369537951647804853029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10774246358634431869902019 16161369537951647804853029)
                    ·
                      refine ⟨3030256788365933963409943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16161369537951647804853029 3030256788365933963409943)
                      ·
                        rfl

theorem cell23_5901404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5901404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901404 prefixEnd_5901404 := by exact prefixLift 5901404
  have htrace : WordTrace (prefixWord ++ tailWord_5901404) baseStart_5901404 baseEnd_5901404 := by
    simpa [prefixWord, tailWord_5901404, baseEnd_5901404] using wordTrace_append hprefix tailTrace_5901404
  have hstable : (prefixWord ++ tailWord_5901404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901404).length < 2 ^ (prefixWord ++ tailWord_5901404).sum := by decide
  have hdescent : baseEnd_5901404 < baseStart_5901404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901405 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 5]
def baseStart_5901405 : Nat := 118140960795 + 5901405 * 2 ^ 59
def prefixEnd_5901405 : Nat := 4983230072969 + 3 ^ 40 * 5901405 * 2
def baseEnd_5901405 : Nat := 336695255760732051055271

theorem tailTrace_5901405 : CollatzResearch.WordTrace tailWord_5901405 prefixEnd_5901405 336695255760732051055271 := by
  unfold tailWord_5901405
  simp only [CollatzResearch.WordTrace]
  refine ⟨215241923185225039577705669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143494615456816693051803779 215241923185225039577705669)
  ·
    refine ⟨40357860597229694920819813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215241923185225039577705669 40357860597229694920819813)
    ·
      refine ⟨7567098861980567797653715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40357860597229694920819813 7567098861980567797653715)
      ·
        refine ⟨11350648292970851696480573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567098861980567797653715 11350648292970851696480573)
        ·
          refine ⟨4256493109864069386180215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11350648292970851696480573 4256493109864069386180215)
          ·
            refine ⟨6384739664796104079270323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256493109864069386180215 6384739664796104079270323)
            ·
              refine ⟨9577109497194156118905485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384739664796104079270323 9577109497194156118905485)
              ·
                refine ⟨3591416061447808544589557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9577109497194156118905485 3591416061447808544589557)
                ·
                  refine ⟨336695255760732051055271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591416061447808544589557 336695255760732051055271)
                  ·
                    rfl

theorem cell23_5901405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_5901405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901405 prefixEnd_5901405 := by exact prefixLift 5901405
  have htrace : WordTrace (prefixWord ++ tailWord_5901405) baseStart_5901405 baseEnd_5901405 := by
    simpa [prefixWord, tailWord_5901405, baseEnd_5901405] using wordTrace_append hprefix tailTrace_5901405
  have hstable : (prefixWord ++ tailWord_5901405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901405).length < 2 ^ (prefixWord ++ tailWord_5901405).sum := by decide
  have hdescent : baseEnd_5901405 < baseStart_5901405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901407 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_5901407 : Nat := 118140960795 + 5901407 * 2 ^ 59
def prefixEnd_5901407 : Nat := 4983230072969 + 3 ^ 40 * 5901407 * 2
def baseEnd_5901407 : Nat := 3030258328807897451672429

theorem tailTrace_5901407 : CollatzResearch.WordTrace tailWord_5901407 prefixEnd_5901407 3030258328807897451672429 := by
  unfold tailWord_5901407
  simp only [CollatzResearch.WordTrace]
  refine ⟨215241996131217793919278475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143494664087478529279518983 215241996131217793919278475)
  ·
    refine ⟨322862994196826690878917713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215241996131217793919278475 322862994196826690878917713)
    ·
      refine ⟨242147245647620018159188285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322862994196826690878917713 242147245647620018159188285)
      ·
        refine ⟨90805217117857506809695607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242147245647620018159188285 90805217117857506809695607)
        ·
          refine ⟨136207825676786260214543411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90805217117857506809695607 136207825676786260214543411)
          ·
            refine ⟨204311738515179390321815117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136207825676786260214543411 204311738515179390321815117)
            ·
              refine ⟨76616901943192271370680669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204311738515179390321815117 76616901943192271370680669)
              ·
                refine ⟨28731338228697101764005251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76616901943192271370680669 28731338228697101764005251)
                ·
                  refine ⟨43097007343045652646007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28731338228697101764005251 43097007343045652646007877)
                  ·
                    refine ⟨8080688876821059871126477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43097007343045652646007877 8080688876821059871126477)
                    ·
                      refine ⟨3030258328807897451672429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8080688876821059871126477 3030258328807897451672429)
                      ·
                        rfl

theorem cell23_5901407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_5901407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901407 prefixEnd_5901407 := by exact prefixLift 5901407
  have htrace : WordTrace (prefixWord ++ tailWord_5901407) baseStart_5901407 baseEnd_5901407 := by
    simpa [prefixWord, tailWord_5901407, baseEnd_5901407] using wordTrace_append hprefix tailTrace_5901407
  have hstable : (prefixWord ++ tailWord_5901407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901407).length < 2 ^ (prefixWord ++ tailWord_5901407).sum := by decide
  have hdescent : baseEnd_5901407 < baseStart_5901407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901424 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_5901424 : Nat := 118140960795 + 5901424 * 2 ^ 59
def prefixEnd_5901424 : Nat := 4983230072969 + 3 ^ 40 * 5901424 * 2
def baseEnd_5901424 : Nat := 3030267057979023885159851

theorem tailTrace_5901424 : CollatzResearch.WordTrace tailWord_5901424 prefixEnd_5901424 3030267057979023885159851 := by
  unfold tailWord_5901424
  simp only [CollatzResearch.WordTrace]
  refine ⟨107621308086078102911323663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143495077448104137215098217 107621308086078102911323663)
  ·
    refine ⟨161431962129117154366985495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107621308086078102911323663 161431962129117154366985495)
    ·
      refine ⟨242147943193675731550478243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161431962129117154366985495 242147943193675731550478243)
      ·
        refine ⟨363221914790513597325717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242147943193675731550478243 363221914790513597325717365)
        ·
          refine ⟨34052054511610649749286003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 363221914790513597325717365 34052054511610649749286003)
          ·
            refine ⟨51078081767415974623929005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34052054511610649749286003 51078081767415974623929005)
            ·
              refine ⟨19154280662780990483973377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51078081767415974623929005 19154280662780990483973377)
              ·
                refine ⟨14365710497085742862980033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19154280662780990483973377 14365710497085742862980033)
                ·
                  refine ⟨10774282872814307147235025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14365710497085742862980033 10774282872814307147235025)
                  ·
                    refine ⟨8080712154610730360426269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10774282872814307147235025 8080712154610730360426269)
                    ·
                      refine ⟨3030267057979023885159851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8080712154610730360426269 3030267057979023885159851)
                      ·
                        rfl

theorem cell23_5901424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_5901424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901424 prefixEnd_5901424 := by exact prefixLift 5901424
  have htrace : WordTrace (prefixWord ++ tailWord_5901424) baseStart_5901424 baseEnd_5901424 := by
    simpa [prefixWord, tailWord_5901424, baseEnd_5901424] using wordTrace_append hprefix tailTrace_5901424
  have hstable : (prefixWord ++ tailWord_5901424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901424).length < 2 ^ (prefixWord ++ tailWord_5901424).sum := by decide
  have hdescent : baseEnd_5901424 < baseStart_5901424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901444 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 6]
def baseStart_5901444 : Nat := 118140960795 + 5901444 * 2 ^ 59
def prefixEnd_5901444 : Nat := 4983230072969 + 3 ^ 40 * 5901444 * 2
def baseEnd_5901444 : Nat := 336697480843568200767751

theorem tailTrace_5901444 : CollatzResearch.WordTrace tailWord_5901444 prefixEnd_5901444 336697480843568200767751 := by
  unfold tailWord_5901444
  simp only [CollatzResearch.WordTrace]
  refine ⟨107621672816041874619187693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143495563754722499492250257 107621672816041874619187693)
  ·
    refine ⟨40358127306015702982195385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107621672816041874619187693 40358127306015702982195385)
    ·
      refine ⟨30268595479511777236646539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40358127306015702982195385 30268595479511777236646539)
      ·
        refine ⟨45402893219267665854969809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30268595479511777236646539 45402893219267665854969809)
        ·
          refine ⟨34052169914450749391227357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45402893219267665854969809 34052169914450749391227357)
          ·
            refine ⟨12769563717919031021710259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34052169914450749391227357 12769563717919031021710259)
            ·
              refine ⟨19154345576878546532565389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12769563717919031021710259 19154345576878546532565389)
              ·
                refine ⟨7182879591329454949712021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19154345576878546532565389 7182879591329454949712021)
                ·
                  refine ⟨336697480843568200767751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7182879591329454949712021 336697480843568200767751)
                  ·
                    rfl

theorem cell23_5901444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_5901444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901444 prefixEnd_5901444 := by exact prefixLift 5901444
  have htrace : WordTrace (prefixWord ++ tailWord_5901444) baseStart_5901444 baseEnd_5901444 := by
    simpa [prefixWord, tailWord_5901444, baseEnd_5901444] using wordTrace_append hprefix tailTrace_5901444
  have hstable : (prefixWord ++ tailWord_5901444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901444).length < 2 ^ (prefixWord ++ tailWord_5901444).sum := by decide
  have hdescent : baseEnd_5901444 < baseStart_5901444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901482 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5901482 : Nat := 118140960795 + 5901482 * 2 ^ 59
def prefixEnd_5901482 : Nat := 4983230072969 + 3 ^ 40 * 5901482 * 2
def baseEnd_5901482 : Nat := 1010098946618994886078195

theorem tailTrace_5901482 : CollatzResearch.WordTrace tailWord_5901482 prefixEnd_5901482 1010098946618994886078195 := by
  unfold tailWord_5901482
  simp only [CollatzResearch.WordTrace]
  refine ⟨53811182901486520432064675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143496487737297387818839133 53811182901486520432064675)
  ·
    refine ⟨80716774352229780648097013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53811182901486520432064675 80716774352229780648097013)
    ·
      refine ⟨7567197595521541935759095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80716774352229780648097013 7567197595521541935759095)
      ·
        refine ⟨11350796393282312903638643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567197595521541935759095 11350796393282312903638643)
        ·
          refine ⟨17026194589923469355457965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11350796393282312903638643 17026194589923469355457965)
          ·
            refine ⟨6384822971221301008296737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17026194589923469355457965 6384822971221301008296737)
            ·
              refine ⟨4788617228415975756222553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6384822971221301008296737 4788617228415975756222553)
              ·
                refine ⟨3591462921311981817166915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788617228415975756222553 3591462921311981817166915)
                ·
                  refine ⟨5387194381967972725750373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591462921311981817166915 5387194381967972725750373)
                  ·
                    refine ⟨1010098946618994886078195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387194381967972725750373 1010098946618994886078195)
                    ·
                      rfl

theorem cell23_5901482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5901482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901482 prefixEnd_5901482 := by exact prefixLift 5901482
  have htrace : WordTrace (prefixWord ++ tailWord_5901482) baseStart_5901482 baseEnd_5901482 := by
    simpa [prefixWord, tailWord_5901482, baseEnd_5901482] using wordTrace_append hprefix tailTrace_5901482
  have hstable : (prefixWord ++ tailWord_5901482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901482).length < 2 ^ (prefixWord ++ tailWord_5901482).sum := by decide
  have hdescent : baseEnd_5901482 < baseStart_5901482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901604 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5901604 : Nat := 118140960795 + 5901604 * 2 ^ 59
def prefixEnd_5901604 : Nat := 4983230072969 + 3 ^ 40 * 5901604 * 2
def baseEnd_5901604 : Nat := 3030359484496833180909023

theorem tailTrace_5901604 : CollatzResearch.WordTrace tailWord_5901604 prefixEnd_5901604 3030359484496833180909023 := by
  unfold tailWord_5901604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107624590655752048282099933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143499454207669397709466577 107624590655752048282099933)
  ·
    refine ⟨40359221495907018105787475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107624590655752048282099933 40359221495907018105787475)
    ·
      refine ⟨60538832243860527158681213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40359221495907018105787475 60538832243860527158681213)
      ·
        refine ⟨22702062091447697684505455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60538832243860527158681213 22702062091447697684505455)
        ·
          refine ⟨34053093137171546526758183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22702062091447697684505455 34053093137171546526758183)
          ·
            refine ⟨51079639705757319790137275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34053093137171546526758183 51079639705757319790137275)
            ·
              refine ⟨76619459558635979685205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51079639705757319790137275 76619459558635979685205913)
              ·
                refine ⟨57464594668976984763904435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76619459558635979685205913 57464594668976984763904435)
                ·
                  refine ⟨86196892003465477145856653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57464594668976984763904435 86196892003465477145856653)
                  ·
                    refine ⟨32323834501299553929696245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86196892003465477145856653 32323834501299553929696245)
                    ·
                      refine ⟨3030359484496833180909023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32323834501299553929696245 3030359484496833180909023)
                      ·
                        rfl

theorem cell23_5901604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5901604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901604 prefixEnd_5901604 := by exact prefixLift 5901604
  have htrace : WordTrace (prefixWord ++ tailWord_5901604) baseStart_5901604 baseEnd_5901604 := by
    simpa [prefixWord, tailWord_5901604, baseEnd_5901604] using wordTrace_append hprefix tailTrace_5901604
  have hstable : (prefixWord ++ tailWord_5901604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901604).length < 2 ^ (prefixWord ++ tailWord_5901604).sum := by decide
  have hdescent : baseEnd_5901604 < baseStart_5901604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901622 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5901622 : Nat := 118140960795 + 5901622 * 2 ^ 59
def prefixEnd_5901622 : Nat := 4983230072969 + 3 ^ 40 * 5901622 * 2
def baseEnd_5901622 : Nat := 3030368727148614110483941

theorem tailTrace_5901622 : CollatzResearch.WordTrace tailWord_5901622 prefixEnd_5901622 3030368727148614110483941 := by
  unfold tailWord_5901622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453114864089930352397195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143499891883625923758903413 13453114864089930352397195)
  ·
    refine ⟨20179672296134895528595793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13453114864089930352397195 20179672296134895528595793)
    ·
      refine ⟨15134754222101171646446845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20179672296134895528595793 15134754222101171646446845)
      ·
        refine ⟨5675532833287939367417567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15134754222101171646446845 5675532833287939367417567)
        ·
          refine ⟨8513299249931909051126351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5675532833287939367417567 8513299249931909051126351)
          ·
            refine ⟨12769948874897863576689527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8513299249931909051126351 12769948874897863576689527)
            ·
              refine ⟨19154923312346795365034291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12769948874897863576689527 19154923312346795365034291)
              ·
                refine ⟨28732384968520193047551437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19154923312346795365034291 28732384968520193047551437)
                ·
                  refine ⟨10774644363195072392831789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28732384968520193047551437 10774644363195072392831789)
                  ·
                    refine ⟨4040491636198152147311921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10774644363195072392831789 4040491636198152147311921)
                    ·
                      refine ⟨3030368727148614110483941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040491636198152147311921 3030368727148614110483941)
                      ·
                        rfl

theorem cell23_5901622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5901622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901622 prefixEnd_5901622 := by exact prefixLift 5901622
  have htrace : WordTrace (prefixWord ++ tailWord_5901622) baseStart_5901622 baseEnd_5901622 := by
    simpa [prefixWord, tailWord_5901622, baseEnd_5901622] using wordTrace_append hprefix tailTrace_5901622
  have hstable : (prefixWord ++ tailWord_5901622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901622).length < 2 ^ (prefixWord ++ tailWord_5901622).sum := by decide
  have hdescent : baseEnd_5901622 < baseStart_5901622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901658 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_5901658 : Nat := 118140960795 + 5901658 * 2 ^ 59
def prefixEnd_5901658 : Nat := 4983230072969 + 3 ^ 40 * 5901658 * 2
def baseEnd_5901658 : Nat := 336709690272463996625975

theorem tailTrace_5901658 : CollatzResearch.WordTrace tailWord_5901658 prefixEnd_5901658 336709690272463996625975 := by
  unfold tailWord_5901658
  simp only [CollatzResearch.WordTrace]
  refine ⟨53812787713327115946666407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143500767235538975857777085 53812787713327115946666407)
  ·
    refine ⟨80719181569990673919999611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53812787713327115946666407 80719181569990673919999611)
    ·
      refine ⟨121078772354986010879999417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80719181569990673919999611 121078772354986010879999417)
      ·
        refine ⟨90809079266239508159999563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121078772354986010879999417 90809079266239508159999563)
        ·
          refine ⟨136213618899359262239999345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90809079266239508159999563 136213618899359262239999345)
          ·
            refine ⟨102160214174519446679999509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136213618899359262239999345 102160214174519446679999509)
            ·
              refine ⟨4788760039430599063124977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102160214174519446679999509 4788760039430599063124977)
              ·
                refine ⟨3591570029572949297343733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788760039430599063124977 3591570029572949297343733)
                ·
                  refine ⟨336709690272463996625975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591570029572949297343733 336709690272463996625975)
                  ·
                    rfl

theorem cell23_5901658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_5901658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901658 prefixEnd_5901658 := by exact prefixLift 5901658
  have htrace : WordTrace (prefixWord ++ tailWord_5901658) baseStart_5901658 baseEnd_5901658 := by
    simpa [prefixWord, tailWord_5901658, baseEnd_5901658] using wordTrace_append hprefix tailTrace_5901658
  have hstable : (prefixWord ++ tailWord_5901658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901658).length < 2 ^ (prefixWord ++ tailWord_5901658).sum := by decide
  have hdescent : baseEnd_5901658 < baseStart_5901658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901691 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 6, 2]
def baseStart_5901691 : Nat := 118140960795 + 5901691 * 2 ^ 59
def prefixEnd_5901691 : Nat := 4983230072969 + 3 ^ 40 * 5901691 * 2
def baseEnd_5901691 : Nat := 3030404157313774340521123

theorem tailTrace_5901691 : CollatzResearch.WordTrace tailWord_5901691 prefixEnd_5901691 3030404157313774340521123 := by
  unfold tailWord_5901691
  simp only [CollatzResearch.WordTrace]
  refine ⟨215252354462188910422616927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143501569641459273615077951 215252354462188910422616927)
  ·
    refine ⟨322878531693283365633925391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215252354462188910422616927 322878531693283365633925391)
    ·
      refine ⟨484317797539925048450888087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322878531693283365633925391 484317797539925048450888087)
      ·
        refine ⟨726476696309887572676332131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484317797539925048450888087 726476696309887572676332131)
        ·
          refine ⟨1089715044464831359014498197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726476696309887572676332131 1089715044464831359014498197)
          ·
            refine ⟨51080392709288969953804603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1089715044464831359014498197 51080392709288969953804603)
            ·
              refine ⟨76620589063933454930706905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51080392709288969953804603 76620589063933454930706905)
              ·
                refine ⟨57465441797950091198030179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76620589063933454930706905 57465441797950091198030179)
                ·
                  refine ⟨86198162696925136797045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57465441797950091198030179 86198162696925136797045269)
                  ·
                    refine ⟨4040538876418365787361497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86198162696925136797045269 4040538876418365787361497)
                    ·
                      refine ⟨3030404157313774340521123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040538876418365787361497 3030404157313774340521123)
                      ·
                        rfl

theorem cell23_5901691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6, 2].length) (baseStart_5901691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901691 prefixEnd_5901691 := by exact prefixLift 5901691
  have htrace : WordTrace (prefixWord ++ tailWord_5901691) baseStart_5901691 baseEnd_5901691 := by
    simpa [prefixWord, tailWord_5901691, baseEnd_5901691] using wordTrace_append hprefix tailTrace_5901691
  have hstable : (prefixWord ++ tailWord_5901691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901691).length < 2 ^ (prefixWord ++ tailWord_5901691).sum := by decide
  have hdescent : baseEnd_5901691 < baseStart_5901691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901775 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 1, 1, 3]
def baseStart_5901775 : Nat := 118140960795 + 5901775 * 2 ^ 59
def prefixEnd_5901775 : Nat := 4983230072969 + 3 ^ 40 * 5901775 * 2
def baseEnd_5901775 : Nat := 3030447289688752011870737

theorem tailTrace_5901775 : CollatzResearch.WordTrace tailWord_5901775 prefixEnd_5901775 3030447289688752011870737 := by
  unfold tailWord_5901775
  simp only [CollatzResearch.WordTrace]
  refine ⟨215255418193884592768674779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143503612129256395179116519 215255418193884592768674779)
  ·
    refine ⟨322883127290826889153012169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215255418193884592768674779 322883127290826889153012169)
    ·
      refine ⟨242162345468120166864759127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322883127290826889153012169 242162345468120166864759127)
      ·
        refine ⟨363243518202180250297138691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242162345468120166864759127 363243518202180250297138691)
        ·
          refine ⟨544865277303270375445708037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363243518202180250297138691 544865277303270375445708037)
          ·
            refine ⟨102162239494363195396070257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 544865277303270375445708037 102162239494363195396070257)
            ·
              refine ⟨76621679620772396547052693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102162239494363195396070257 76621679620772396547052693)
              ·
                refine ⟨3591641232223706088143095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76621679620772396547052693 3591641232223706088143095)
                ·
                  refine ⟨5387461848335559132214643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591641232223706088143095 5387461848335559132214643)
                  ·
                    refine ⟨8081192772503338698321965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5387461848335559132214643 8081192772503338698321965)
                    ·
                      refine ⟨3030447289688752011870737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081192772503338698321965 3030447289688752011870737)
                      ·
                        rfl

theorem cell23_5901775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 1, 3].length) (baseStart_5901775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901775 prefixEnd_5901775 := by exact prefixLift 5901775
  have htrace : WordTrace (prefixWord ++ tailWord_5901775) baseStart_5901775 baseEnd_5901775 := by
    simpa [prefixWord, tailWord_5901775, baseEnd_5901775] using wordTrace_append hprefix tailTrace_5901775
  have hstable : (prefixWord ++ tailWord_5901775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901775).length < 2 ^ (prefixWord ++ tailWord_5901775).sum := by decide
  have hdescent : baseEnd_5901775 < baseStart_5901775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901782 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_5901782 : Nat := 118140960795 + 5901782 * 2 ^ 59
def prefixEnd_5901782 : Nat := 4983230072969 + 3 ^ 40 * 5901782 * 2
def baseEnd_5901782 : Nat := 336716764894814831609245

theorem tailTrace_5901782 : CollatzResearch.WordTrace tailWord_5901782 prefixEnd_5901782 336716764894814831609245 := by
  unfold tailWord_5901782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453479594053702060261225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143503782336572821976119733 13453479594053702060261225)
  ·
    refine ⟨10090109695540276545195919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13453479594053702060261225 10090109695540276545195919)
    ·
      refine ⟨15135164543310414817793879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090109695540276545195919 15135164543310414817793879)
      ·
        refine ⟨22702746814965622226690819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15135164543310414817793879 22702746814965622226690819)
        ·
          refine ⟨34054120222448433340036229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22702746814965622226690819 34054120222448433340036229)
          ·
            refine ⟨6385147541709081251256793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34054120222448433340036229 6385147541709081251256793)
            ·
              refine ⟨4788860656281810938442595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385147541709081251256793 4788860656281810938442595)
              ·
                refine ⟨7183290984422716407663893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788860656281810938442595 7183290984422716407663893)
                ·
                  refine ⟨336716764894814831609245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7183290984422716407663893 336716764894814831609245)
                  ·
                    rfl

theorem cell23_5901782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_5901782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901782 prefixEnd_5901782 := by exact prefixLift 5901782
  have htrace : WordTrace (prefixWord ++ tailWord_5901782) baseStart_5901782 baseEnd_5901782 := by
    simpa [prefixWord, tailWord_5901782, baseEnd_5901782] using wordTrace_append hprefix tailTrace_5901782
  have hstable : (prefixWord ++ tailWord_5901782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901782).length < 2 ^ (prefixWord ++ tailWord_5901782).sum := by decide
  have hdescent : baseEnd_5901782 < baseStart_5901782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901791 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 6]
def baseStart_5901791 : Nat := 118140960795 + 5901791 * 2 ^ 59
def prefixEnd_5901791 : Nat := 4983230072969 + 3 ^ 40 * 5901791 * 2
def baseEnd_5901791 : Nat := 1010151835126407983090221

theorem tailTrace_5901791 : CollatzResearch.WordTrace tailWord_5901791 prefixEnd_5901791 1010151835126407983090221 := by
  unfold tailWord_5901791
  simp only [CollatzResearch.WordTrace]
  refine ⟨215256001761826627501257227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143504001174551085000838151 215256001761826627501257227)
  ·
    refine ⟨322884002642739941251885841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215256001761826627501257227 322884002642739941251885841)
    ·
      refine ⟨242163001982054955938914381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322884002642739941251885841 242163001982054955938914381)
      ·
        refine ⟨90811125743270608477092893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242163001982054955938914381 90811125743270608477092893)
        ·
          refine ⟨34054172153726478178909835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90811125743270608477092893 34054172153726478178909835)
          ·
            refine ⟨51081258230589717268364753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34054172153726478178909835 51081258230589717268364753)
            ·
              refine ⟨38310943672942287951273565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51081258230589717268364753 38310943672942287951273565)
              ·
                refine ⟨14366603877353357981727587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38310943672942287951273565 14366603877353357981727587)
                ·
                  refine ⟨21549905816030036972591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14366603877353357981727587 21549905816030036972591381)
                  ·
                    refine ⟨1010151835126407983090221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21549905816030036972591381 1010151835126407983090221)
                    ·
                      rfl

theorem cell23_5901791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_5901791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901791 prefixEnd_5901791 := by exact prefixLift 5901791
  have htrace : WordTrace (prefixWord ++ tailWord_5901791) baseStart_5901791 baseEnd_5901791 := by
    simpa [prefixWord, tailWord_5901791, baseEnd_5901791] using wordTrace_append hprefix tailTrace_5901791
  have hstable : (prefixWord ++ tailWord_5901791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901791).length < 2 ^ (prefixWord ++ tailWord_5901791).sum := by decide
  have hdescent : baseEnd_5901791 < baseStart_5901791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901795 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 1, 5]
def baseStart_5901795 : Nat := 118140960795 + 5901795 * 2 ^ 59
def prefixEnd_5901795 : Nat := 4983230072969 + 3 ^ 40 * 5901795 * 2
def baseEnd_5901795 : Nat := 1010152519767280644540215

theorem tailTrace_5901795 : CollatzResearch.WordTrace tailWord_5901795 prefixEnd_5901795 1010152519767280644540215 := by
  unfold tailWord_5901795
  simp only [CollatzResearch.WordTrace]
  refine ⟨215256147653812136184402839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143504098435874757456268559 215256147653812136184402839)
  ·
    refine ⟨322884221480718204276604259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215256147653812136184402839 322884221480718204276604259)
    ·
      refine ⟨484326332221077306414906389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322884221480718204276604259 484326332221077306414906389)
      ·
        refine ⟨22702796822862998738198737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 484326332221077306414906389 22702796822862998738198737)
        ·
          refine ⟨17027097617147249053649053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22702796822862998738198737 17027097617147249053649053)
          ·
            refine ⟨6385161606430218395118395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17027097617147249053649053 6385161606430218395118395)
            ·
              refine ⟨9577742409645327592677593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385161606430218395118395 9577742409645327592677593)
              ·
                refine ⟨7183306807233995694508195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9577742409645327592677593 7183306807233995694508195)
                ·
                  refine ⟨10774960210850993541762293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7183306807233995694508195 10774960210850993541762293)
                  ·
                    refine ⟨1010152519767280644540215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10774960210850993541762293 1010152519767280644540215)
                    ·
                      rfl

theorem cell23_5901795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 5].length) (baseStart_5901795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901795 prefixEnd_5901795 := by exact prefixLift 5901795
  have htrace : WordTrace (prefixWord ++ tailWord_5901795) baseStart_5901795 baseEnd_5901795 := by
    simpa [prefixWord, tailWord_5901795, baseEnd_5901795] using wordTrace_append hprefix tailTrace_5901795
  have hstable : (prefixWord ++ tailWord_5901795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901795).length < 2 ^ (prefixWord ++ tailWord_5901795).sum := by decide
  have hdescent : baseEnd_5901795 < baseStart_5901795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901802 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_5901802 : Nat := 118140960795 + 5901802 * 2 ^ 59
def prefixEnd_5901802 : Nat := 4983230072969 + 3 ^ 40 * 5901802 * 2
def baseEnd_5901802 : Nat := 3030461153666423406233113

theorem tailTrace_5901802 : CollatzResearch.WordTrace tailWord_5901802 prefixEnd_5901802 3030461153666423406233113 := by
  unfold tailWord_5901802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53814100741196694094976915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143504268643191184253271773 53814100741196694094976915)
  ·
    refine ⟨80721151111795041142465373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53814100741196694094976915 80721151111795041142465373)
    ·
      refine ⟨30270431666923140428424515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80721151111795041142465373 30270431666923140428424515)
      ·
        refine ⟨45405647500384710642636773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30270431666923140428424515 45405647500384710642636773)
        ·
          refine ⟨8513558906322133245494395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45405647500384710642636773 8513558906322133245494395)
          ·
            refine ⟨12770338359483199868241593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8513558906322133245494395 12770338359483199868241593)
            ·
              refine ⟨9577753769612399901181195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12770338359483199868241593 9577753769612399901181195)
              ·
                refine ⟨14366630654418599851771793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9577753769612399901181195 14366630654418599851771793)
                ·
                  refine ⟨10774972990813949888828845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14366630654418599851771793 10774972990813949888828845)
                  ·
                    refine ⟨4040614871555231208310817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10774972990813949888828845 4040614871555231208310817)
                    ·
                      refine ⟨3030461153666423406233113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040614871555231208310817 3030461153666423406233113)
                      ·
                        rfl

theorem cell23_5901802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_5901802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901802 prefixEnd_5901802 := by exact prefixLift 5901802
  have htrace : WordTrace (prefixWord ++ tailWord_5901802) baseStart_5901802 baseEnd_5901802 := by
    simpa [prefixWord, tailWord_5901802, baseEnd_5901802] using wordTrace_append hprefix tailTrace_5901802
  have hstable : (prefixWord ++ tailWord_5901802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901802).length < 2 ^ (prefixWord ++ tailWord_5901802).sum := by decide
  have hdescent : baseEnd_5901802 < baseStart_5901802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901826 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5901826 : Nat := 118140960795 + 5901826 * 2 ^ 59
def prefixEnd_5901826 : Nat := 4983230072969 + 3 ^ 40 * 5901826 * 2
def baseEnd_5901826 : Nat := 3030473477202131312333003

theorem tailTrace_5901826 : CollatzResearch.WordTrace tailWord_5901826 prefixEnd_5901826 3030473477202131312333003 := by
  unfold tailWord_5901826
  simp only [CollatzResearch.WordTrace]
  refine ⟨53814319579174957119695333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143504852211133218985854221 53814319579174957119695333)
  ·
    refine ⟨10090184921095304459942875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53814319579174957119695333 10090184921095304459942875)
    ·
      refine ⟨15135277381642956689914313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090184921095304459942875 15135277381642956689914313)
      ·
        refine ⟨11351458036232217517435735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15135277381642956689914313 11351458036232217517435735)
        ·
          refine ⟨17027187054348326276153603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351458036232217517435735 17027187054348326276153603)
          ·
            refine ⟨25540780581522489414230405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17027187054348326276153603 25540780581522489414230405)
            ·
              refine ⟨4788896359035466765168201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25540780581522489414230405 4788896359035466765168201)
              ·
                refine ⟨3591672269276600073876151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788896359035466765168201 3591672269276600073876151)
                ·
                  refine ⟨5387508403914900110814227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591672269276600073876151 5387508403914900110814227)
                  ·
                    refine ⟨8081262605872350166221341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5387508403914900110814227 8081262605872350166221341)
                    ·
                      refine ⟨3030473477202131312333003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081262605872350166221341 3030473477202131312333003)
                      ·
                        rfl

theorem cell23_5901826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5901826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901826 prefixEnd_5901826 := by exact prefixLift 5901826
  have htrace : WordTrace (prefixWord ++ tailWord_5901826) baseStart_5901826 baseEnd_5901826 := by
    simpa [prefixWord, tailWord_5901826, baseEnd_5901826] using wordTrace_append hprefix tailTrace_5901826
  have hstable : (prefixWord ++ tailWord_5901826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901826).length < 2 ^ (prefixWord ++ tailWord_5901826).sum := by decide
  have hdescent : baseEnd_5901826 < baseStart_5901826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901861 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_5901861 : Nat := 118140960795 + 5901861 * 2 ^ 59
def prefixEnd_5901861 : Nat := 4983230072969 + 3 ^ 40 * 5901861 * 2
def baseEnd_5901861 : Nat := 3030491449025038675395341

theorem tailTrace_5901861 : CollatzResearch.WordTrace tailWord_5901861 prefixEnd_5901861 3030491449025038675395341 := by
  unfold tailWord_5901861
  simp only [CollatzResearch.WordTrace]
  refine ⟨215258554871573029456305437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143505703247715352970870291 215258554871573029456305437)
  ·
    refine ⟨80721958076839886046114539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215258554871573029456305437 80721958076839886046114539)
    ·
      refine ⟨121082937115259829069171809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80721958076839886046114539 121082937115259829069171809)
      ·
        refine ⟨90812202836444871801878857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121082937115259829069171809 90812202836444871801878857)
        ·
          refine ⟨68109152127333653851409143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90812202836444871801878857 68109152127333653851409143)
          ·
            refine ⟨102163728191000480777113715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68109152127333653851409143 102163728191000480777113715)
            ·
              refine ⟨153245592286500721165670573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102163728191000480777113715 153245592286500721165670573)
              ·
                refine ⟨57467097107437770437126465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153245592286500721165670573 57467097107437770437126465)
                ·
                  refine ⟨43100322830578327827844849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57467097107437770437126465 43100322830578327827844849)
                  ·
                    refine ⟨32325242122933745870883637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43100322830578327827844849 32325242122933745870883637)
                    ·
                      refine ⟨3030491449025038675395341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32325242122933745870883637 3030491449025038675395341)
                      ·
                        rfl

theorem cell23_5901861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_5901861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901861 prefixEnd_5901861 := by exact prefixLift 5901861
  have htrace : WordTrace (prefixWord ++ tailWord_5901861) baseStart_5901861 baseEnd_5901861 := by
    simpa [prefixWord, tailWord_5901861, baseEnd_5901861] using wordTrace_append hprefix tailTrace_5901861
  have hstable : (prefixWord ++ tailWord_5901861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901861).length < 2 ^ (prefixWord ++ tailWord_5901861).sum := by decide
  have hdescent : baseEnd_5901861 < baseStart_5901861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901891 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_5901891 : Nat := 118140960795 + 5901891 * 2 ^ 59
def prefixEnd_5901891 : Nat := 4983230072969 + 3 ^ 40 * 5901891 * 2
def baseEnd_5901891 : Nat := 3030506853444673558020203

theorem tailTrace_5901891 : CollatzResearch.WordTrace tailWord_5901891 prefixEnd_5901891 3030506853444673558020203 := by
  unfold tailWord_5901891
  simp only [CollatzResearch.WordTrace]
  refine ⟨215259649061464344579897527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143506432707642896386598351 215259649061464344579897527)
  ·
    refine ⟨322889473592196516869846291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215259649061464344579897527 322889473592196516869846291)
    ·
      refine ⟨484334210388294775304769437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322889473592196516869846291 484334210388294775304769437)
      ·
        refine ⟨181625328895610540739288539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484334210388294775304769437 181625328895610540739288539)
        ·
          refine ⟨272437993343415811108932809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181625328895610540739288539 272437993343415811108932809)
          ·
            refine ⟨204328495007561858331699607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272437993343415811108932809 204328495007561858331699607)
            ·
              refine ⟨306492742511342787497549411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204328495007561858331699607 306492742511342787497549411)
              ·
                refine ⟨459739113767014181246324117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306492742511342787497549411 459739113767014181246324117)
                ·
                  refine ⟨21550270957828789745921443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459739113767014181246324117 21550270957828789745921443)
                  ·
                    refine ⟨32325406436743184618882165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21550270957828789745921443 32325406436743184618882165)
                    ·
                      refine ⟨3030506853444673558020203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32325406436743184618882165 3030506853444673558020203)
                      ·
                        rfl

theorem cell23_5901891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_5901891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901891 prefixEnd_5901891 := by exact prefixLift 5901891
  have htrace : WordTrace (prefixWord ++ tailWord_5901891) baseStart_5901891 baseEnd_5901891 := by
    simpa [prefixWord, tailWord_5901891, baseEnd_5901891] using wordTrace_append hprefix tailTrace_5901891
  have hstable : (prefixWord ++ tailWord_5901891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901891).length < 2 ^ (prefixWord ++ tailWord_5901891).sum := by decide
  have hdescent : baseEnd_5901891 < baseStart_5901891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901908 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5901908 : Nat := 118140960795 + 5901908 * 2 ^ 59
def prefixEnd_5901908 : Nat := 4983230072969 + 3 ^ 40 * 5901908 * 2
def baseEnd_5901908 : Nat := 3030515582615799991507625

theorem tailTrace_5901908 : CollatzResearch.WordTrace tailWord_5901908 prefixEnd_5901908 3030515582615799991507625 := by
  unfold tailWord_5901908
  simp only [CollatzResearch.WordTrace]
  refine ⟨107630134551201378241633189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143506846068268504322177585 107630134551201378241633189)
  ·
    refine ⟨20180650228350258420306223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107630134551201378241633189 20180650228350258420306223)
    ·
      refine ⟨30270975342525387630459335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20180650228350258420306223 30270975342525387630459335)
      ·
        refine ⟨45406463013788081445689003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30270975342525387630459335 45406463013788081445689003)
        ·
          refine ⟨68109694520682122168533505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45406463013788081445689003 68109694520682122168533505)
          ·
            refine ⟨51082270890511591626400129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68109694520682122168533505 51082270890511591626400129)
            ·
              refine ⟨38311703167883693719800097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51082270890511591626400129 38311703167883693719800097)
              ·
                refine ⟨28733777375912770289850073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38311703167883693719800097 28733777375912770289850073)
                ·
                  refine ⟨21550333031934577717387555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28733777375912770289850073 21550333031934577717387555)
                  ·
                    refine ⟨32325499547901866576081333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21550333031934577717387555 32325499547901866576081333)
                    ·
                      refine ⟨3030515582615799991507625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32325499547901866576081333 3030515582615799991507625)
                      ·
                        rfl

theorem cell23_5901908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5901908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901908 prefixEnd_5901908 := by exact prefixLift 5901908
  have htrace : WordTrace (prefixWord ++ tailWord_5901908) baseStart_5901908 baseEnd_5901908 := by
    simpa [prefixWord, tailWord_5901908, baseEnd_5901908] using wordTrace_append hprefix tailTrace_5901908
  have hstable : (prefixWord ++ tailWord_5901908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901908).length < 2 ^ (prefixWord ++ tailWord_5901908).sum := by decide
  have hdescent : baseEnd_5901908 < baseStart_5901908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5901975 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 2, 5]
def baseStart_5901975 : Nat := 118140960795 + 5901975 * 2 ^ 59
def prefixEnd_5901975 : Nat := 4983230072969 + 3 ^ 40 * 5901975 * 2
def baseEnd_5901975 : Nat := 1010183328606550409789939

theorem tailTrace_5901975 : CollatzResearch.WordTrace tailWord_5901975 prefixEnd_5901975 1010183328606550409789939 := by
  unfold tailWord_5901975
  simp only [CollatzResearch.WordTrace]
  refine ⟨215262712793160026925955379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143508475195440017950636919 215262712793160026925955379)
  ·
    refine ⟨322894069189740040388933069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215262712793160026925955379 322894069189740040388933069)
    ·
      refine ⟨121085275946152515145849901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 322894069189740040388933069 121085275946152515145849901)
      ·
        refine ⟨45406978479807193179693713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121085275946152515145849901 45406978479807193179693713)
        ·
          refine ⟨34055233859855394884770285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45406978479807193179693713 34055233859855394884770285)
          ·
            refine ⟨12770712697445773081788857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34055233859855394884770285 12770712697445773081788857)
            ·
              refine ⟨9578034523084329811341643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12770712697445773081788857 9578034523084329811341643)
              ·
                refine ⟨14367051784626494717012465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578034523084329811341643 14367051784626494717012465)
                ·
                  refine ⟨10775288838469871037759349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14367051784626494717012465 10775288838469871037759349)
                  ·
                    refine ⟨1010183328606550409789939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10775288838469871037759349 1010183328606550409789939)
                    ·
                      rfl

theorem cell23_5901975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_5901975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5901975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5901975 prefixEnd_5901975 := by exact prefixLift 5901975
  have htrace : WordTrace (prefixWord ++ tailWord_5901975) baseStart_5901975 baseEnd_5901975 := by
    simpa [prefixWord, tailWord_5901975, baseEnd_5901975] using wordTrace_append hprefix tailTrace_5901975
  have hstable : (prefixWord ++ tailWord_5901975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5901975).length < 2 ^ (prefixWord ++ tailWord_5901975).sum := by decide
  have hdescent : baseEnd_5901975 < baseStart_5901975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5901975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902012 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5902012 : Nat := 118140960795 + 5902012 * 2 ^ 59
def prefixEnd_5902012 : Nat := 4983230072969 + 3 ^ 40 * 5902012 * 2
def baseEnd_5902012 : Nat := 3030568984603867584607147

theorem tailTrace_5902012 : CollatzResearch.WordTrace tailWord_5902012 prefixEnd_5902012 3030568984603867584607147 := by
  unfold tailWord_5902012
  simp only [CollatzResearch.WordTrace]
  refine ⟨107632031147012991122526145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143509374862683988163368193 107632031147012991122526145)
  ·
    refine ⟨80724023360259743341894609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107632031147012991122526145 80724023360259743341894609)
    ·
      refine ⟨60543017520194807506420957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80724023360259743341894609 60543017520194807506420957)
      ·
        refine ⟨22703631570073052814907859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60543017520194807506420957 22703631570073052814907859)
        ·
          refine ⟨34055447355109579222361789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22703631570073052814907859 34055447355109579222361789)
          ·
            refine ⟨12770792758166092208385671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34055447355109579222361789 12770792758166092208385671)
            ·
              refine ⟨19156189137249138312578507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770792758166092208385671 19156189137249138312578507)
              ·
                refine ⟨28734283705873707468867761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19156189137249138312578507 28734283705873707468867761)
                ·
                  refine ⟨21550712779405280601650821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28734283705873707468867761 21550712779405280601650821)
                  ·
                    refine ⟨4040758646138490112809529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21550712779405280601650821 4040758646138490112809529)
                    ·
                      refine ⟨3030568984603867584607147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040758646138490112809529 3030568984603867584607147)
                      ·
                        rfl

theorem cell23_5902012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5902012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902012 prefixEnd_5902012 := by exact prefixLift 5902012
  have htrace : WordTrace (prefixWord ++ tailWord_5902012) baseStart_5902012 baseEnd_5902012 := by
    simpa [prefixWord, tailWord_5902012, baseEnd_5902012] using wordTrace_append hprefix tailTrace_5902012
  have hstable : (prefixWord ++ tailWord_5902012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902012).length < 2 ^ (prefixWord ++ tailWord_5902012).sum := by decide
  have hdescent : baseEnd_5902012 < baseStart_5902012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902029 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5902029 : Nat := 118140960795 + 5902029 * 2 ^ 59
def prefixEnd_5902029 : Nat := 4983230072969 + 3 ^ 40 * 5902029 * 2
def baseEnd_5902029 : Nat := 3030577713774994018094569

theorem tailTrace_5902029 : CollatzResearch.WordTrace tailWord_5902029 prefixEnd_5902029 3030577713774994018094569 := by
  unfold tailWord_5902029
  simp only [CollatzResearch.WordTrace]
  refine ⟨215264682334964394148421141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143509788223309596098947427 215264682334964394148421141)
  ·
    refine ⟨10090531984451455975707241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215264682334964394148421141 10090531984451455975707241)
    ·
      refine ⟨7567898988338591981780431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10090531984451455975707241 7567898988338591981780431)
      ·
        refine ⟨11351848482507887972670647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567898988338591981780431 11351848482507887972670647)
        ·
          refine ⟨17027772723761831959005971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351848482507887972670647 17027772723761831959005971)
          ·
            refine ⟨25541659085642747938508957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17027772723761831959005971 25541659085642747938508957)
            ·
              refine ⟨9578122157116030476940859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25541659085642747938508957 9578122157116030476940859)
              ·
                refine ⟨14367183235674045715411289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578122157116030476940859 14367183235674045715411289)
                ·
                  refine ⟨10775387426755534286558467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14367183235674045715411289 10775387426755534286558467)
                  ·
                    refine ⟨16163081140133301429837701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10775387426755534286558467 16163081140133301429837701)
                    ·
                      refine ⟨3030577713774994018094569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16163081140133301429837701 3030577713774994018094569)
                      ·
                        rfl

theorem cell23_5902029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5902029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902029 prefixEnd_5902029 := by exact prefixLift 5902029
  have htrace : WordTrace (prefixWord ++ tailWord_5902029) baseStart_5902029 baseEnd_5902029 := by
    simpa [prefixWord, tailWord_5902029, baseEnd_5902029] using wordTrace_append hprefix tailTrace_5902029
  have hstable : (prefixWord ++ tailWord_5902029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902029).length < 2 ^ (prefixWord ++ tailWord_5902029).sum := by decide
  have hdescent : baseEnd_5902029 < baseStart_5902029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902112 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_5902112 : Nat := 118140960795 + 5902112 * 2 ^ 59
def prefixEnd_5902112 : Nat := 4983230072969 + 3 ^ 40 * 5902112 * 2
def baseEnd_5902112 : Nat := 1010206777556439064452229

theorem tailTrace_5902112 : CollatzResearch.WordTrace tailWord_5902112 prefixEnd_5902112 1010206777556439064452229 := by
  unfold tailWord_5902112
  simp only [CollatzResearch.WordTrace]
  refine ⟨107633854796831849661846295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143511806395775799549128393 107633854796831849661846295)
  ·
    refine ⟨161450782195247774492769443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107633854796831849661846295 161450782195247774492769443)
    ·
      refine ⟨242176173292871661739154165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161450782195247774492769443 242176173292871661739154165)
      ·
        refine ⟨22704016246206718288045703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242176173292871661739154165 22704016246206718288045703)
        ·
          refine ⟨34056024369310077432068555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22704016246206718288045703 34056024369310077432068555)
          ·
            refine ⟨51084036553965116148102833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34056024369310077432068555 51084036553965116148102833)
            ·
              refine ⟨38313027415473837111077125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51084036553965116148102833 38313027415473837111077125)
              ·
                refine ⟨7183692640401344458326961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38313027415473837111077125 7183692640401344458326961)
                ·
                  refine ⟨5387769480301008343745221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183692640401344458326961 5387769480301008343745221)
                  ·
                    refine ⟨1010206777556439064452229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387769480301008343745221 1010206777556439064452229)
                    ·
                      rfl

theorem cell23_5902112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_5902112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902112 prefixEnd_5902112 := by exact prefixLift 5902112
  have htrace : WordTrace (prefixWord ++ tailWord_5902112) baseStart_5902112 baseEnd_5902112 := by
    simpa [prefixWord, tailWord_5902112, baseEnd_5902112] using wordTrace_append hprefix tailTrace_5902112
  have hstable : (prefixWord ++ tailWord_5902112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902112).length < 2 ^ (prefixWord ++ tailWord_5902112).sum := by decide
  have hdescent : baseEnd_5902112 < baseStart_5902112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902129 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_5902129 : Nat := 118140960795 + 5902129 * 2 ^ 59
def prefixEnd_5902129 : Nat := 4983230072969 + 3 ^ 40 * 5902129 * 2
def baseEnd_5902129 : Nat := 1010209687280147875614703

theorem tailTrace_5902129 : CollatzResearch.WordTrace tailWord_5902129 prefixEnd_5902129 1010209687280147875614703 := by
  unfold tailWord_5902129
  simp only [CollatzResearch.WordTrace]
  refine ⟨215268329634602111227061441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143512219756401407484707627 215268329634602111227061441)
  ·
    refine ⟨161451247225951583420296081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215268329634602111227061441 161451247225951583420296081)
    ·
      refine ⟨121088435419463687565222061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161451247225951583420296081 121088435419463687565222061)
      ·
        refine ⟨45408163282298882836958273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121088435419463687565222061 45408163282298882836958273)
        ·
          refine ⟨34056122461724162127718705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45408163282298882836958273 34056122461724162127718705)
          ·
            refine ⟨25542091846293121595789029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34056122461724162127718705 25542091846293121595789029)
            ·
              refine ⟨4789142221179960299210443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25542091846293121595789029 4789142221179960299210443)
              ·
                refine ⟨7183713331769940448815665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789142221179960299210443 7183713331769940448815665)
                ·
                  refine ⟨5387784998827455336611749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183713331769940448815665 5387784998827455336611749)
                  ·
                    refine ⟨1010209687280147875614703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387784998827455336611749 1010209687280147875614703)
                    ·
                      rfl

theorem cell23_5902129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_5902129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902129 prefixEnd_5902129 := by exact prefixLift 5902129
  have htrace : WordTrace (prefixWord ++ tailWord_5902129) baseStart_5902129 baseEnd_5902129 := by
    simpa [prefixWord, tailWord_5902129, baseEnd_5902129] using wordTrace_append hprefix tailTrace_5902129
  have hstable : (prefixWord ++ tailWord_5902129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902129).length < 2 ^ (prefixWord ++ tailWord_5902129).sum := by decide
  have hdescent : baseEnd_5902129 < baseStart_5902129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902132 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5902132 : Nat := 118140960795 + 5902132 * 2 ^ 59
def prefixEnd_5902132 : Nat := 4983230072969 + 3 ^ 40 * 5902132 * 2
def baseEnd_5902132 : Nat := 3030630602282407115106595

theorem tailTrace_5902132 : CollatzResearch.WordTrace tailWord_5902132 prefixEnd_5902132 3030630602282407115106595 := by
  unfold tailWord_5902132
  simp only [CollatzResearch.WordTrace]
  refine ⟨107634219526795621369710325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143512292702394161826280433 107634219526795621369710325)
  ·
    refine ⟨10090708080637089503410343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107634219526795621369710325 10090708080637089503410343)
    ·
      refine ⟨15136062120955634255115515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090708080637089503410343 15136062120955634255115515)
      ·
        refine ⟨22704093181433451382673273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136062120955634255115515 22704093181433451382673273)
        ·
          refine ⟨17028069886075088537004955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22704093181433451382673273 17028069886075088537004955)
          ·
            refine ⟨25542104829112632805507433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17028069886075088537004955 25542104829112632805507433)
            ·
              refine ⟨19156578621834474604130575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25542104829112632805507433 19156578621834474604130575)
              ·
                refine ⟨28734867932751711906195863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19156578621834474604130575 28734867932751711906195863)
                ·
                  refine ⟨43102301899127567859293795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28734867932751711906195863 43102301899127567859293795)
                  ·
                    refine ⟨64653452848691351788940693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43102301899127567859293795 64653452848691351788940693)
                    ·
                      refine ⟨3030630602282407115106595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64653452848691351788940693 3030630602282407115106595)
                      ·
                        rfl

theorem cell23_5902132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5902132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902132 prefixEnd_5902132 := by exact prefixLift 5902132
  have htrace : WordTrace (prefixWord ++ tailWord_5902132) baseStart_5902132 baseEnd_5902132 := by
    simpa [prefixWord, tailWord_5902132, baseEnd_5902132] using wordTrace_append hprefix tailTrace_5902132
  have hstable : (prefixWord ++ tailWord_5902132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902132).length < 2 ^ (prefixWord ++ tailWord_5902132).sum := by decide
  have hdescent : baseEnd_5902132 < baseStart_5902132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902152 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_5902152 : Nat := 118140960795 + 5902152 * 2 ^ 59
def prefixEnd_5902152 : Nat := 4983230072969 + 3 ^ 40 * 5902152 * 2
def baseEnd_5902152 : Nat := 3030640871895497036856503

theorem tailTrace_5902152 : CollatzResearch.WordTrace tailWord_5902152 prefixEnd_5902152 3030640871895497036856503 := by
  unfold tailWord_5902152
  simp only [CollatzResearch.WordTrace]
  refine ⟨107634584256759393077574355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143512779009012524103432473 107634584256759393077574355)
  ·
    refine ⟨161451876385139089616361533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107634584256759393077574355 161451876385139089616361533)
    ·
      refine ⟨60544453644427158606135575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161451876385139089616361533 60544453644427158606135575)
      ·
        refine ⟨90816680466640737909203363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60544453644427158606135575 90816680466640737909203363)
        ·
          refine ⟨136225020699961106863805045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90816680466640737909203363 136225020699961106863805045)
          ·
            refine ⟨12771095690621353768481723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136225020699961106863805045 12771095690621353768481723)
            ·
              refine ⟨19156643535932030652722585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12771095690621353768481723 19156643535932030652722585)
              ·
                refine ⟨14367482651949022989541939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19156643535932030652722585 14367482651949022989541939)
                ·
                  refine ⟨21551223977923534484312909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14367482651949022989541939 21551223977923534484312909)
                  ·
                    refine ⟨8081708991721325431617341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21551223977923534484312909 8081708991721325431617341)
                    ·
                      refine ⟨3030640871895497036856503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081708991721325431617341 3030640871895497036856503)
                      ·
                        rfl

theorem cell23_5902152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_5902152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902152 prefixEnd_5902152 := by exact prefixLift 5902152
  have htrace : WordTrace (prefixWord ++ tailWord_5902152) baseStart_5902152 baseEnd_5902152 := by
    simpa [prefixWord, tailWord_5902152, baseEnd_5902152] using wordTrace_append hprefix tailTrace_5902152
  have hstable : (prefixWord ++ tailWord_5902152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902152).length < 2 ^ (prefixWord ++ tailWord_5902152).sum := by decide
  have hdescent : baseEnd_5902152 < baseStart_5902152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902156 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_5902156 : Nat := 118140960795 + 5902156 * 2 ^ 59
def prefixEnd_5902156 : Nat := 4983230072969 + 3 ^ 40 * 5902156 * 2
def baseEnd_5902156 : Nat := 3030642925818115021206485

theorem tailTrace_5902156 : CollatzResearch.WordTrace tailWord_5902156 prefixEnd_5902156 3030642925818115021206485 := by
  unfold tailWord_5902156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107634657202752147419147161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143512876270336196558862881 107634657202752147419147161)
  ·
    refine ⟨80725992902064110564360371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107634657202752147419147161 80725992902064110564360371)
    ·
      refine ⟨121088989353096165846540557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80725992902064110564360371 121088989353096165846540557)
      ·
        refine ⟨45408371007411062192452709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121088989353096165846540557 45408371007411062192452709)
        ·
          refine ⟨8514069563889574161084883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45408371007411062192452709 8514069563889574161084883)
          ·
            refine ⟨12771104345834361241627325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514069563889574161084883 12771104345834361241627325)
            ·
              refine ⟨4789164129687885465610247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12771104345834361241627325 4789164129687885465610247)
              ·
                refine ⟨7183746194531828198415371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789164129687885465610247 7183746194531828198415371)
                ·
                  refine ⟨10775619291797742297623057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7183746194531828198415371 10775619291797742297623057)
                  ·
                    refine ⟨8081714468848306723217293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10775619291797742297623057 8081714468848306723217293)
                    ·
                      refine ⟨3030642925818115021206485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081714468848306723217293 3030642925818115021206485)
                      ·
                        rfl

theorem cell23_5902156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_5902156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902156 prefixEnd_5902156 := by exact prefixLift 5902156
  have htrace : WordTrace (prefixWord ++ tailWord_5902156) baseStart_5902156 baseEnd_5902156 := by
    simpa [prefixWord, tailWord_5902156, baseEnd_5902156] using wordTrace_append hprefix tailTrace_5902156
  have hstable : (prefixWord ++ tailWord_5902156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902156).length < 2 ^ (prefixWord ++ tailWord_5902156).sum := by decide
  have hdescent : baseEnd_5902156 < baseStart_5902156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902169 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_5902169 : Nat := 118140960795 + 5902169 * 2 ^ 59
def prefixEnd_5902169 : Nat := 4983230072969 + 3 ^ 40 * 5902169 * 2
def baseEnd_5902169 : Nat := 3030649601066623470343925

theorem tailTrace_5902169 : CollatzResearch.WordTrace tailWord_5902169 prefixEnd_5902169 3030649601066623470343925 := by
  unfold tailWord_5902169
  simp only [CollatzResearch.WordTrace]
  refine ⟨215269788554457198058517561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143513192369638132039011707 215269788554457198058517561)
  ·
    refine ⟨161452341415842898543888171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215269788554457198058517561 161452341415842898543888171)
    ·
      refine ⟨242178512123764347815832257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161452341415842898543888171 242178512123764347815832257)
      ·
        refine ⟨181633884092823260861874193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242178512123764347815832257 181633884092823260861874193)
        ·
          refine ⟨136225413069617445646405645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181633884092823260861874193 136225413069617445646405645)
          ·
            refine ⟨51084529901106542117402117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136225413069617445646405645 51084529901106542117402117)
            ·
              refine ⟨9578349356457476647012897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51084529901106542117402117 9578349356457476647012897)
              ·
                refine ⟨7183762017343107485259673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9578349356457476647012897 7183762017343107485259673)
                ·
                  refine ⟨5387821513007330613944755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183762017343107485259673 5387821513007330613944755)
                  ·
                    refine ⟨8081732269510995920917133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5387821513007330613944755 8081732269510995920917133)
                    ·
                      refine ⟨3030649601066623470343925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081732269510995920917133 3030649601066623470343925)
                      ·
                        rfl

theorem cell23_5902169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_5902169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902169 prefixEnd_5902169 := by exact prefixLift 5902169
  have htrace : WordTrace (prefixWord ++ tailWord_5902169) baseStart_5902169 baseEnd_5902169 := by
    simpa [prefixWord, tailWord_5902169, baseEnd_5902169] using wordTrace_append hprefix tailTrace_5902169
  have hstable : (prefixWord ++ tailWord_5902169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902169).length < 2 ^ (prefixWord ++ tailWord_5902169).sum := by decide
  have hdescent : baseEnd_5902169 < baseStart_5902169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902175 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_5902175 : Nat := 118140960795 + 5902175 * 2 ^ 59
def prefixEnd_5902175 : Nat := 4983230072969 + 3 ^ 40 * 5902175 * 2
def baseEnd_5902175 : Nat := 3030652681950550446868897

theorem tailTrace_5902175 : CollatzResearch.WordTrace tailWord_5902175 prefixEnd_5902175 3030652681950550446868897 := by
  unfold tailWord_5902175
  simp only [CollatzResearch.WordTrace]
  refine ⟨215270007392435461083235979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143513338261623640722157319 215270007392435461083235979)
  ·
    refine ⟨322905011088653191624853969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215270007392435461083235979 322905011088653191624853969)
    ·
      refine ⟨242178758316489893718640477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322905011088653191624853969 242178758316489893718640477)
      ·
        refine ⟨90817034368683710144490179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242178758316489893718640477 90817034368683710144490179)
        ·
          refine ⟨136225551553025565216735269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90817034368683710144490179 136225551553025565216735269)
          ·
            refine ⟨25542290916192293478137863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136225551553025565216735269 25542290916192293478137863)
            ·
              refine ⟨38313436374288440217206795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25542290916192293478137863 38313436374288440217206795)
              ·
                refine ⟨57470154561432660325810193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38313436374288440217206795 57470154561432660325810193)
                ·
                  refine ⟨43102615921074495244357645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57470154561432660325810193 43102615921074495244357645)
                  ·
                    refine ⟨16163480970402935716634117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43102615921074495244357645 16163480970402935716634117)
                    ·
                      refine ⟨3030652681950550446868897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16163480970402935716634117 3030652681950550446868897)
                      ·
                        rfl

theorem cell23_5902175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_5902175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902175 prefixEnd_5902175 := by exact prefixLift 5902175
  have htrace : WordTrace (prefixWord ++ tailWord_5902175) baseStart_5902175 baseEnd_5902175 := by
    simpa [prefixWord, tailWord_5902175, baseEnd_5902175] using wordTrace_append hprefix tailTrace_5902175
  have hstable : (prefixWord ++ tailWord_5902175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902175).length < 2 ^ (prefixWord ++ tailWord_5902175).sum := by decide
  have hdescent : baseEnd_5902175 < baseStart_5902175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902186 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5902186 : Nat := 118140960795 + 5902186 * 2 ^ 59
def prefixEnd_5902186 : Nat := 4983230072969 + 3 ^ 40 * 5902186 * 2
def baseEnd_5902186 : Nat := 3030658330237749903831347

theorem tailTrace_5902186 : CollatzResearch.WordTrace tailWord_5902186 prefixEnd_5902186 3030658330237749903831347 := by
  unfold tailWord_5902186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53817602148848902490471603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143513605730263739974590941 53817602148848902490471603)
  ·
    refine ⟨80726403223273353735707405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53817602148848902490471603 80726403223273353735707405)
    ·
      refine ⟨30272401208727507650890277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80726403223273353735707405 30272401208727507650890277)
      ·
        refine ⟨5676075226636407684541927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30272401208727507650890277 5676075226636407684541927)
        ·
          refine ⟨8514112839954611526812891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676075226636407684541927 8514112839954611526812891)
          ·
            refine ⟨12771169259931917290219337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514112839954611526812891 12771169259931917290219337)
            ·
              refine ⟨9578376944948937967664503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12771169259931917290219337 9578376944948937967664503)
              ·
                refine ⟨14367565417423406951496755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578376944948937967664503 14367565417423406951496755)
                ·
                  refine ⟨21551348126135110427245133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14367565417423406951496755 21551348126135110427245133)
                  ·
                    refine ⟨8081755547300666410216925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21551348126135110427245133 8081755547300666410216925)
                    ·
                      refine ⟨3030658330237749903831347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081755547300666410216925 3030658330237749903831347)
                      ·
                        rfl

theorem cell23_5902186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5902186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902186 prefixEnd_5902186 := by exact prefixLift 5902186
  have htrace : WordTrace (prefixWord ++ tailWord_5902186) baseStart_5902186 baseEnd_5902186 := by
    simpa [prefixWord, tailWord_5902186, baseEnd_5902186] using wordTrace_append hprefix tailTrace_5902186
  have hstable : (prefixWord ++ tailWord_5902186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902186).length < 2 ^ (prefixWord ++ tailWord_5902186).sum := by decide
  have hdescent : baseEnd_5902186 < baseStart_5902186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902195 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3]
def baseStart_5902195 : Nat := 118140960795 + 5902195 * 2 ^ 59
def prefixEnd_5902195 : Nat := 4983230072969 + 3 ^ 40 * 5902195 * 2
def baseEnd_5902195 : Nat := 3030662951563640368618805

theorem tailTrace_5902195 : CollatzResearch.WordTrace tailWord_5902195 prefixEnd_5902195 3030662951563640368618805 := by
  unfold tailWord_5902195
  simp only [CollatzResearch.WordTrace]
  refine ⟨215270736852363004498964039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143513824568242002999309359 215270736852363004498964039)
  ·
    refine ⟨322906105278544506748446059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215270736852363004498964039 322906105278544506748446059)
    ·
      refine ⟨484359157917816760122669089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322906105278544506748446059 484359157917816760122669089)
      ·
        refine ⟨363269368438362570092001817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484359157917816760122669089 363269368438362570092001817)
        ·
          refine ⟨272452026328771927569001363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363269368438362570092001817 272452026328771927569001363)
          ·
            refine ⟨408678039493157891353502045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272452026328771927569001363 408678039493157891353502045)
            ·
              refine ⟨153254264809934209257563267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408678039493157891353502045 153254264809934209257563267)
              ·
                refine ⟨229881397214901313886344901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153254264809934209257563267 229881397214901313886344901)
                ·
                  refine ⟨43102761977793996353689669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229881397214901313886344901 43102761977793996353689669)
                  ·
                    refine ⟨8081767870836374316316813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43102761977793996353689669 8081767870836374316316813)
                    ·
                      refine ⟨3030662951563640368618805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081767870836374316316813 3030662951563640368618805)
                      ·
                        rfl

theorem cell23_5902195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_5902195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902195 prefixEnd_5902195 := by exact prefixLift 5902195
  have htrace : WordTrace (prefixWord ++ tailWord_5902195) baseStart_5902195 baseEnd_5902195 := by
    simpa [prefixWord, tailWord_5902195, baseEnd_5902195] using wordTrace_append hprefix tailTrace_5902195
  have hstable : (prefixWord ++ tailWord_5902195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902195).length < 2 ^ (prefixWord ++ tailWord_5902195).sum := by decide
  have hdescent : baseEnd_5902195 < baseStart_5902195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902205 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_5902205 : Nat := 118140960795 + 5902205 * 2 ^ 59
def prefixEnd_5902205 : Nat := 4983230072969 + 3 ^ 40 * 5902205 * 2
def baseEnd_5902205 : Nat := 3030668086370185329493759

theorem tailTrace_5902205 : CollatzResearch.WordTrace tailWord_5902205 prefixEnd_5902205 3030668086370185329493759 := by
  unfold tailWord_5902205
  simp only [CollatzResearch.WordTrace]
  refine ⟨215271101582326776206828069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143514067721551184137885379 215271101582326776206828069)
  ·
    refine ⟨40363331546686270538780263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215271101582326776206828069 40363331546686270538780263)
    ·
      refine ⟨60544997320029405808170395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40363331546686270538780263 60544997320029405808170395)
      ·
        refine ⟨90817495980044108712255593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60544997320029405808170395 90817495980044108712255593)
        ·
          refine ⟨68113121985033081534191695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90817495980044108712255593 68113121985033081534191695)
          ·
            refine ⟨102169682977549622301287543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68113121985033081534191695 102169682977549622301287543)
            ·
              refine ⟨153254524466324433451931315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102169682977549622301287543 153254524466324433451931315)
              ·
                refine ⟨229881786699486650177896973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153254524466324433451931315 229881786699486650177896973)
                ·
                  refine ⟨86205670012307493816711365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229881786699486650177896973 86205670012307493816711365)
                  ·
                    refine ⟨16163563127307655090633381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86205670012307493816711365 16163563127307655090633381)
                    ·
                      refine ⟨3030668086370185329493759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16163563127307655090633381 3030668086370185329493759)
                      ·
                        rfl

theorem cell23_5902205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_5902205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902205 prefixEnd_5902205 := by exact prefixLift 5902205
  have htrace : WordTrace (prefixWord ++ tailWord_5902205) baseStart_5902205 baseEnd_5902205 := by
    simpa [prefixWord, tailWord_5902205, baseEnd_5902205] using wordTrace_append hprefix tailTrace_5902205
  have hstable : (prefixWord ++ tailWord_5902205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902205).length < 2 ^ (prefixWord ++ tailWord_5902205).sum := by decide
  have hdescent : baseEnd_5902205 < baseStart_5902205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902282 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_5902282 : Nat := 118140960795 + 5902282 * 2 ^ 59
def prefixEnd_5902282 : Nat := 4983230072969 + 3 ^ 40 * 5902282 * 2
def baseEnd_5902282 : Nat := 3030707624380581528230905

theorem tailTrace_5902282 : CollatzResearch.WordTrace tailWord_5902282 prefixEnd_5902282 3030707624380581528230905 := by
  unfold tailWord_5902282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53818477500761954589345275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143515940002031878904920733 53818477500761954589345275)
  ·
    refine ⟨80727716251142931884017913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53818477500761954589345275 80727716251142931884017913)
    ·
      refine ⟨60545787188357198913013435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80727716251142931884017913 60545787188357198913013435)
      ·
        refine ⟨90818680782535798369520153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60545787188357198913013435 90818680782535798369520153)
        ·
          refine ⟨68114010586901848777140115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90818680782535798369520153 68114010586901848777140115)
          ·
            refine ⟨102171015880352773165710173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68114010586901848777140115 102171015880352773165710173)
            ·
              refine ⟨38314130955132289937141315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102171015880352773165710173 38314130955132289937141315)
              ·
                refine ⟨57471196432698434905711973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38314130955132289937141315 57471196432698434905711973)
                ·
                  refine ⟨10775849331130956544820995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57471196432698434905711973 10775849331130956544820995)
                  ·
                    refine ⟨16163773996696434817231493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10775849331130956544820995 16163773996696434817231493)
                    ·
                      refine ⟨3030707624380581528230905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16163773996696434817231493 3030707624380581528230905)
                      ·
                        rfl

theorem cell23_5902282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_5902282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902282 prefixEnd_5902282 := by exact prefixLift 5902282
  have htrace : WordTrace (prefixWord ++ tailWord_5902282) baseStart_5902282 baseEnd_5902282 := by
    simpa [prefixWord, tailWord_5902282, baseEnd_5902282] using wordTrace_append hprefix tailTrace_5902282
  have hstable : (prefixWord ++ tailWord_5902282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902282).length < 2 ^ (prefixWord ++ tailWord_5902282).sum := by decide
  have hdescent : baseEnd_5902282 < baseStart_5902282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902294 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5902294 : Nat := 118140960795 + 5902294 * 2 ^ 59
def prefixEnd_5902294 : Nat := 4983230072969 + 3 ^ 40 * 5902294 * 2
def baseEnd_5902294 : Nat := 3030713786148435481280851

theorem tailTrace_5902294 : CollatzResearch.WordTrace tailWord_5902294 prefixEnd_5902294 3030713786148435481280851 := by
  unfold tailWord_5902294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13454646729937771525426121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143516231786002896271211957 13454646729937771525426121)
  ·
    refine ⟨10090985047453328644069591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13454646729937771525426121 10090985047453328644069591)
    ·
      refine ⟨15136477571179992966104387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10090985047453328644069591 15136477571179992966104387)
      ·
        refine ⟨22704716356769989449156581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136477571179992966104387 22704716356769989449156581)
        ·
          refine ⟨4257134316894373021716859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22704716356769989449156581 4257134316894373021716859)
          ·
            refine ⟨6385701475341559532575289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257134316894373021716859 6385701475341559532575289)
            ·
              refine ⟨4789276106506169649431467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385701475341559532575289 4789276106506169649431467)
              ·
                refine ⟨7183914159759254474147201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789276106506169649431467 7183914159759254474147201)
                ·
                  refine ⟨5387935619819440855610401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7183914159759254474147201 5387935619819440855610401)
                  ·
                    refine ⟨4040951714864580641707801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387935619819440855610401 4040951714864580641707801)
                    ·
                      refine ⟨3030713786148435481280851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4040951714864580641707801 3030713786148435481280851)
                      ·
                        rfl

theorem cell23_5902294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5902294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902294 prefixEnd_5902294 := by exact prefixLift 5902294
  have htrace : WordTrace (prefixWord ++ tailWord_5902294) baseStart_5902294 baseEnd_5902294 := by
    simpa [prefixWord, tailWord_5902294, baseEnd_5902294] using wordTrace_append hprefix tailTrace_5902294
  have hstable : (prefixWord ++ tailWord_5902294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902294).length < 2 ^ (prefixWord ++ tailWord_5902294).sum := by decide
  have hdescent : baseEnd_5902294 < baseStart_5902294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902319 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_5902319 : Nat := 118140960795 + 5902319 * 2 ^ 59
def prefixEnd_5902319 : Nat := 4983230072969 + 3 ^ 40 * 5902319 * 2
def baseEnd_5902319 : Nat := 3030726623164797883468235

theorem tailTrace_5902319 : CollatzResearch.WordTrace tailWord_5902319 prefixEnd_5902319 3030726623164797883468235 := by
  unfold tailWord_5902319
  simp only [CollatzResearch.WordTrace]
  refine ⟨215275259503913773676478011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143516839669275849117652007 215275259503913773676478011)
  ·
    refine ⟨322912889255870660514717017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215275259503913773676478011 322912889255870660514717017)
    ·
      refine ⟨242184666941902995386037763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322912889255870660514717017 242184666941902995386037763)
      ·
        refine ⟨363277000412854493079056645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242184666941902995386037763 363277000412854493079056645)
        ·
          refine ⟨68114437577410217452323121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363277000412854493079056645 68114437577410217452323121)
          ·
            refine ⟨51085828183057663089242341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68114437577410217452323121 51085828183057663089242341)
            ·
              refine ⟨9578592784323311829232939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51085828183057663089242341 9578592784323311829232939)
              ·
                refine ⟨14367889176484967743849409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578592784323311829232939 14367889176484967743849409)
                ·
                  refine ⟨10775916882363725807887057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14367889176484967743849409 10775916882363725807887057)
                  ·
                    refine ⟨8081937661772794355915293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10775916882363725807887057 8081937661772794355915293)
                    ·
                      refine ⟨3030726623164797883468235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8081937661772794355915293 3030726623164797883468235)
                      ·
                        rfl

theorem cell23_5902319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_5902319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902319 prefixEnd_5902319 := by exact prefixLift 5902319
  have htrace : WordTrace (prefixWord ++ tailWord_5902319) baseStart_5902319 baseEnd_5902319 := by
    simpa [prefixWord, tailWord_5902319, baseEnd_5902319] using wordTrace_append hprefix tailTrace_5902319
  have hstable : (prefixWord ++ tailWord_5902319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902319).length < 2 ^ (prefixWord ++ tailWord_5902319).sum := by decide
  have hdescent : baseEnd_5902319 < baseStart_5902319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902343 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 1, 4]
def baseStart_5902343 : Nat := 118140960795 + 5902343 * 2 ^ 59
def prefixEnd_5902343 : Nat := 4983230072969 + 3 ^ 40 * 5902343 * 2
def baseEnd_5902343 : Nat := 1010246315566835263189375

theorem tailTrace_5902343 : CollatzResearch.WordTrace tailWord_5902343 prefixEnd_5902343 1010246315566835263189375 := by
  unfold tailWord_5902343
  simp only [CollatzResearch.WordTrace]
  refine ⟨215276134855826825775351683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143517423237217883850234455 215276134855826825775351683)
  ·
    refine ⟨322914202283740238663027525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215276134855826825775351683 322914202283740238663027525)
    ·
      refine ⟨60546412928201294749317661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322914202283740238663027525 60546412928201294749317661)
      ·
        refine ⟨22704904848075485530994123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60546412928201294749317661 22704904848075485530994123)
        ·
          refine ⟨34057357272113228296491185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22704904848075485530994123 34057357272113228296491185)
          ·
            refine ⟨25543017954084921222368389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34057357272113228296491185 25543017954084921222368389)
            ·
              refine ⟨4789315866390922729194073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25543017954084921222368389 4789315866390922729194073)
              ·
                refine ⟨3591986899793192046895555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789315866390922729194073 3591986899793192046895555)
                ·
                  refine ⟨5387980349689788070343333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591986899793192046895555 5387980349689788070343333)
                  ·
                    refine ⟨1010246315566835263189375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5387980349689788070343333 1010246315566835263189375)
                    ·
                      rfl

theorem cell23_5902343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_5902343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902343 prefixEnd_5902343 := by exact prefixLift 5902343
  have htrace : WordTrace (prefixWord ++ tailWord_5902343) baseStart_5902343 baseEnd_5902343 := by
    simpa [prefixWord, tailWord_5902343, baseEnd_5902343] using wordTrace_append hprefix tailTrace_5902343
  have hstable : (prefixWord ++ tailWord_5902343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902343).length < 2 ^ (prefixWord ++ tailWord_5902343).sum := by decide
  have hdescent : baseEnd_5902343 < baseStart_5902343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902386 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_5902386 : Nat := 118140960795 + 5902386 * 2 ^ 59
def prefixEnd_5902386 : Nat := 4983230072969 + 3 ^ 40 * 5902386 * 2
def baseEnd_5902386 : Nat := 1010253675456216373776809

theorem tailTrace_5902386 : CollatzResearch.WordTrace tailWord_5902386 prefixEnd_5902386 1010253675456216373776809 := by
  unfold tailWord_5902386
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819425798667761029791753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143518468796447362746111341 53819425798667761029791753)
  ·
    refine ⟨40364569349000820772343815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53819425798667761029791753 40364569349000820772343815)
    ·
      refine ⟨60546854023501231158515723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40364569349000820772343815 60546854023501231158515723)
      ·
        refine ⟨90820281035251846737773585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60546854023501231158515723 90820281035251846737773585)
        ·
          refine ⟨68115210776438885053330189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90820281035251846737773585 68115210776438885053330189)
          ·
            refine ⟨25543204041164581894998821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68115210776438885053330189 25543204041164581894998821)
            ·
              refine ⟨4789350757718359105312279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25543204041164581894998821 4789350757718359105312279)
              ·
                refine ⟨7184026136577538657968419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789350757718359105312279 7184026136577538657968419)
                ·
                  refine ⟨10776039204866307986952629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184026136577538657968419 10776039204866307986952629)
                  ·
                    refine ⟨1010253675456216373776809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10776039204866307986952629 1010253675456216373776809)
                    ·
                      rfl

theorem cell23_5902386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_5902386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902386 prefixEnd_5902386 := by exact prefixLift 5902386
  have htrace : WordTrace (prefixWord ++ tailWord_5902386) baseStart_5902386 baseEnd_5902386 := by
    simpa [prefixWord, tailWord_5902386, baseEnd_5902386] using wordTrace_append hprefix tailTrace_5902386
  have hstable : (prefixWord ++ tailWord_5902386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902386).length < 2 ^ (prefixWord ++ tailWord_5902386).sum := by decide
  have hdescent : baseEnd_5902386 < baseStart_5902386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902426 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_5902426 : Nat := 118140960795 + 5902426 * 2 ^ 59
def prefixEnd_5902426 : Nat := 4983230072969 + 3 ^ 40 * 5902426 * 2
def baseEnd_5902426 : Nat := 3030781565594828964830243

theorem tailTrace_5902426 : CollatzResearch.WordTrace tailWord_5902426 prefixEnd_5902426 3030781565594828964830243 := by
  unfold tailWord_5902426
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819790528631532737655783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143519441409684087300415421 53819790528631532737655783)
  ·
    refine ⟨80729685792947299106483675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53819790528631532737655783 80729685792947299106483675)
    ·
      refine ⟨121094528689420948659725513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80729685792947299106483675 121094528689420948659725513)
      ·
        refine ⟨90820896517065711494794135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121094528689420948659725513 90820896517065711494794135)
        ·
          refine ⟨136231344775598567242191203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90820896517065711494794135 136231344775598567242191203)
          ·
            refine ⟨204347017163397850863286805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136231344775598567242191203 204347017163397850863286805)
            ·
              refine ⟨9578766429534274259216569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204347017163397850863286805 9578766429534274259216569)
              ·
                refine ⟨7184074822150705694412427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9578766429534274259216569 7184074822150705694412427)
                ·
                  refine ⟨10776112233226058541618641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184074822150705694412427 10776112233226058541618641)
                  ·
                    refine ⟨8082084174919543906213981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10776112233226058541618641 8082084174919543906213981)
                    ·
                      refine ⟨3030781565594828964830243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082084174919543906213981 3030781565594828964830243)
                      ·
                        rfl

theorem cell23_5902426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_5902426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902426 prefixEnd_5902426 := by exact prefixLift 5902426
  have htrace : WordTrace (prefixWord ++ tailWord_5902426) baseStart_5902426 baseEnd_5902426 := by
    simpa [prefixWord, tailWord_5902426, baseEnd_5902426] using wordTrace_append hprefix tailTrace_5902426
  have hstable : (prefixWord ++ tailWord_5902426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902426).length < 2 ^ (prefixWord ++ tailWord_5902426).sum := by decide
  have hdescent : baseEnd_5902426 < baseStart_5902426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902434 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5902434 : Nat := 118140960795 + 5902434 * 2 ^ 59
def prefixEnd_5902434 : Nat := 4983230072969 + 3 ^ 40 * 5902434 * 2
def baseEnd_5902434 : Nat := 3030785673440064933530207

theorem tailTrace_5902434 : CollatzResearch.WordTrace tailWord_5902434 prefixEnd_5902434 3030785673440064933530207 := by
  unfold tailWord_5902434
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819863474624287079228589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143519635932331432211276237 53819863474624287079228589)
  ·
    refine ⟨20182448802984107654710721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53819863474624287079228589 20182448802984107654710721)
    ·
      refine ⟨15136836602238080741033041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20182448802984107654710721 15136836602238080741033041)
      ·
        refine ⟨11352627451678560555774781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15136836602238080741033041 11352627451678560555774781)
        ·
          refine ⟨4257235294379460208415543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11352627451678560555774781 4257235294379460208415543)
          ·
            refine ⟨6385852941569190312623315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257235294379460208415543 6385852941569190312623315)
            ·
              refine ⟨9578779412353785468934973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385852941569190312623315 9578779412353785468934973)
              ·
                refine ⟨3592042279632669550850615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9578779412353785468934973 3592042279632669550850615)
                ·
                  refine ⟨5388063419449004326275923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592042279632669550850615 5388063419449004326275923)
                  ·
                    refine ⟨8082095129173506489413885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388063419449004326275923 8082095129173506489413885)
                    ·
                      refine ⟨3030785673440064933530207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082095129173506489413885 3030785673440064933530207)
                      ·
                        rfl

theorem cell23_5902434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5902434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902434 prefixEnd_5902434 := by exact prefixLift 5902434
  have htrace : WordTrace (prefixWord ++ tailWord_5902434) baseStart_5902434 baseEnd_5902434 := by
    simpa [prefixWord, tailWord_5902434, baseEnd_5902434] using wordTrace_append hprefix tailTrace_5902434
  have hstable : (prefixWord ++ tailWord_5902434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902434).length < 2 ^ (prefixWord ++ tailWord_5902434).sum := by decide
  have hdescent : baseEnd_5902434 < baseStart_5902434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902439 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_5902439 : Nat := 118140960795 + 5902439 * 2 ^ 59
def prefixEnd_5902439 : Nat := 4983230072969 + 3 ^ 40 * 5902439 * 2
def baseEnd_5902439 : Nat := 3030788240843337413967683

theorem tailTrace_5902439 : CollatzResearch.WordTrace tailWord_5902439 prefixEnd_5902439 3030788240843337413967683 := by
  unfold tailWord_5902439
  simp only [CollatzResearch.WordTrace]
  refine ⟨215279636263479034170846371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143519757508986022780564247 215279636263479034170846371)
  ·
    refine ⟨322919454395218551256269557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215279636263479034170846371 322919454395218551256269557)
    ·
      refine ⟨30273698849551739180275271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 322919454395218551256269557 30273698849551739180275271)
      ·
        refine ⟨45410548274327608770412907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30273698849551739180275271 45410548274327608770412907)
        ·
          refine ⟨68115822411491413155619361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45410548274327608770412907 68115822411491413155619361)
          ·
            refine ⟨51086866808618559866714521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68115822411491413155619361 51086866808618559866714521)
            ·
              refine ⟨38315150106463919900035891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51086866808618559866714521 38315150106463919900035891)
              ·
                refine ⟨57472725159695879850053837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38315150106463919900035891 57472725159695879850053837)
                ·
                  refine ⟨21552271934885954943770189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57472725159695879850053837 21552271934885954943770189)
                  ·
                    refine ⟨8082101975582233103913821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21552271934885954943770189 8082101975582233103913821)
                    ·
                      refine ⟨3030788240843337413967683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082101975582233103913821 3030788240843337413967683)
                      ·
                        rfl

theorem cell23_5902439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_5902439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902439 prefixEnd_5902439 := by exact prefixLift 5902439
  have htrace : WordTrace (prefixWord ++ tailWord_5902439) baseStart_5902439 baseEnd_5902439 := by
    simpa [prefixWord, tailWord_5902439, baseEnd_5902439] using wordTrace_append hprefix tailTrace_5902439
  have hstable : (prefixWord ++ tailWord_5902439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902439).length < 2 ^ (prefixWord ++ tailWord_5902439).sum := by decide
  have hdescent : baseEnd_5902439 < baseStart_5902439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902456 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_5902456 : Nat := 118140960795 + 5902456 * 2 ^ 59
def prefixEnd_5902456 : Nat := 4983230072969 + 3 ^ 40 * 5902456 * 2
def baseEnd_5902456 : Nat := 3030796970014463847455105

theorem tailTrace_5902456 : CollatzResearch.WordTrace tailWord_5902456 prefixEnd_5902456 3030796970014463847455105 := by
  unfold tailWord_5902456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107640128152208723037107611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143520170869611630716143481 107640128152208723037107611)
  ·
    refine ⟨161460192228313084555661417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107640128152208723037107611 161460192228313084555661417)
    ·
      refine ⟨121095144171234813416746063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161460192228313084555661417 121095144171234813416746063)
      ·
        refine ⟨181642716256852220125119095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121095144171234813416746063 181642716256852220125119095)
        ·
          refine ⟨272464074385278330187678643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181642716256852220125119095 272464074385278330187678643)
          ·
            refine ⟨408696111577917495281517965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272464074385278330187678643 408696111577917495281517965)
            ·
              refine ⟨153261041841719060730569237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408696111577917495281517965 153261041841719060730569237)
              ·
                refine ⟨7184111336330580971745433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153261041841719060730569237 7184111336330580971745433)
                ·
                  refine ⟨5388083502247935728809075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7184111336330580971745433 5388083502247935728809075)
                  ·
                    refine ⟨8082125253371903593213613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388083502247935728809075 8082125253371903593213613)
                    ·
                      refine ⟨3030796970014463847455105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082125253371903593213613 3030796970014463847455105)
                      ·
                        rfl

theorem cell23_5902456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_5902456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902456 prefixEnd_5902456 := by exact prefixLift 5902456
  have htrace : WordTrace (prefixWord ++ tailWord_5902456) baseStart_5902456 baseEnd_5902456 := by
    simpa [prefixWord, tailWord_5902456, baseEnd_5902456] using wordTrace_append hprefix tailTrace_5902456
  have hstable : (prefixWord ++ tailWord_5902456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902456).length < 2 ^ (prefixWord ++ tailWord_5902456).sum := by decide
  have hdescent : baseEnd_5902456 < baseStart_5902456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902457 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 1, 2, 2]
def baseStart_5902457 : Nat := 118140960795 + 5902457 * 2 ^ 59
def prefixEnd_5902457 : Nat := 4983230072969 + 3 ^ 40 * 5902457 * 2
def baseEnd_5902457 : Nat := 3030797483495118343542601

theorem tailTrace_5902457 : CollatzResearch.WordTrace tailWord_5902457 prefixEnd_5902457 3030797483495118343542601 := by
  unfold tailWord_5902457
  simp only [CollatzResearch.WordTrace]
  refine ⟨215280292777413823245001625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143520195184942548830001083 215280292777413823245001625)
  ·
    refine ⟨161460219583060367433751219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215280292777413823245001625 161460219583060367433751219)
    ·
      refine ⟨242190329374590551150626829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161460219583060367433751219 242190329374590551150626829)
      ·
        refine ⟨90821373515471456681485061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242190329374590551150626829 90821373515471456681485061)
        ·
          refine ⟨17029007534150898127778449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90821373515471456681485061 17029007534150898127778449)
          ·
            refine ⟨12771755650613173595833837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17029007534150898127778449 12771755650613173595833837)
            ·
              refine ⟨4789408368979940098437689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12771755650613173595833837 4789408368979940098437689)
              ·
                refine ⟨3592056276734955073828267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789408368979940098437689 3592056276734955073828267)
                ·
                  refine ⟨5388084415102432610742401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592056276734955073828267 5388084415102432610742401)
                  ·
                    refine ⟨4041063311326824458056801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5388084415102432610742401 4041063311326824458056801)
                    ·
                      refine ⟨3030797483495118343542601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041063311326824458056801 3030797483495118343542601)
                      ·
                        rfl

theorem cell23_5902457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_5902457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902457 prefixEnd_5902457 := by exact prefixLift 5902457
  have htrace : WordTrace (prefixWord ++ tailWord_5902457) baseStart_5902457 baseEnd_5902457 := by
    simpa [prefixWord, tailWord_5902457, baseEnd_5902457] using wordTrace_append hprefix tailTrace_5902457
  have hstable : (prefixWord ++ tailWord_5902457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902457).length < 2 ^ (prefixWord ++ tailWord_5902457).sum := by decide
  have hdescent : baseEnd_5902457 < baseStart_5902457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 10, 2]
def baseStart_5902479 : Nat := 118140960795 + 5902479 * 2 ^ 59
def prefixEnd_5902479 : Nat := 4983230072969 + 3 ^ 40 * 5902479 * 2
def baseEnd_5902479 : Nat := 3030808780069517257467499

theorem tailTrace_5902479 : CollatzResearch.WordTrace tailWord_5902479 prefixEnd_5902479 3030808780069517257467499 := by
  unfold tailWord_5902479
  simp only [CollatzResearch.WordTrace]
  refine ⟨215281095183334121002302491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143520730122222747334868327 215281095183334121002302491)
  ·
    refine ⟨322921642775001181503453737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215281095183334121002302491 322921642775001181503453737)
    ·
      refine ⟨242191232081250886127590303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322921642775001181503453737 242191232081250886127590303)
      ·
        refine ⟨363286848121876329191385455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242191232081250886127590303 363286848121876329191385455)
        ·
          refine ⟨544930272182814493787078183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363286848121876329191385455 544930272182814493787078183)
          ·
            refine ⟨817395408274221740680617275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544930272182814493787078183 817395408274221740680617275)
            ·
              refine ⟨1226093112411332611020925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817395408274221740680617275 1226093112411332611020925913)
              ·
                refine ⟨919569834308499458265694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226093112411332611020925913 919569834308499458265694435)
                ·
                  refine ⟨1379354751462749187398541653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919569834308499458265694435 1379354751462749187398541653)
                  ·
                    refine ⟨4041078373426023009956665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1379354751462749187398541653 4041078373426023009956665)
                    ·
                      refine ⟨3030808780069517257467499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041078373426023009956665 3030808780069517257467499)
                      ·
                        rfl

theorem cell23_5902479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 10, 2].length) (baseStart_5902479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902479 prefixEnd_5902479 := by exact prefixLift 5902479
  have htrace : WordTrace (prefixWord ++ tailWord_5902479) baseStart_5902479 baseEnd_5902479 := by
    simpa [prefixWord, tailWord_5902479, baseEnd_5902479] using wordTrace_append hprefix tailTrace_5902479
  have hstable : (prefixWord ++ tailWord_5902479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902479).length < 2 ^ (prefixWord ++ tailWord_5902479).sum := by decide
  have hdescent : baseEnd_5902479 < baseStart_5902479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902496 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2]
def baseStart_5902496 : Nat := 118140960795 + 5902496 * 2 ^ 59
def prefixEnd_5902496 : Nat := 4983230072969 + 3 ^ 40 * 5902496 * 2
def baseEnd_5902496 : Nat := 3030817509240643690954921

theorem tailTrace_5902496 : CollatzResearch.WordTrace tailWord_5902496 prefixEnd_5902496 3030817509240643690954921 := by
  unfold tailWord_5902496
  simp only [CollatzResearch.WordTrace]
  refine ⟨107640857612136266452835671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143521143482848355270447561 107640857612136266452835671)
  ·
    refine ⟨161461286418204399679253507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107640857612136266452835671 161461286418204399679253507)
    ·
      refine ⟨242191929627306599518880261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161461286418204399679253507 242191929627306599518880261)
      ·
        refine ⟨45410986805119987409790049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242191929627306599518880261 45410986805119987409790049)
        ·
          refine ⟨34058240103839990557342537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45410986805119987409790049 34058240103839990557342537)
          ·
            refine ⟨25543680077879992918006903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34058240103839990557342537 25543680077879992918006903)
            ·
              refine ⟨38315520116819989377010355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25543680077879992918006903 38315520116819989377010355)
              ·
                refine ⟨57473280175229984065515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38315520116819989377010355 57473280175229984065515533)
                ·
                  refine ⟨21552480065711244024568325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57473280175229984065515533 21552480065711244024568325)
                  ·
                    refine ⟨4041090012320858254606561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21552480065711244024568325 4041090012320858254606561)
                    ·
                      refine ⟨3030817509240643690954921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041090012320858254606561 3030817509240643690954921)
                      ·
                        rfl

theorem cell23_5902496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_5902496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902496 prefixEnd_5902496 := by exact prefixLift 5902496
  have htrace : WordTrace (prefixWord ++ tailWord_5902496) baseStart_5902496 baseEnd_5902496 := by
    simpa [prefixWord, tailWord_5902496, baseEnd_5902496] using wordTrace_append hprefix tailTrace_5902496
  have hstable : (prefixWord ++ tailWord_5902496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902496).length < 2 ^ (prefixWord ++ tailWord_5902496).sum := by decide
  have hdescent : baseEnd_5902496 < baseStart_5902496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902606 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5902606 : Nat := 118140960795 + 5902606 * 2 ^ 59
def prefixEnd_5902606 : Nat := 4983230072969 + 3 ^ 40 * 5902606 * 2
def baseEnd_5902606 : Nat := 3030873992112638260579415

theorem tailTrace_5902606 : CollatzResearch.WordTrace tailWord_5902606 prefixEnd_5902606 3030873992112638260579415 := by
  unfold tailWord_5902606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26910715906734252711521959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143523818169249347794783781 26910715906734252711521959)
  ·
    refine ⟨40366073860101379067282939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26910715906734252711521959 40366073860101379067282939)
    ·
      refine ⟨60549110790152068600924409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40366073860101379067282939 60549110790152068600924409)
      ·
        refine ⟨45411833092614051450693307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60549110790152068600924409 45411833092614051450693307)
        ·
          refine ⟨68117749638921077176039961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45411833092614051450693307 68117749638921077176039961)
          ·
            refine ⟨51088312229190807882029971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68117749638921077176039961 51088312229190807882029971)
            ·
              refine ⟨76632468343786211823044957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51088312229190807882029971 76632468343786211823044957)
              ·
                refine ⟨28737175628919829433641859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76632468343786211823044957 28737175628919829433641859)
                ·
                  refine ⟨43105763443379744150462789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28737175628919829433641859 43105763443379744150462789)
                  ·
                    refine ⟨8082330645633702028211773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43105763443379744150462789 8082330645633702028211773)
                    ·
                      refine ⟨3030873992112638260579415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082330645633702028211773 3030873992112638260579415)
                      ·
                        rfl

theorem cell23_5902606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5902606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902606 prefixEnd_5902606 := by exact prefixLift 5902606
  have htrace : WordTrace (prefixWord ++ tailWord_5902606) baseStart_5902606 baseEnd_5902606 := by
    simpa [prefixWord, tailWord_5902606, baseEnd_5902606] using wordTrace_append hprefix tailTrace_5902606
  have hstable : (prefixWord ++ tailWord_5902606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902606).length < 2 ^ (prefixWord ++ tailWord_5902606).sum := by decide
  have hdescent : baseEnd_5902606 < baseStart_5902606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902609 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 8]
def baseStart_5902609 : Nat := 118140960795 + 5902609 * 2 ^ 59
def prefixEnd_5902609 : Nat := 4983230072969 + 3 ^ 40 * 5902609 * 2
def baseEnd_5902609 : Nat := 336763948061622416537989

theorem tailTrace_5902609 : CollatzResearch.WordTrace tailWord_5902609 prefixEnd_5902609 336763948061622416537989 := by
  unfold tailWord_5902609
  simp only [CollatzResearch.WordTrace]
  refine ⟨215285836672863153204534881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143523891115242102136356587 215285836672863153204534881)
  ·
    refine ⟨161464377504647364903401161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215285836672863153204534881 161464377504647364903401161)
    ·
      refine ⟨121098283128485523677550871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161464377504647364903401161 121098283128485523677550871)
      ·
        refine ⟨181647424692728285516326307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121098283128485523677550871 181647424692728285516326307)
        ·
          refine ⟨272471137039092428274489461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181647424692728285516326307 272471137039092428274489461)
          ·
            refine ⟨25544169097414915150733387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272471137039092428274489461 25544169097414915150733387)
            ·
              refine ⟨38316253646122372726100081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25544169097414915150733387 38316253646122372726100081)
              ·
                refine ⟨28737190234591779544575061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38316253646122372726100081 28737190234591779544575061)
                ·
                  refine ⟨336763948061622416537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28737190234591779544575061 336763948061622416537989)
                  ·
                    rfl

theorem cell23_5902609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_5902609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902609 prefixEnd_5902609 := by exact prefixLift 5902609
  have htrace : WordTrace (prefixWord ++ tailWord_5902609) baseStart_5902609 baseEnd_5902609 := by
    simpa [prefixWord, tailWord_5902609, baseEnd_5902609] using wordTrace_append hprefix tailTrace_5902609
  have hstable : (prefixWord ++ tailWord_5902609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902609).length < 2 ^ (prefixWord ++ tailWord_5902609).sum := by decide
  have hdescent : baseEnd_5902609 < baseStart_5902609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902623 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_5902623 : Nat := 118140960795 + 5902623 * 2 ^ 59
def prefixEnd_5902623 : Nat := 4983230072969 + 3 ^ 40 * 5902623 * 2
def baseEnd_5902623 : Nat := 3030882721283764694066837

theorem tailTrace_5902623 : CollatzResearch.WordTrace tailWord_5902623 prefixEnd_5902623 3030882721283764694066837 := by
  unfold tailWord_5902623
  simp only [CollatzResearch.WordTrace]
  refine ⟨215286347294812433595544523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143524231529874955730363015 215286347294812433595544523)
  ·
    refine ⟨322929520942218650393316785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215286347294812433595544523 322929520942218650393316785)
    ·
      refine ⟨242197140706663987794987589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322929520942218650393316785 242197140706663987794987589)
      ·
        refine ⟨45411963882499497711560173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242197140706663987794987589 45411963882499497711560173)
        ·
          refine ⟨17029486455937311641835065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45411963882499497711560173 17029486455937311641835065)
          ·
            refine ⟨12772114841952983731376299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17029486455937311641835065 12772114841952983731376299)
            ·
              refine ⟨19158172262929475597064449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772114841952983731376299 19158172262929475597064449)
              ·
                refine ⟨14368629197197106697798337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19158172262929475597064449 14368629197197106697798337)
                ·
                  refine ⟨10776471897897830023348753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14368629197197106697798337 10776471897897830023348753)
                  ·
                    refine ⟨8082353923423372517511565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10776471897897830023348753 8082353923423372517511565)
                    ·
                      refine ⟨3030882721283764694066837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082353923423372517511565 3030882721283764694066837)
                      ·
                        rfl

theorem cell23_5902623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_5902623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902623 prefixEnd_5902623 := by exact prefixLift 5902623
  have htrace : WordTrace (prefixWord ++ tailWord_5902623) baseStart_5902623 baseEnd_5902623 := by
    simpa [prefixWord, tailWord_5902623, baseEnd_5902623] using wordTrace_append hprefix tailTrace_5902623
  have hstable : (prefixWord ++ tailWord_5902623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902623).length < 2 ^ (prefixWord ++ tailWord_5902623).sum := by decide
  have hdescent : baseEnd_5902623 < baseStart_5902623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902626 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_5902626 : Nat := 118140960795 + 5902626 * 2 ^ 59
def prefixEnd_5902626 : Nat := 4983230072969 + 3 ^ 40 * 5902626 * 2
def baseEnd_5902626 : Nat := 336764917969525353592147

theorem tailTrace_5902626 : CollatzResearch.WordTrace tailWord_5902626 prefixEnd_5902626 336764917969525353592147 := by
  unfold tailWord_5902626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53821614178450391276975933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143524304475867710071935821 53821614178450391276975933)
  ·
    refine ⟨20183105316918896728865975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53821614178450391276975933 20183105316918896728865975)
    ·
      refine ⟨30274657975378345093298963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20183105316918896728865975 30274657975378345093298963)
      ·
        refine ⟨45411986963067517639948445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30274657975378345093298963 45411986963067517639948445)
        ·
          refine ⟨17029495111150319114980667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45411986963067517639948445 17029495111150319114980667)
          ·
            refine ⟨25544242666725478672471001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029495111150319114980667 25544242666725478672471001)
            ·
              refine ⟨19158182000044109004353251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25544242666725478672471001 19158182000044109004353251)
              ·
                refine ⟨28737273000066163506529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19158182000044109004353251 28737273000066163506529877)
                ·
                  refine ⟨336764917969525353592147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28737273000066163506529877 336764917969525353592147)
                  ·
                    rfl

theorem cell23_5902626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_5902626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902626 prefixEnd_5902626 := by exact prefixLift 5902626
  have htrace : WordTrace (prefixWord ++ tailWord_5902626) baseStart_5902626 baseEnd_5902626 := by
    simpa [prefixWord, tailWord_5902626, baseEnd_5902626] using wordTrace_append hprefix tailTrace_5902626
  have hstable : (prefixWord ++ tailWord_5902626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902626).length < 2 ^ (prefixWord ++ tailWord_5902626).sum := by decide
  have hdescent : baseEnd_5902626 < baseStart_5902626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902656 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_5902656 : Nat := 118140960795 + 5902656 * 2 ^ 59
def prefixEnd_5902656 : Nat := 4983230072969 + 3 ^ 40 * 5902656 * 2
def baseEnd_5902656 : Nat := 1010299888715121021651395

theorem tailTrace_5902656 : CollatzResearch.WordTrace tailWord_5902656 prefixEnd_5902656 1010299888715121021651395 := by
  unfold tailWord_5902656
  simp only [CollatzResearch.WordTrace]
  refine ⟨107643775451846440115747911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143525033935795253487663881 107643775451846440115747911)
  ·
    refine ⟨161465663177769660173621867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107643775451846440115747911 161465663177769660173621867)
    ·
      refine ⟨242198494766654490260432801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161465663177769660173621867 242198494766654490260432801)
      ·
        refine ⟨181648871074990867695324601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242198494766654490260432801 181648871074990867695324601)
        ·
          refine ⟨136236653306243150771493451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181648871074990867695324601 136236653306243150771493451)
          ·
            refine ⟨204354979959364726157240177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136236653306243150771493451 204354979959364726157240177)
            ·
              refine ⟨153266234969523544617930133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204354979959364726157240177 153266234969523544617930133)
              ·
                refine ⟨7184354764196416153965475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153266234969523544617930133 7184354764196416153965475)
                ·
                  refine ⟨10776532146294624230948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184354764196416153965475 10776532146294624230948213)
                  ·
                    refine ⟨1010299888715121021651395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10776532146294624230948213 1010299888715121021651395)
                    ·
                      rfl

theorem cell23_5902656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_5902656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902656 prefixEnd_5902656 := by exact prefixLift 5902656
  have htrace : WordTrace (prefixWord ++ tailWord_5902656) baseStart_5902656 baseEnd_5902656 := by
    simpa [prefixWord, tailWord_5902656, baseEnd_5902656] using wordTrace_append hprefix tailTrace_5902656
  have hstable : (prefixWord ++ tailWord_5902656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902656).length < 2 ^ (prefixWord ++ tailWord_5902656).sum := by decide
  have hdescent : baseEnd_5902656 < baseStart_5902656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902687 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 1, 1, 3]
def baseStart_5902687 : Nat := 118140960795 + 5902687 * 2 ^ 59
def prefixEnd_5902687 : Nat := 4983230072969 + 3 ^ 40 * 5902687 * 2
def baseEnd_5902687 : Nat := 3030915584045652443666543

theorem tailTrace_5902687 : CollatzResearch.WordTrace tailWord_5902687 prefixEnd_5902687 3030915584045652443666543 := by
  unfold tailWord_5902687
  simp only [CollatzResearch.WordTrace]
  refine ⟨215288681566580572525874315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143525787711053715017249543 215288681566580572525874315)
  ·
    refine ⟨322933022349870858788811473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215288681566580572525874315 322933022349870858788811473)
    ·
      refine ⟨242199766762403144091608605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322933022349870858788811473 242199766762403144091608605)
      ·
        refine ⟨90824912535901179034353227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242199766762403144091608605 90824912535901179034353227)
        ·
          refine ⟨136237368803851768551529841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90824912535901179034353227 136237368803851768551529841)
          ·
            refine ⟨102178026602888826413647381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136237368803851768551529841 102178026602888826413647381)
            ·
              refine ⟨4789594997010413738139721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102178026602888826413647381 4789594997010413738139721)
              ·
                refine ⟨3592196247757810303604791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789594997010413738139721 3592196247757810303604791)
                ·
                  refine ⟨5388294371636715455407187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592196247757810303604791 5388294371636715455407187)
                  ·
                    refine ⟨8082441557455073183110781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388294371636715455407187 8082441557455073183110781)
                    ·
                      refine ⟨3030915584045652443666543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082441557455073183110781 3030915584045652443666543)
                      ·
                        rfl

theorem cell23_5902687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_5902687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902687 prefixEnd_5902687 := by exact prefixLift 5902687
  have htrace : WordTrace (prefixWord ++ tailWord_5902687) baseStart_5902687 baseEnd_5902687 := by
    simpa [prefixWord, tailWord_5902687, baseEnd_5902687] using wordTrace_append hprefix tailTrace_5902687
  have hstable : (prefixWord ++ tailWord_5902687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902687).length < 2 ^ (prefixWord ++ tailWord_5902687).sum := by decide
  have hdescent : baseEnd_5902687 < baseStart_5902687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902713 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_5902713 : Nat := 118140960795 + 5902713 * 2 ^ 59
def prefixEnd_5902713 : Nat := 4983230072969 + 3 ^ 40 * 5902713 * 2
def baseEnd_5902713 : Nat := 3030928934542669341941423

theorem tailTrace_5902713 : CollatzResearch.WordTrace tailWord_5902713 prefixEnd_5902713 3030928934542669341941423 := by
  unfold tailWord_5902713
  simp only [CollatzResearch.WordTrace]
  refine ⟨215289629864486378966320793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143526419909657585977547195 215289629864486378966320793)
  ·
    refine ⟨161467222398364784224740595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215289629864486378966320793 161467222398364784224740595)
    ·
      refine ⟨242200833597547176337110893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161467222398364784224740595 242200833597547176337110893)
      ·
        refine ⟨90825312599080191126416585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242200833597547176337110893 90825312599080191126416585)
        ·
          refine ⟨68118984449310143344812439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90825312599080191126416585 68118984449310143344812439)
          ·
            refine ⟨102178476673965215017218659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68118984449310143344812439 102178476673965215017218659)
            ·
              refine ⟨153267715010947822525827989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102178476673965215017218659 153267715010947822525827989)
              ·
                refine ⟨7184424141138179180898187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153267715010947822525827989 7184424141138179180898187)
                ·
                  refine ⟨10776636211707268771347281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184424141138179180898187 10776636211707268771347281)
                  ·
                    refine ⟨8082477158780451578510461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10776636211707268771347281 8082477158780451578510461)
                    ·
                      refine ⟨3030928934542669341941423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082477158780451578510461 3030928934542669341941423)
                      ·
                        rfl

theorem cell23_5902713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_5902713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902713 prefixEnd_5902713 := by exact prefixLift 5902713
  have htrace : WordTrace (prefixWord ++ tailWord_5902713) baseStart_5902713 baseEnd_5902713 := by
    simpa [prefixWord, tailWord_5902713, baseEnd_5902713] using wordTrace_append hprefix tailTrace_5902713
  have hstable : (prefixWord ++ tailWord_5902713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902713).length < 2 ^ (prefixWord ++ tailWord_5902713).sum := by decide
  have hdescent : baseEnd_5902713 < baseStart_5902713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902744 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5902744 : Nat := 118140960795 + 5902744 * 2 ^ 59
def prefixEnd_5902744 : Nat := 4983230072969 + 3 ^ 40 * 5902744 * 2
def baseEnd_5902744 : Nat := 3030944852442958720653781

theorem tailTrace_5902744 : CollatzResearch.WordTrace tailWord_5902744 prefixEnd_5902744 3030944852442958720653781 := by
  unfold tailWord_5902744
  simp only [CollatzResearch.WordTrace]
  refine ⟨107645380263687035630349643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143527173684916047507132857 107645380263687035630349643)
  ·
    refine ⟨161468070395530553445524465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107645380263687035630349643 161468070395530553445524465)
    ·
      refine ⟨121101052796647915084143349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161468070395530553445524465 121101052796647915084143349)
      ·
        refine ⟨11353223699685742039138439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121101052796647915084143349 11353223699685742039138439)
        ·
          refine ⟨17029835549528613058707659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353223699685742039138439 17029835549528613058707659)
          ·
            refine ⟨25544753324292919588061489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029835549528613058707659 25544753324292919588061489)
            ·
              refine ⟨19158564993219689691046117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25544753324292919588061489 19158564993219689691046117)
              ·
                refine ⟨3592230936228691817071147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19158564993219689691046117 3592230936228691817071147)
                ·
                  refine ⟨5388346404343037725606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592230936228691817071147 5388346404343037725606721)
                  ·
                    refine ⟨4041259803257278294205041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5388346404343037725606721 4041259803257278294205041)
                    ·
                      refine ⟨3030944852442958720653781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041259803257278294205041 3030944852442958720653781)
                      ·
                        rfl

theorem cell23_5902744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5902744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902744 prefixEnd_5902744 := by exact prefixLift 5902744
  have htrace : WordTrace (prefixWord ++ tailWord_5902744) baseStart_5902744 baseEnd_5902744 := by
    simpa [prefixWord, tailWord_5902744, baseEnd_5902744] using wordTrace_append hprefix tailTrace_5902744
  have hstable : (prefixWord ++ tailWord_5902744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902744).length < 2 ^ (prefixWord ++ tailWord_5902744).sum := by decide
  have hdescent : baseEnd_5902744 < baseStart_5902744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902813 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5902813 : Nat := 118140960795 + 5902813 * 2 ^ 59
def prefixEnd_5902813 : Nat := 4983230072969 + 3 ^ 40 * 5902813 * 2
def baseEnd_5902813 : Nat := 3030980282608118950690963

theorem tailTrace_5902813 : CollatzResearch.WordTrace tailWord_5902813 prefixEnd_5902813 3030980282608118950690963 := by
  unfold tailWord_5902813
  simp only [CollatzResearch.WordTrace]
  refine ⟨215293277164124096044961093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143528851442749397363307395 215293277164124096044961093)
  ·
    refine ⟨40367489468273268008430205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215293277164124096044961093 40367489468273268008430205)
    ·
      refine ⟨15137808550602475503161327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40367489468273268008430205 15137808550602475503161327)
      ·
        refine ⟨22706712825903713254741991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15137808550602475503161327 22706712825903713254741991)
        ·
          refine ⟨34060069238855569882112987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22706712825903713254741991 34060069238855569882112987)
          ·
            refine ⟨51090103858283354823169481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34060069238855569882112987 51090103858283354823169481)
            ·
              refine ⟨38317577893712516117377111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51090103858283354823169481 38317577893712516117377111)
              ·
                refine ⟨57476366840568774176065667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38317577893712516117377111 57476366840568774176065667)
                ·
                  refine ⟨86214550260853161264098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57476366840568774176065667 86214550260853161264098501)
                  ·
                    refine ⟨16165228173909967737018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86214550260853161264098501 16165228173909967737018469)
                    ·
                      refine ⟨3030980282608118950690963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16165228173909967737018469 3030980282608118950690963)
                      ·
                        rfl

theorem cell23_5902813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5902813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902813 prefixEnd_5902813 := by exact prefixLift 5902813
  have htrace : WordTrace (prefixWord ++ tailWord_5902813) baseStart_5902813 baseEnd_5902813 := by
    simpa [prefixWord, tailWord_5902813, baseEnd_5902813] using wordTrace_append hprefix tailTrace_5902813
  have hstable : (prefixWord ++ tailWord_5902813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902813).length < 2 ^ (prefixWord ++ tailWord_5902813).sum := by decide
  have hdescent : baseEnd_5902813 < baseStart_5902813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902817 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_5902817 : Nat := 118140960795 + 5902817 * 2 ^ 59
def prefixEnd_5902817 : Nat := 4983230072969 + 3 ^ 40 * 5902817 * 2
def baseEnd_5902817 : Nat := 3030982336530736935040945

theorem tailTrace_5902817 : CollatzResearch.WordTrace tailWord_5902817 prefixEnd_5902817 3030982336530736935040945 := by
  unfold tailWord_5902817
  simp only [CollatzResearch.WordTrace]
  refine ⟨215293423056109604728106705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143528948704073069818737803 215293423056109604728106705)
  ·
    refine ⟨161470067292082203546080029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215293423056109604728106705 161470067292082203546080029)
    ·
      refine ⟨60551275234530826329780011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161470067292082203546080029 60551275234530826329780011)
      ·
        refine ⟨90826912851796239494670017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60551275234530826329780011 90826912851796239494670017)
        ·
          refine ⟨68120184638847179621002513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90826912851796239494670017 68120184638847179621002513)
          ·
            refine ⟨51090138479135384715751885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68120184638847179621002513 51090138479135384715751885)
            ·
              refine ⟨19158801929675769268406957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51090138479135384715751885 19158801929675769268406957)
              ·
                refine ⟨7184550723628413475652609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19158801929675769268406957 7184550723628413475652609)
                ·
                  refine ⟨5388413042721310106739457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7184550723628413475652609 5388413042721310106739457)
                  ·
                    refine ⟨4041309782040982580054593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5388413042721310106739457 4041309782040982580054593)
                    ·
                      refine ⟨3030982336530736935040945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041309782040982580054593 3030982336530736935040945)
                      ·
                        rfl

theorem cell23_5902817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_5902817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902817 prefixEnd_5902817 := by exact prefixLift 5902817
  have htrace : WordTrace (prefixWord ++ tailWord_5902817) baseStart_5902817 baseEnd_5902817 := by
    simpa [prefixWord, tailWord_5902817, baseEnd_5902817] using wordTrace_append hprefix tailTrace_5902817
  have hstable : (prefixWord ++ tailWord_5902817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902817).length < 2 ^ (prefixWord ++ tailWord_5902817).sum := by decide
  have hdescent : baseEnd_5902817 < baseStart_5902817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902821 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5902821 : Nat := 118140960795 + 5902821 * 2 ^ 59
def prefixEnd_5902821 : Nat := 4983230072969 + 3 ^ 40 * 5902821 * 2
def baseEnd_5902821 : Nat := 3030984390453354919390927

theorem tailTrace_5902821 : CollatzResearch.WordTrace tailWord_5902821 prefixEnd_5902821 3030984390453354919390927 := by
  unfold tailWord_5902821
  simp only [CollatzResearch.WordTrace]
  refine ⟨215293568948095113411252317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143529045965396742274168211 215293568948095113411252317)
  ·
    refine ⟨80735088355535667529219619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215293568948095113411252317 80735088355535667529219619)
    ·
      refine ⟨121102632533303501293829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80735088355535667529219619 121102632533303501293829429)
      ·
        refine ⟨11353371799997203246296509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121102632533303501293829429 11353371799997203246296509)
        ·
          refine ⟨4257514424998951217361191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11353371799997203246296509 4257514424998951217361191)
          ·
            refine ⟨6386271637498426826041787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257514424998951217361191 6386271637498426826041787)
            ·
              refine ⟨9579407456247640239062681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386271637498426826041787 9579407456247640239062681)
              ·
                refine ⟨7184555592185730179297011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9579407456247640239062681 7184555592185730179297011)
                ·
                  refine ⟨10776833388278595268945517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184555592185730179297011 10776833388278595268945517)
                  ·
                    refine ⟨4041312520604473225854569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10776833388278595268945517 4041312520604473225854569)
                    ·
                      refine ⟨3030984390453354919390927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041312520604473225854569 3030984390453354919390927)
                      ·
                        rfl

theorem cell23_5902821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5902821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902821 prefixEnd_5902821 := by exact prefixLift 5902821
  have htrace : WordTrace (prefixWord ++ tailWord_5902821) baseStart_5902821 baseEnd_5902821 := by
    simpa [prefixWord, tailWord_5902821, baseEnd_5902821] using wordTrace_append hprefix tailTrace_5902821
  have hstable : (prefixWord ++ tailWord_5902821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902821).length < 2 ^ (prefixWord ++ tailWord_5902821).sum := by decide
  have hdescent : baseEnd_5902821 < baseStart_5902821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902843 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 7, 2]
def baseStart_5902843 : Nat := 118140960795 + 5902843 * 2 ^ 59
def prefixEnd_5902843 : Nat := 4983230072969 + 3 ^ 40 * 5902843 * 2
def baseEnd_5902843 : Nat := 3030995687027753833315825

theorem tailTrace_5902843 : CollatzResearch.WordTrace tailWord_5902843 prefixEnd_5902843 3030995687027753833315825 := by
  unfold tailWord_5902843
  simp only [CollatzResearch.WordTrace]
  refine ⟨215294371354015411168553183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143529580902676940779035455 215294371354015411168553183)
  ·
    refine ⟨322941557031023116752829775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215294371354015411168553183 322941557031023116752829775)
    ·
      refine ⟨484412335546534675129244663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322941557031023116752829775 484412335546534675129244663)
      ·
        refine ⟨726618503319802012693866995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484412335546534675129244663 726618503319802012693866995)
        ·
          refine ⟨1089927754979703019040800493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726618503319802012693866995 1089927754979703019040800493)
          ·
            refine ⟨408722908117388632140300185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1089927754979703019040800493 408722908117388632140300185)
            ·
              refine ⟨306542181088041474105225139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408722908117388632140300185 306542181088041474105225139)
              ·
                refine ⟨459813271632062211157837709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306542181088041474105225139 459813271632062211157837709)
                ·
                  refine ⟨172429976862023329184189141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459813271632062211157837709 172429976862023329184189141)
                  ·
                    refine ⟨4041327582703671777754433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172429976862023329184189141 4041327582703671777754433)
                    ·
                      refine ⟨3030995687027753833315825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041327582703671777754433 3030995687027753833315825)
                      ·
                        rfl

theorem cell23_5902843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7, 2].length) (baseStart_5902843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902843 prefixEnd_5902843 := by exact prefixLift 5902843
  have htrace : WordTrace (prefixWord ++ tailWord_5902843) baseStart_5902843 baseEnd_5902843 := by
    simpa [prefixWord, tailWord_5902843, baseEnd_5902843] using wordTrace_append hprefix tailTrace_5902843
  have hstable : (prefixWord ++ tailWord_5902843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902843).length < 2 ^ (prefixWord ++ tailWord_5902843).sum := by decide
  have hdescent : baseEnd_5902843 < baseStart_5902843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902853 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_5902853 : Nat := 118140960795 + 5902853 * 2 ^ 59
def prefixEnd_5902853 : Nat := 4983230072969 + 3 ^ 40 * 5902853 * 2
def baseEnd_5902853 : Nat := 1010333607278099598063593

theorem tailTrace_5902853 : CollatzResearch.WordTrace tailWord_5902853 prefixEnd_5902853 1010333607278099598063593 := by
  unfold tailWord_5902853
  simp only [CollatzResearch.WordTrace]
  refine ⟨215294736083979182876417213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143529824055986121917611475 215294736083979182876417213)
  ·
    refine ⟨80735526031492193578656455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215294736083979182876417213 80735526031492193578656455)
    ·
      refine ⟨121103289047238290367984683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80735526031492193578656455 121103289047238290367984683)
      ·
        refine ⟨181654933570857435551977025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121103289047238290367984683 181654933570857435551977025)
        ·
          refine ⟨136241200178143076663982769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181654933570857435551977025 136241200178143076663982769)
          ·
            refine ⟨102180900133607307497987077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136241200178143076663982769 102180900133607307497987077)
            ·
              refine ⟨19158918775051370155872577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102180900133607307497987077 19158918775051370155872577)
              ·
                refine ⟨14369189081288527616904433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19158918775051370155872577 14369189081288527616904433)
                ·
                  refine ⟨10776891810966395712678325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14369189081288527616904433 10776891810966395712678325)
                  ·
                    refine ⟨1010333607278099598063593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10776891810966395712678325 1010333607278099598063593)
                    ·
                      rfl

theorem cell23_5902853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_5902853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902853 prefixEnd_5902853 := by exact prefixLift 5902853
  have htrace : WordTrace (prefixWord ++ tailWord_5902853) baseStart_5902853 baseEnd_5902853 := by
    simpa [prefixWord, tailWord_5902853, baseEnd_5902853] using wordTrace_append hprefix tailTrace_5902853
  have hstable : (prefixWord ++ tailWord_5902853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902853).length < 2 ^ (prefixWord ++ tailWord_5902853).sum := by decide
  have hdescent : baseEnd_5902853 < baseStart_5902853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902854 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5902854 : Nat := 118140960795 + 5902854 * 2 ^ 59
def prefixEnd_5902854 : Nat := 4983230072969 + 3 ^ 40 * 5902854 * 2
def baseEnd_5902854 : Nat := 3031001335314953290278275

theorem tailTrace_5902854 : CollatzResearch.WordTrace tailWord_5902854 prefixEnd_5902854 3031001335314953290278275 := by
  unfold tailWord_5902854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727961642405486251475113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143529848371317040031469077 6727961642405486251475113)
  ·
    refine ⟨5045971231804114688606335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6727961642405486251475113 5045971231804114688606335)
    ·
      refine ⟨7568956847706172032909503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5045971231804114688606335 7568956847706172032909503)
      ·
        refine ⟨11353435271559258049364255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568956847706172032909503 11353435271559258049364255)
        ·
          refine ⟨17030152907338887074046383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353435271559258049364255 17030152907338887074046383)
          ·
            refine ⟨25545229361008330611069575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17030152907338887074046383 25545229361008330611069575)
            ·
              refine ⟨38317844041512495916604363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25545229361008330611069575 38317844041512495916604363)
              ·
                refine ⟨57476766062268743874906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38317844041512495916604363 57476766062268743874906545)
                ·
                  refine ⟨43107574546701557906179909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57476766062268743874906545 43107574546701557906179909)
                  ·
                    refine ⟨8082670227506542107408733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43107574546701557906179909 8082670227506542107408733)
                    ·
                      refine ⟨3031001335314953290278275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082670227506542107408733 3031001335314953290278275)
                      ·
                        rfl

theorem cell23_5902854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5902854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902854 prefixEnd_5902854 := by exact prefixLift 5902854
  have htrace : WordTrace (prefixWord ++ tailWord_5902854) baseStart_5902854 baseEnd_5902854 := by
    simpa [prefixWord, tailWord_5902854, baseEnd_5902854] using wordTrace_append hprefix tailTrace_5902854
  have hstable : (prefixWord ++ tailWord_5902854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902854).length < 2 ^ (prefixWord ++ tailWord_5902854).sum := by decide
  have hdescent : baseEnd_5902854 < baseStart_5902854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902860 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_5902860 : Nat := 118140960795 + 5902860 * 2 ^ 59
def prefixEnd_5902860 : Nat := 4983230072969 + 3 ^ 40 * 5902860 * 2
def baseEnd_5902860 : Nat := 3031004416198880266803247

theorem tailTrace_5902860 : CollatzResearch.WordTrace tailWord_5902860 prefixEnd_5902860 3031004416198880266803247 := by
  unfold tailWord_5902860
  simp only [CollatzResearch.WordTrace]
  refine ⟨107647495697476911535961017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143529994263302548714614689 107647495697476911535961017)
  ·
    refine ⟨80735621773107683651970763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107647495697476911535961017 80735621773107683651970763)
    ·
      refine ⟨121103432659661525477956145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80735621773107683651970763 121103432659661525477956145)
      ·
        refine ⟨90827574494746144108467109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121103432659661525477956145 90827574494746144108467109)
        ·
          refine ⟨17030170217764902020337583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90827574494746144108467109 17030170217764902020337583)
          ·
            refine ⟨25545255326647353030506375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17030170217764902020337583 25545255326647353030506375)
            ·
              refine ⟨38317882989971029545759563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25545255326647353030506375 38317882989971029545759563)
              ·
                refine ⟨57476824484956544318639345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38317882989971029545759563 57476824484956544318639345)
                ·
                  refine ⟨43107618363717408238979509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57476824484956544318639345 43107618363717408238979509)
                  ·
                    refine ⟨4041339221598507022404329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43107618363717408238979509 4041339221598507022404329)
                    ·
                      refine ⟨3031004416198880266803247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041339221598507022404329 3031004416198880266803247)
                      ·
                        rfl

theorem cell23_5902860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_5902860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902860 prefixEnd_5902860 := by exact prefixLift 5902860
  have htrace : WordTrace (prefixWord ++ tailWord_5902860) baseStart_5902860 baseEnd_5902860 := by
    simpa [prefixWord, tailWord_5902860, baseEnd_5902860] using wordTrace_append hprefix tailTrace_5902860
  have hstable : (prefixWord ++ tailWord_5902860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902860).length < 2 ^ (prefixWord ++ tailWord_5902860).sum := by decide
  have hdescent : baseEnd_5902860 < baseStart_5902860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902887 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5902887 : Nat := 118140960795 + 5902887 * 2 ^ 59
def prefixEnd_5902887 : Nat := 4983230072969 + 3 ^ 40 * 5902887 * 2
def baseEnd_5902887 : Nat := 1010339426725517220388541

theorem tailTrace_5902887 : CollatzResearch.WordTrace tailWord_5902887 prefixEnd_5902887 1010339426725517220388541 := by
  unfold tailWord_5902887
  simp only [CollatzResearch.WordTrace]
  refine ⟨215295976165856006683154915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143530650777237337788769943 215295976165856006683154915)
  ·
    refine ⟨322943964248784010024732373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215295976165856006683154915 322943964248784010024732373)
    ·
      refine ⟨7568999162080875234954665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 322943964248784010024732373 7568999162080875234954665)
      ·
        refine ⟨5676749371560656426215999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7568999162080875234954665 5676749371560656426215999)
        ·
          refine ⟨8515124057340984639323999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676749371560656426215999 8515124057340984639323999)
          ·
            refine ⟨12772686086011476958985999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515124057340984639323999 12772686086011476958985999)
            ·
              refine ⟨19159029129017215438478999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772686086011476958985999 19159029129017215438478999)
              ·
                refine ⟨28738543693525823157718499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19159029129017215438478999 28738543693525823157718499)
                ·
                  refine ⟨43107815540288734736577749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28738543693525823157718499 43107815540288734736577749)
                  ·
                    refine ⟨1010339426725517220388541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43107815540288734736577749 1010339426725517220388541)
                    ·
                      rfl

theorem cell23_5902887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5902887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902887 prefixEnd_5902887 := by exact prefixLift 5902887
  have htrace : WordTrace (prefixWord ++ tailWord_5902887) baseStart_5902887 baseEnd_5902887 := by
    simpa [prefixWord, tailWord_5902887, baseEnd_5902887] using wordTrace_append hprefix tailTrace_5902887
  have hstable : (prefixWord ++ tailWord_5902887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902887).length < 2 ^ (prefixWord ++ tailWord_5902887).sum := by decide
  have hdescent : baseEnd_5902887 < baseStart_5902887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902890 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5902890 : Nat := 118140960795 + 5902890 * 2 ^ 59
def prefixEnd_5902890 : Nat := 4983230072969 + 3 ^ 40 * 5902890 * 2
def baseEnd_5902890 : Nat := 3031019820618515149428109

theorem tailTrace_5902890 : CollatzResearch.WordTrace tailWord_5902890 prefixEnd_5902890 3031019820618515149428109 := by
  unfold tailWord_5902890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53824021396211284548878531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143530723723230092130342749 53824021396211284548878531)
  ·
    refine ⟨80736032094316926823317797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53824021396211284548878531 80736032094316926823317797)
    ·
      refine ⟨15138006017684423779372087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80736032094316926823317797 15138006017684423779372087)
      ·
        refine ⟨22707009026526635669058131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15138006017684423779372087 22707009026526635669058131)
        ·
          refine ⟨34060513539789953503587197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22707009026526635669058131 34060513539789953503587197)
          ·
            refine ⟨12772692577421232563845199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34060513539789953503587197 12772692577421232563845199)
            ·
              refine ⟨19159038866131848845767799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772692577421232563845199 19159038866131848845767799)
              ·
                refine ⟨28738558299197773268651699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19159038866131848845767799 28738558299197773268651699)
                ·
                  refine ⟨43107837448796659902977549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28738558299197773268651699 43107837448796659902977549)
                  ·
                    refine ⟨16165439043298747463616581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43107837448796659902977549 16165439043298747463616581)
                    ·
                      refine ⟨3031019820618515149428109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16165439043298747463616581 3031019820618515149428109)
                      ·
                        rfl

theorem cell23_5902890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5902890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902890 prefixEnd_5902890 := by exact prefixLift 5902890
  have htrace : WordTrace (prefixWord ++ tailWord_5902890) baseStart_5902890 baseEnd_5902890 := by
    simpa [prefixWord, tailWord_5902890, baseEnd_5902890] using wordTrace_append hprefix tailTrace_5902890
  have hstable : (prefixWord ++ tailWord_5902890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902890).length < 2 ^ (prefixWord ++ tailWord_5902890).sum := by decide
  have hdescent : baseEnd_5902890 < baseStart_5902890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902917 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_5902917 : Nat := 118140960795 + 5902917 * 2 ^ 59
def prefixEnd_5902917 : Nat := 4983230072969 + 3 ^ 40 * 5902917 * 2
def baseEnd_5902917 : Nat := 1010344561532062181263495

theorem tailTrace_5902917 : CollatzResearch.WordTrace tailWord_5902917 prefixEnd_5902917 1010344561532062181263495 := by
  unfold tailWord_5902917
  simp only [CollatzResearch.WordTrace]
  refine ⟨215297070355747321806747005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143531380237164881204498003 215297070355747321806747005)
  ·
    refine ⟨80736401383405245677530127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215297070355747321806747005 80736401383405245677530127)
    ·
      refine ⟨121104602075107868516295191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80736401383405245677530127 121104602075107868516295191)
      ·
        refine ⟨181656903112661802774442787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121104602075107868516295191 181656903112661802774442787)
        ·
          refine ⟨272485354668992704161664181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181656903112661802774442787 272485354668992704161664181)
          ·
            refine ⟨25545502000218066015156017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272485354668992704161664181 25545502000218066015156017)
            ·
              refine ⟨19159126500163549511367013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25545502000218066015156017 19159126500163549511367013)
              ·
                refine ⟨3592336218780665533381315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19159126500163549511367013 3592336218780665533381315)
                ·
                  refine ⟨5388504328170998300071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592336218780665533381315 5388504328170998300071973)
                  ·
                    refine ⟨1010344561532062181263495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5388504328170998300071973 1010344561532062181263495)
                    ·
                      rfl

theorem cell23_5902917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_5902917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902917 prefixEnd_5902917 := by exact prefixLift 5902917
  have htrace : WordTrace (prefixWord ++ tailWord_5902917) baseStart_5902917 baseEnd_5902917 := by
    simpa [prefixWord, tailWord_5902917, baseEnd_5902917] using wordTrace_append hprefix tailTrace_5902917
  have hstable : (prefixWord ++ tailWord_5902917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902917).length < 2 ^ (prefixWord ++ tailWord_5902917).sum := by decide
  have hdescent : baseEnd_5902917 < baseStart_5902917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902943 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 3, 5]
def baseStart_5902943 : Nat := 118140960795 + 5902943 * 2 ^ 59
def prefixEnd_5902943 : Nat := 4983230072969 + 3 ^ 40 * 5902943 * 2
def baseEnd_5902943 : Nat := 1010349011697734480688455

theorem tailTrace_5902943 : CollatzResearch.WordTrace tailWord_5902943 prefixEnd_5902943 1010349011697734480688455 := by
  unfold tailWord_5902943
  simp only [CollatzResearch.WordTrace]
  refine ⟨215298018653653128247193483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143532012435768752164795655 215298018653653128247193483)
  ·
    refine ⟨322947027980479692370790225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215298018653653128247193483 322947027980479692370790225)
    ·
      refine ⟨242210270985359769278092669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322947027980479692370790225 242210270985359769278092669)
      ·
        refine ⟨90828851619509913479284751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242210270985359769278092669 90828851619509913479284751)
        ·
          refine ⟨136243277429264870218927127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90828851619509913479284751 136243277429264870218927127)
          ·
            refine ⟨204364916143897305328390691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136243277429264870218927127 204364916143897305328390691)
            ·
              refine ⟨306547374215845957992586037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204364916143897305328390691 306547374215845957992586037)
              ·
                refine ⟨28738816332735558561804941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306547374215845957992586037 28738816332735558561804941)
                ·
                  refine ⟨10777056124775834460676853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28738816332735558561804941 10777056124775834460676853)
                  ·
                    refine ⟨1010349011697734480688455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10777056124775834460676853 1010349011697734480688455)
                    ·
                      rfl

theorem cell23_5902943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_5902943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902943 prefixEnd_5902943 := by exact prefixLift 5902943
  have htrace : WordTrace (prefixWord ++ tailWord_5902943) baseStart_5902943 baseEnd_5902943 := by
    simpa [prefixWord, tailWord_5902943, baseEnd_5902943] using wordTrace_append hprefix tailTrace_5902943
  have hstable : (prefixWord ++ tailWord_5902943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902943).length < 2 ^ (prefixWord ++ tailWord_5902943).sum := by decide
  have hdescent : baseEnd_5902943 < baseStart_5902943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902990 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_5902990 : Nat := 118140960795 + 5902990 * 2 ^ 59
def prefixEnd_5902990 : Nat := 4983230072969 + 3 ^ 40 * 5902990 * 2
def baseEnd_5902990 : Nat := 1010357056227988252725883

theorem tailTrace_5902990 : CollatzResearch.WordTrace tailWord_5902990 prefixEnd_5902990 1010357056227988252725883 := by
  unfold tailWord_5902990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26912466610560356909269303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143533155256321903516102949 26912466610560356909269303)
  ·
    refine ⟨40368699915840535363903955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26912466610560356909269303 40368699915840535363903955)
    ·
      refine ⟨60553049873760803045855933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40368699915840535363903955 60553049873760803045855933)
      ·
        refine ⟨22707393702660301142195975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60553049873760803045855933 22707393702660301142195975)
        ·
          refine ⟨34061090553990451713293963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22707393702660301142195975 34061090553990451713293963)
          ·
            refine ⟨51091635830985677569940945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34061090553990451713293963 51091635830985677569940945)
            ·
              refine ⟨38318726873239258177455709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51091635830985677569940945 38318726873239258177455709)
              ·
                refine ⟨14369522577464721816545891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38318726873239258177455709 14369522577464721816545891)
                ·
                  refine ⟨21554283866197082724818837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14369522577464721816545891 21554283866197082724818837)
                  ·
                    refine ⟨1010357056227988252725883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21554283866197082724818837 1010357056227988252725883)
                    ·
                      rfl

theorem cell23_5902990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_5902990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902990 prefixEnd_5902990 := by exact prefixLift 5902990
  have htrace : WordTrace (prefixWord ++ tailWord_5902990) baseStart_5902990 baseEnd_5902990 := by
    simpa [prefixWord, tailWord_5902990, baseEnd_5902990] using wordTrace_append hprefix tailTrace_5902990
  have hstable : (prefixWord ++ tailWord_5902990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902990).length < 2 ^ (prefixWord ++ tailWord_5902990).sum := by decide
  have hdescent : baseEnd_5902990 < baseStart_5902990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5902994 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_5902994 : Nat := 118140960795 + 5902994 * 2 ^ 59
def prefixEnd_5902994 : Nat := 4983230072969 + 3 ^ 40 * 5902994 * 2
def baseEnd_5902994 : Nat := 1010357740868860914175877

theorem tailTrace_5902994 : CollatzResearch.WordTrace tailWord_5902994 prefixEnd_5902994 1010357740868860914175877 := by
  unfold tailWord_5902994
  simp only [CollatzResearch.WordTrace]
  refine ⟨53824969694117090989325009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143533252517645575971533357 53824969694117090989325009)
  ·
    refine ⟨40368727270587818241993757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53824969694117090989325009 40368727270587818241993757)
    ·
      refine ⟨15138272726470431840747659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40368727270587818241993757 15138272726470431840747659)
      ·
        refine ⟨22707409089705647761121489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15138272726470431840747659 22707409089705647761121489)
        ·
          refine ⟨17030556817279235820841117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22707409089705647761121489 17030556817279235820841117)
          ·
            refine ⟨6386458806479713432815419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17030556817279235820841117 6386458806479713432815419)
            ·
              refine ⟨9579688209719570149223129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386458806479713432815419 9579688209719570149223129)
              ·
                refine ⟨7184766157289677611917347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9579688209719570149223129 7184766157289677611917347)
                ·
                  refine ⟨10777149235934516417876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184766157289677611917347 10777149235934516417876021)
                  ·
                    refine ⟨1010357740868860914175877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10777149235934516417876021 1010357740868860914175877)
                    ·
                      rfl

theorem cell23_5902994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_5902994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5902994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5902994 prefixEnd_5902994 := by exact prefixLift 5902994
  have htrace : WordTrace (prefixWord ++ tailWord_5902994) baseStart_5902994 baseEnd_5902994 := by
    simpa [prefixWord, tailWord_5902994, baseEnd_5902994] using wordTrace_append hprefix tailTrace_5902994
  have hstable : (prefixWord ++ tailWord_5902994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5902994).length < 2 ^ (prefixWord ++ tailWord_5902994).sum := by decide
  have hdescent : baseEnd_5902994 < baseStart_5902994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5902994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903025 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5903025 : Nat := 118140960795 + 5903025 * 2 ^ 59
def prefixEnd_5903025 : Nat := 4983230072969 + 3 ^ 40 * 5903025 * 2
def baseEnd_5903025 : Nat := 3031089140506872121239989

theorem tailTrace_5903025 : CollatzResearch.WordTrace tailWord_5903025 prefixEnd_5903025 3031089140506872121239989 := by
  unfold tailWord_5903025
  simp only [CollatzResearch.WordTrace]
  refine ⟨215301009439356056251678529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143534006292904037501119019 215301009439356056251678529)
  ·
    refine ⟨161475757079517042188758897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215301009439356056251678529 161475757079517042188758897)
    ·
      refine ⟨121106817809637781641569173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161475757079517042188758897 121106817809637781641569173)
      ·
        refine ⟨5676882084826771014448555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121106817809637781641569173 5676882084826771014448555)
        ·
          refine ⟨8515323127240156521672833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676882084826771014448555 8515323127240156521672833)
          ·
            refine ⟨6386492345430117391254625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515323127240156521672833 6386492345430117391254625)
            ·
              refine ⟨4789869259072588043440969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386492345430117391254625 4789869259072588043440969)
              ·
                refine ⟨3592401944304441032580727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789869259072588043440969 3592401944304441032580727)
                ·
                  refine ⟨5388602916456661548871091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592401944304441032580727 5388602916456661548871091)
                  ·
                    refine ⟨8082904374684992323306637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388602916456661548871091 8082904374684992323306637)
                    ·
                      refine ⟨3031089140506872121239989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082904374684992323306637 3031089140506872121239989)
                      ·
                        rfl

theorem cell23_5903025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5903025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903025 prefixEnd_5903025 := by exact prefixLift 5903025
  have htrace : WordTrace (prefixWord ++ tailWord_5903025) baseStart_5903025 baseEnd_5903025 := by
    simpa [prefixWord, tailWord_5903025, baseEnd_5903025] using wordTrace_append hprefix tailTrace_5903025
  have hstable : (prefixWord ++ tailWord_5903025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903025).length < 2 ^ (prefixWord ++ tailWord_5903025).sum := by decide
  have hdescent : baseEnd_5903025 < baseStart_5903025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903057 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_5903057 : Nat := 118140960795 + 5903057 * 2 ^ 59
def prefixEnd_5903057 : Nat := 4983230072969 + 3 ^ 40 * 5903057 * 2
def baseEnd_5903057 : Nat := 3031105571887815996039841

theorem tailTrace_5903057 : CollatzResearch.WordTrace tailWord_5903057 prefixEnd_5903057 3031105571887815996039841 := by
  unfold tailWord_5903057
  simp only [CollatzResearch.WordTrace]
  refine ⟨215302176575240125716843425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143534784383493417144562283 215302176575240125716843425)
  ·
    refine ⟨161476632431430094287632569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215302176575240125716843425 161476632431430094287632569)
    ·
      refine ⟨121107474323572570715724427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161476632431430094287632569 121107474323572570715724427)
      ·
        refine ⟨181661211485358856073586641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121107474323572570715724427 181661211485358856073586641)
        ·
          refine ⟨136245908614019142055189981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181661211485358856073586641 136245908614019142055189981)
          ·
            refine ⟨51092215730257178270696243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136245908614019142055189981 51092215730257178270696243)
            ·
              refine ⟨76638323595385767406044365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51092215730257178270696243 76638323595385767406044365)
              ·
                refine ⟨28739371348269662777266637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76638323595385767406044365 28739371348269662777266637)
                ·
                  refine ⟨10777264255601123541474989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28739371348269662777266637 10777264255601123541474989)
                  ·
                    refine ⟨4041474095850421328053121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10777264255601123541474989 4041474095850421328053121)
                    ·
                      refine ⟨3031105571887815996039841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041474095850421328053121 3031105571887815996039841)
                      ·
                        rfl

theorem cell23_5903057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_5903057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903057 prefixEnd_5903057 := by exact prefixLift 5903057
  have htrace : WordTrace (prefixWord ++ tailWord_5903057) baseStart_5903057 baseEnd_5903057 := by
    simpa [prefixWord, tailWord_5903057, baseEnd_5903057] using wordTrace_append hprefix tailTrace_5903057
  have hstable : (prefixWord ++ tailWord_5903057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903057).length < 2 ^ (prefixWord ++ tailWord_5903057).sum := by decide
  have hdescent : baseEnd_5903057 < baseStart_5903057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903068 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5903068 : Nat := 118140960795 + 5903068 * 2 ^ 59
def prefixEnd_5903068 : Nat := 4983230072969 + 3 ^ 40 * 5903068 * 2
def baseEnd_5903068 : Nat := 3031111220175015453002291

theorem tailTrace_5903068 : CollatzResearch.WordTrace tailWord_5903068 prefixEnd_5903068 3031111220175015453002291 := by
  unfold tailWord_5903068
  simp only [CollatzResearch.WordTrace]
  refine ⟨107651288889100137297746929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143535051852133516396995905 107651288889100137297746929)
  ·
    refine ⟨80738466666825102973310197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107651288889100137297746929 80738466666825102973310197)
    ·
      refine ⟨7569231250014853403747831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80738466666825102973310197 7569231250014853403747831)
      ·
        refine ⟨11353846875022280105621747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569231250014853403747831 11353846875022280105621747)
        ·
          refine ⟨17030770312533420158432621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353846875022280105621747 17030770312533420158432621)
          ·
            refine ⟨6386538867200032559412233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17030770312533420158432621 6386538867200032559412233)
            ·
              refine ⟨4789904150400024419559175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386538867200032559412233 4789904150400024419559175)
              ·
                refine ⟨7184856225600036629338763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789904150400024419559175 7184856225600036629338763)
                ·
                  refine ⟨10777284338400054944008145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184856225600036629338763 10777284338400054944008145)
                  ·
                    refine ⟨8082963253800041208006109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10777284338400054944008145 8082963253800041208006109)
                    ·
                      refine ⟨3031111220175015453002291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8082963253800041208006109 3031111220175015453002291)
                      ·
                        rfl

theorem cell23_5903068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5903068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903068 prefixEnd_5903068 := by exact prefixLift 5903068
  have htrace : WordTrace (prefixWord ++ tailWord_5903068) baseStart_5903068 baseEnd_5903068 := by
    simpa [prefixWord, tailWord_5903068, baseEnd_5903068] using wordTrace_append hprefix tailTrace_5903068
  have hstable : (prefixWord ++ tailWord_5903068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903068).length < 2 ^ (prefixWord ++ tailWord_5903068).sum := by decide
  have hdescent : baseEnd_5903068 < baseStart_5903068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903177 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_5903177 : Nat := 118140960795 + 5903177 * 2 ^ 59
def prefixEnd_5903177 : Nat := 4983230072969 + 3 ^ 40 * 5903177 * 2
def baseEnd_5903177 : Nat := 3031167189566355526539289

theorem tailTrace_5903177 : CollatzResearch.WordTrace tailWord_5903177 prefixEnd_5903177 3031167189566355526539289 := by
  unfold tailWord_5903177
  simp only [CollatzResearch.WordTrace]
  refine ⟨215306553334805386211211785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143537702223203590807474523 215306553334805386211211785)
  ·
    refine ⟨161479915001104039658408839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215306553334805386211211785 161479915001104039658408839)
    ·
      refine ⟨242219872501656059487613259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161479915001104039658408839 242219872501656059487613259)
      ·
        refine ⟨363329808752484089231419889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242219872501656059487613259 363329808752484089231419889)
        ·
          refine ⟨272497356564363066923564917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363329808752484089231419889 272497356564363066923564917)
          ·
            refine ⟨25546627177909037524084211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272497356564363066923564917 25546627177909037524084211)
            ·
              refine ⟨38319940766863556286126317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25546627177909037524084211 38319940766863556286126317)
              ·
                refine ⟨14369977787573833607297369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38319940766863556286126317 14369977787573833607297369)
                ·
                  refine ⟨10777483340680375205473027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14369977787573833607297369 10777483340680375205473027)
                  ·
                    refine ⟨16166225011020562808209541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10777483340680375205473027 16166225011020562808209541)
                    ·
                      refine ⟨3031167189566355526539289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16166225011020562808209541 3031167189566355526539289)
                      ·
                        rfl

theorem cell23_5903177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_5903177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903177 prefixEnd_5903177 := by exact prefixLift 5903177
  have htrace : WordTrace (prefixWord ++ tailWord_5903177) baseStart_5903177 baseEnd_5903177 := by
    simpa [prefixWord, tailWord_5903177, baseEnd_5903177] using wordTrace_append hprefix tailTrace_5903177
  have hstable : (prefixWord ++ tailWord_5903177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903177).length < 2 ^ (prefixWord ++ tailWord_5903177).sum := by decide
  have hdescent : baseEnd_5903177 < baseStart_5903177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903217 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 6]
def baseStart_5903217 : Nat := 118140960795 + 5903217 * 2 ^ 59
def prefixEnd_5903217 : Nat := 4983230072969 + 3 ^ 40 * 5903217 * 2
def baseEnd_5903217 : Nat := 336798636532503930004345

theorem tailTrace_5903217 : CollatzResearch.WordTrace tailWord_5903217 prefixEnd_5903217 336798636532503930004345 := by
  unfold tailWord_5903217
  simp only [CollatzResearch.WordTrace]
  refine ⟨215308012254660473042667905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143538674836440315361778603 215308012254660473042667905)
  ·
    refine ⟨161481009190995354782000929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215308012254660473042667905 161481009190995354782000929)
    ·
      refine ⟨121110756893246516086500697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161481009190995354782000929 121110756893246516086500697)
      ·
        refine ⟨90833067669934887064875523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121110756893246516086500697 90833067669934887064875523)
        ·
          refine ⟨136249601504902330597313285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90833067669934887064875523 136249601504902330597313285)
          ·
            refine ⟨25546800282169186986996241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136249601504902330597313285 25546800282169186986996241)
            ·
              refine ⟨19160100211626890240247181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25546800282169186986996241 19160100211626890240247181)
              ·
                refine ⟨7185037579360083840092693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19160100211626890240247181 7185037579360083840092693)
                ·
                  refine ⟨336798636532503930004345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7185037579360083840092693 336798636532503930004345)
                  ·
                    rfl

theorem cell23_5903217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_5903217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903217 prefixEnd_5903217 := by exact prefixLift 5903217
  have htrace : WordTrace (prefixWord ++ tailWord_5903217) baseStart_5903217 baseEnd_5903217 := by
    simpa [prefixWord, tailWord_5903217, baseEnd_5903217] using wordTrace_append hprefix tailTrace_5903217
  have hstable : (prefixWord ++ tailWord_5903217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903217).length < 2 ^ (prefixWord ++ tailWord_5903217).sum := by decide
  have hdescent : baseEnd_5903217 < baseStart_5903217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903261 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_5903261 : Nat := 118140960795 + 5903261 * 2 ^ 59
def prefixEnd_5903261 : Nat := 4983230072969 + 3 ^ 40 * 5903261 * 2
def baseEnd_5903261 : Nat := 3031210321941333197888903

theorem tailTrace_5903261 : CollatzResearch.WordTrace tailWord_5903261 prefixEnd_5903261 3031210321941333197888903 := by
  unfold tailWord_5903261
  simp only [CollatzResearch.WordTrace]
  refine ⟨215309617066501068557269637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143539744711000712371513091 215309617066501068557269637)
  ·
    refine ⟨40370553199968950354488057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215309617066501068557269637 40370553199968950354488057)
    ·
      refine ⟨30277914899976712765866043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40370553199968950354488057 30277914899976712765866043)
      ·
        refine ⟨45416872349965069148799065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30277914899976712765866043 45416872349965069148799065)
        ·
          refine ⟨34062654262473801861599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45416872349965069148799065 34062654262473801861599299)
          ·
            refine ⟨51093981393710702792398949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34062654262473801861599299 51093981393710702792398949)
            ·
              refine ⟨9580121511320756773574803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51093981393710702792398949 9580121511320756773574803)
              ·
                refine ⟨14370182266981135160362205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9580121511320756773574803 14370182266981135160362205)
                ·
                  refine ⟨5388818350117925685135827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14370182266981135160362205 5388818350117925685135827)
                  ·
                    refine ⟨8083227525176888527703741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388818350117925685135827 8083227525176888527703741)
                    ·
                      refine ⟨3031210321941333197888903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083227525176888527703741 3031210321941333197888903)
                      ·
                        rfl

theorem cell23_5903261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_5903261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903261 prefixEnd_5903261 := by exact prefixLift 5903261
  have htrace : WordTrace (prefixWord ++ tailWord_5903261) baseStart_5903261 baseEnd_5903261 := by
    simpa [prefixWord, tailWord_5903261, baseEnd_5903261] using wordTrace_append hprefix tailTrace_5903261
  have hstable : (prefixWord ++ tailWord_5903261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903261).length < 2 ^ (prefixWord ++ tailWord_5903261).sum := by decide
  have hdescent : baseEnd_5903261 < baseStart_5903261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903267 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4]
def baseStart_5903267 : Nat := 118140960795 + 5903267 * 2 ^ 59
def prefixEnd_5903267 : Nat := 4983230072969 + 3 ^ 40 * 5903267 * 2
def baseEnd_5903267 : Nat := 3031213402825260174413875

theorem tailTrace_5903267 : CollatzResearch.WordTrace tailWord_5903267 prefixEnd_5903267 3031213402825260174413875 := by
  unfold tailWord_5903267
  simp only [CollatzResearch.WordTrace]
  refine ⟨215309835904479331581988055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143539890602986221054658703 215309835904479331581988055)
  ·
    refine ⟨322964753856718997372982083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215309835904479331581988055 322964753856718997372982083)
    ·
      refine ⟨484447130785078496059473125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322964753856718997372982083 484447130785078496059473125)
      ·
        refine ⟨90833837022202218011151211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 484447130785078496059473125 90833837022202218011151211)
        ·
          refine ⟨136250755533303327016726817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90833837022202218011151211 136250755533303327016726817)
          ·
            refine ⟨102188066649977495262545113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136250755533303327016726817 102188066649977495262545113)
            ·
              refine ⟨76641049987483121446908835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102188066649977495262545113 76641049987483121446908835)
              ·
                refine ⟨114961574981224682170363253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76641049987483121446908835 114961574981224682170363253)
                ·
                  refine ⟨10777647654489813953471555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114961574981224682170363253 10777647654489813953471555)
                  ·
                    refine ⟨16166471481734720930207333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10777647654489813953471555 16166471481734720930207333)
                    ·
                      refine ⟨3031213402825260174413875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16166471481734720930207333 3031213402825260174413875)
                      ·
                        rfl

theorem cell23_5903267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_5903267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903267 prefixEnd_5903267 := by exact prefixLift 5903267
  have htrace : WordTrace (prefixWord ++ tailWord_5903267) baseStart_5903267 baseEnd_5903267 := by
    simpa [prefixWord, tailWord_5903267, baseEnd_5903267] using wordTrace_append hprefix tailTrace_5903267
  have hstable : (prefixWord ++ tailWord_5903267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903267).length < 2 ^ (prefixWord ++ tailWord_5903267).sum := by decide
  have hdescent : baseEnd_5903267 < baseStart_5903267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903281 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_5903281 : Nat := 118140960795 + 5903281 * 2 ^ 59
def prefixEnd_5903281 : Nat := 4983230072969 + 3 ^ 40 * 5903281 * 2
def baseEnd_5903281 : Nat := 1010406863851474373212937

theorem tailTrace_5903281 : CollatzResearch.WordTrace tailWord_5903281 prefixEnd_5903281 1010406863851474373212937 := by
  unfold tailWord_5903281
  simp only [CollatzResearch.WordTrace]
  refine ⟨215310346526428611972997697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143540231017619074648665131 215310346526428611972997697)
  ·
    refine ⟨161482759894821458979748273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215310346526428611972997697 161482759894821458979748273)
    ·
      refine ⟨121112069921116094234811205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161482759894821458979748273 121112069921116094234811205)
      ·
        refine ⟨22708513110209267669027101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121112069921116094234811205 22708513110209267669027101)
        ·
          refine ⟨8515692416328475375885163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22708513110209267669027101 8515692416328475375885163)
          ·
            refine ⟨12773538624492713063827745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515692416328475375885163 12773538624492713063827745)
            ·
              refine ⟨9580153968369534797870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12773538624492713063827745 9580153968369534797870809)
              ·
                refine ⟨7185115476277151098403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580153968369534797870809 7185115476277151098403107)
                ·
                  refine ⟨10777673214415726647604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185115476277151098403107 10777673214415726647604661)
                  ·
                    refine ⟨1010406863851474373212937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10777673214415726647604661 1010406863851474373212937)
                    ·
                      rfl

theorem cell23_5903281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_5903281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903281 prefixEnd_5903281 := by exact prefixLift 5903281
  have htrace : WordTrace (prefixWord ++ tailWord_5903281) baseStart_5903281 baseEnd_5903281 := by
    simpa [prefixWord, tailWord_5903281, baseEnd_5903281] using wordTrace_append hprefix tailTrace_5903281
  have hstable : (prefixWord ++ tailWord_5903281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903281).length < 2 ^ (prefixWord ++ tailWord_5903281).sum := by decide
  have hdescent : baseEnd_5903281 < baseStart_5903281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903294 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5903294 : Nat := 118140960795 + 5903294 * 2 ^ 59
def prefixEnd_5903294 : Nat := 4983230072969 + 3 ^ 40 * 5903294 * 2
def baseEnd_5903294 : Nat := 1010409088934310522925417

theorem tailTrace_5903294 : CollatzResearch.WordTrace tailWord_5903294 prefixEnd_5903294 1010409088934310522925417 := by
  unfold tailWord_5903294
  simp only [CollatzResearch.WordTrace]
  refine ⟨26913852584422689399152617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143540547116921010128813957 26913852584422689399152617)
  ·
    refine ⟨20185389438317017049364463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26913852584422689399152617 20185389438317017049364463)
    ·
      refine ⟨30278084157475525574046695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20185389438317017049364463 30278084157475525574046695)
      ·
        refine ⟨45417126236213288361070043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30278084157475525574046695 45417126236213288361070043)
        ·
          refine ⟨68125689354319932541605065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45417126236213288361070043 68125689354319932541605065)
          ·
            refine ⟨51094267015739949406203799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68125689354319932541605065 51094267015739949406203799)
            ·
              refine ⟨76641400523609924109305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51094267015739949406203799 76641400523609924109305699)
              ·
                refine ⟨114962100785414886163958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76641400523609924109305699 114962100785414886163958549)
                ·
                  refine ⟨5388848474316322788935557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114962100785414886163958549 5388848474316322788935557)
                  ·
                    refine ⟨1010409088934310522925417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5388848474316322788935557 1010409088934310522925417)
                    ·
                      rfl

theorem cell23_5903294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5903294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903294 prefixEnd_5903294 := by exact prefixLift 5903294
  have htrace : WordTrace (prefixWord ++ tailWord_5903294) baseStart_5903294 baseEnd_5903294 := by
    simpa [prefixWord, tailWord_5903294, baseEnd_5903294] using wordTrace_append hprefix tailTrace_5903294
  have hstable : (prefixWord ++ tailWord_5903294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903294).length < 2 ^ (prefixWord ++ tailWord_5903294).sum := by decide
  have hdescent : baseEnd_5903294 < baseStart_5903294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903307 : List Nat := [1, 1, 1, 1, 3, 7, 9]
def baseStart_5903307 : Nat := 118140960795 + 5903307 * 2 ^ 59
def prefixEnd_5903307 : Nat := 4983230072969 + 3 ^ 40 * 5903307 * 2
def baseEnd_5903307 : Nat := 37422641259894321208811

theorem tailTrace_5903307 : CollatzResearch.WordTrace tailWord_5903307 prefixEnd_5903307 37422641259894321208811 := by
  unfold tailWord_5903307
  simp only [CollatzResearch.WordTrace]
  refine ⟨215311294824334418413444175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143540863216222945608962783 215311294824334418413444175)
  ·
    refine ⟨322966942236501627620166263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215311294824334418413444175 322966942236501627620166263)
    ·
      refine ⟨484450413354752441430249395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322966942236501627620166263 484450413354752441430249395)
      ·
        refine ⟨726675620032128662145374093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484450413354752441430249395 726675620032128662145374093)
        ·
          refine ⟨272503357512048248304515285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726675620032128662145374093 272503357512048248304515285)
          ·
            refine ⟨6386797441688630819637077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 272503357512048248304515285 6386797441688630819637077)
            ·
              refine ⟨37422641259894321208811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6386797441688630819637077 37422641259894321208811)
              ·
                rfl

theorem cell23_5903307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 9].length) (baseStart_5903307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903307 prefixEnd_5903307 := by exact prefixLift 5903307
  have htrace : WordTrace (prefixWord ++ tailWord_5903307) baseStart_5903307 baseEnd_5903307 := by
    simpa [prefixWord, tailWord_5903307, baseEnd_5903307] using wordTrace_append hprefix tailTrace_5903307
  have hstable : (prefixWord ++ tailWord_5903307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903307).length < 2 ^ (prefixWord ++ tailWord_5903307).sum := by decide
  have hdescent : baseEnd_5903307 < baseStart_5903307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903314 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5903314 : Nat := 118140960795 + 5903314 * 2 ^ 59
def prefixEnd_5903314 : Nat := 4983230072969 + 3 ^ 40 * 5903314 * 2
def baseEnd_5903314 : Nat := 3031237536416021490526159

theorem tailTrace_5903314 : CollatzResearch.WordTrace tailWord_5903314 prefixEnd_5903314 3031237536416021490526159 := by
  unfold tailWord_5903314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53827887533827264652237249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143541033423539372405965997 53827887533827264652237249)
  ·
    refine ⟨40370915650370448489177937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53827887533827264652237249 40370915650370448489177937)
    ·
      refine ⟨30278186737777836366883453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40370915650370448489177937 30278186737777836366883453)
      ·
        refine ⟨11354320026666688637581295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30278186737777836366883453 11354320026666688637581295)
        ·
          refine ⟨17031480040000032956371943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354320026666688637581295 17031480040000032956371943)
          ·
            refine ⟨25547220060000049434557915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031480040000032956371943 25547220060000049434557915)
            ·
              refine ⟨38320830090000074151836873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25547220060000049434557915 38320830090000074151836873)
              ·
                refine ⟨28740622567500055613877655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38320830090000074151836873 28740622567500055613877655)
                ·
                  refine ⟨43110933851250083420816483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28740622567500055613877655 43110933851250083420816483)
                  ·
                    refine ⟨64666400776875125131224725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43110933851250083420816483 64666400776875125131224725)
                    ·
                      refine ⟨3031237536416021490526159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64666400776875125131224725 3031237536416021490526159)
                      ·
                        rfl

theorem cell23_5903314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5903314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903314 prefixEnd_5903314 := by exact prefixLift 5903314
  have htrace : WordTrace (prefixWord ++ tailWord_5903314) baseStart_5903314 baseEnd_5903314 := by
    simpa [prefixWord, tailWord_5903314, baseEnd_5903314] using wordTrace_append hprefix tailTrace_5903314
  have hstable : (prefixWord ++ tailWord_5903314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903314).length < 2 ^ (prefixWord ++ tailWord_5903314).sum := by decide
  have hdescent : baseEnd_5903314 < baseStart_5903314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903338 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_5903338 : Nat := 118140960795 + 5903338 * 2 ^ 59
def prefixEnd_5903338 : Nat := 4983230072969 + 3 ^ 40 * 5903338 * 2
def baseEnd_5903338 : Nat := 3031249859951729396626049

theorem tailTrace_5903338 : CollatzResearch.WordTrace tailWord_5903338 prefixEnd_5903338 3031249859951729396626049 := by
  unfold tailWord_5903338
  simp only [CollatzResearch.WordTrace]
  refine ⟨53828106371805527676955667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143541616991481407138548445 53828106371805527676955667)
  ·
    refine ⟨80742159557708291515433501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53828106371805527676955667 80742159557708291515433501)
    ·
      refine ⟨30278309834140609318287563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80742159557708291515433501 30278309834140609318287563)
      ·
        refine ⟨45417464751210913977431345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30278309834140609318287563 45417464751210913977431345)
        ·
          refine ⟨34063098563408185483073509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45417464751210913977431345 34063098563408185483073509)
          ·
            refine ⟨6386830980639034778076283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34063098563408185483073509 6386830980639034778076283)
            ·
              refine ⟨9580246470958552167114425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386830980639034778076283 9580246470958552167114425)
              ·
                refine ⟨7185184853218914125335819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580246470958552167114425 7185184853218914125335819)
                ·
                  refine ⟨10777777279828371188003729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185184853218914125335819 10777777279828371188003729)
                  ·
                    refine ⟨8083332959871278391002797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10777777279828371188003729 8083332959871278391002797)
                    ·
                      refine ⟨3031249859951729396626049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083332959871278391002797 3031249859951729396626049)
                      ·
                        rfl

theorem cell23_5903338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_5903338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903338 prefixEnd_5903338 := by exact prefixLift 5903338
  have htrace : WordTrace (prefixWord ++ tailWord_5903338) baseStart_5903338 baseEnd_5903338 := by
    simpa [prefixWord, tailWord_5903338, baseEnd_5903338] using wordTrace_append hprefix tailTrace_5903338
  have hstable : (prefixWord ++ tailWord_5903338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903338).length < 2 ^ (prefixWord ++ tailWord_5903338).sum := by decide
  have hdescent : baseEnd_5903338 < baseStart_5903338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903368 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_5903368 : Nat := 118140960795 + 5903368 * 2 ^ 59
def prefixEnd_5903368 : Nat := 4983230072969 + 3 ^ 40 * 5903368 * 2
def baseEnd_5903368 : Nat := 3031265264371364279250911

theorem tailTrace_5903368 : CollatzResearch.WordTrace tailWord_5903368 prefixEnd_5903368 3031265264371364279250911 := by
  unfold tailWord_5903368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107656759838556712915707379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143542346451408950554276505 107656759838556712915707379)
  ·
    refine ⟨161485139757835069373561069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107656759838556712915707379 161485139757835069373561069)
    ·
      refine ⟨60556927409188151015085401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161485139757835069373561069 60556927409188151015085401)
      ·
        refine ⟨45417695556891113261314051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60556927409188151015085401 45417695556891113261314051)
        ·
          refine ⟨68126543335336669891971077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45417695556891113261314051 68126543335336669891971077)
          ·
            refine ⟨12773726875375625604744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68126543335336669891971077 12773726875375625604744577)
            ·
              refine ⟨9580295156531719203558433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12773726875375625604744577 9580295156531719203558433)
              ·
                refine ⟨7185221367398789402668825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9580295156531719203558433 7185221367398789402668825)
                ·
                  refine ⟨5388916025549092052001619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185221367398789402668825 5388916025549092052001619)
                  ·
                    refine ⟨8083374038323638078002429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388916025549092052001619 8083374038323638078002429)
                    ·
                      refine ⟨3031265264371364279250911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083374038323638078002429 3031265264371364279250911)
                      ·
                        rfl

theorem cell23_5903368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_5903368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903368 prefixEnd_5903368 := by exact prefixLift 5903368
  have htrace : WordTrace (prefixWord ++ tailWord_5903368) baseStart_5903368 baseEnd_5903368 := by
    simpa [prefixWord, tailWord_5903368, baseEnd_5903368] using wordTrace_append hprefix tailTrace_5903368
  have hstable : (prefixWord ++ tailWord_5903368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903368).length < 2 ^ (prefixWord ++ tailWord_5903368).sum := by decide
  have hdescent : baseEnd_5903368 < baseStart_5903368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903374 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5903374 : Nat := 118140960795 + 5903374 * 2 ^ 59
def prefixEnd_5903374 : Nat := 4983230072969 + 3 ^ 40 * 5903374 * 2
def baseEnd_5903374 : Nat := 3031268345255291255775883

theorem tailTrace_5903374 : CollatzResearch.WordTrace tailWord_5903374 prefixEnd_5903374 3031268345255291255775883 := by
  unfold tailWord_5903374
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914217314386461107016647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143542492343394459237422117 26914217314386461107016647)
  ·
    refine ⟨40371325971579691660524971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914217314386461107016647 40371325971579691660524971)
    ·
      refine ⟨60556988957369537490787457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40371325971579691660524971 60556988957369537490787457)
      ·
        refine ⟨45417741718027153118090593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60556988957369537490787457 45417741718027153118090593)
        ·
          refine ⟨34063306288520364838567945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45417741718027153118090593 34063306288520364838567945)
          ·
            refine ⟨25547479716390273628925959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34063306288520364838567945 25547479716390273628925959)
            ·
              refine ⟨38321219574585410443388939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25547479716390273628925959 38321219574585410443388939)
              ·
                refine ⟨57481829361878115665083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38321219574585410443388939 57481829361878115665083409)
                ·
                  refine ⟨43111372021408586748812557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57481829361878115665083409 43111372021408586748812557)
                  ·
                    refine ⟨16166764508028220030804709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43111372021408586748812557 16166764508028220030804709)
                    ·
                      refine ⟨3031268345255291255775883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16166764508028220030804709 3031268345255291255775883)
                      ·
                        rfl

theorem cell23_5903374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5903374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903374 prefixEnd_5903374 := by exact prefixLift 5903374
  have htrace : WordTrace (prefixWord ++ tailWord_5903374) baseStart_5903374 baseEnd_5903374 := by
    simpa [prefixWord, tailWord_5903374, baseEnd_5903374] using wordTrace_append hprefix tailTrace_5903374
  have hstable : (prefixWord ++ tailWord_5903374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903374).length < 2 ^ (prefixWord ++ tailWord_5903374).sum := by decide
  have hdescent : baseEnd_5903374 < baseStart_5903374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903377 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_5903377 : Nat := 118140960795 + 5903377 * 2 ^ 59
def prefixEnd_5903377 : Nat := 4983230072969 + 3 ^ 40 * 5903377 * 2
def baseEnd_5903377 : Nat := 3031269885697254744038369

theorem tailTrace_5903377 : CollatzResearch.WordTrace tailWord_5903377 prefixEnd_5903377 3031269885697254744038369 := by
  unfold tailWord_5903377
  simp only [CollatzResearch.WordTrace]
  refine ⟨215313847934080820368492385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143542565289387213578994923 215313847934080820368492385)
  ·
    refine ⟨161485385950560615276369289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215313847934080820368492385 161485385950560615276369289)
    ·
      refine ⟨121114039462920461457276967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161485385950560615276369289 121114039462920461457276967)
      ·
        refine ⟨181671059194380692185915451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121114039462920461457276967 181671059194380692185915451)
        ·
          refine ⟨272506588791571038278873177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181671059194380692185915451 272506588791571038278873177)
          ·
            refine ⟨204379941593678278709154883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272506588791571038278873177 204379941593678278709154883)
            ·
              refine ⟨306569912390517418063732325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204379941593678278709154883 306569912390517418063732325)
              ·
                refine ⟨57481858573222015886949811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 306569912390517418063732325 57481858573222015886949811)
                ·
                  refine ⟨86222787859833023830424717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57481858573222015886949811 86222787859833023830424717)
                  ·
                    refine ⟨32333545447437383936409269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86222787859833023830424717 32333545447437383936409269)
                    ·
                      refine ⟨3031269885697254744038369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32333545447437383936409269 3031269885697254744038369)
                      ·
                        rfl

theorem cell23_5903377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_5903377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903377 prefixEnd_5903377 := by exact prefixLift 5903377
  have htrace : WordTrace (prefixWord ++ tailWord_5903377) baseStart_5903377 baseEnd_5903377 := by
    simpa [prefixWord, tailWord_5903377, baseEnd_5903377] using wordTrace_append hprefix tailTrace_5903377
  have hstable : (prefixWord ++ tailWord_5903377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903377).length < 2 ^ (prefixWord ++ tailWord_5903377).sum := by decide
  have hdescent : baseEnd_5903377 < baseStart_5903377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903384 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_5903384 : Nat := 118140960795 + 5903384 * 2 ^ 59
def prefixEnd_5903384 : Nat := 4983230072969 + 3 ^ 40 * 5903384 * 2
def baseEnd_5903384 : Nat := 1010424493353945405550279

theorem tailTrace_5903384 : CollatzResearch.WordTrace tailWord_5903384 prefixEnd_5903384 1010424493353945405550279 := by
  unfold tailWord_5903384
  simp only [CollatzResearch.WordTrace]
  refine ⟨107657051622527730281998603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143542735496703640375998137 107657051622527730281998603)
  ·
    refine ⟨161485577433791595422997905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107657051622527730281998603 161485577433791595422997905)
    ·
      refine ⟨121114183075343696567248429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161485577433791595422997905 121114183075343696567248429)
      ·
        refine ⟨45417818653253886212718161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121114183075343696567248429 45417818653253886212718161)
        ·
          refine ⟨34063363989940414659538621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45417818653253886212718161 34063363989940414659538621)
          ·
            refine ⟨12773761496227655497326983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34063363989940414659538621 12773761496227655497326983)
            ·
              refine ⟨19160642244341483245990475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773761496227655497326983 19160642244341483245990475)
              ·
                refine ⟨28740963366512224868985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19160642244341483245990475 28740963366512224868985713)
                ·
                  refine ⟨21555722524884168651739285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28740963366512224868985713 21555722524884168651739285)
                  ·
                    refine ⟨1010424493353945405550279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21555722524884168651739285 1010424493353945405550279)
                    ·
                      rfl

theorem cell23_5903384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_5903384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903384 prefixEnd_5903384 := by exact prefixLift 5903384
  have htrace : WordTrace (prefixWord ++ tailWord_5903384) baseStart_5903384 baseEnd_5903384 := by
    simpa [prefixWord, tailWord_5903384, baseEnd_5903384] using wordTrace_append hprefix tailTrace_5903384
  have hstable : (prefixWord ++ tailWord_5903384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903384).length < 2 ^ (prefixWord ++ tailWord_5903384).sum := by decide
  have hdescent : baseEnd_5903384 < baseStart_5903384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903391 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 4, 2]
def baseStart_5903391 : Nat := 118140960795 + 5903391 * 2 ^ 59
def prefixEnd_5903391 : Nat := 4983230072969 + 3 ^ 40 * 5903391 * 2
def baseEnd_5903391 : Nat := 3031277074426417689263305

theorem tailTrace_5903391 : CollatzResearch.WordTrace tailWord_5903391 prefixEnd_5903391 3031277074426417689263305 := by
  unfold tailWord_5903391
  simp only [CollatzResearch.WordTrace]
  refine ⟨215314358556030100759502027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143542905704020067173001351 215314358556030100759502027)
  ·
    refine ⟨322971537834045151139253041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215314358556030100759502027 322971537834045151139253041)
    ·
      refine ⟨242228653375533863354439781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322971537834045151139253041 242228653375533863354439781)
      ·
        refine ⟨45417872507912599378957459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242228653375533863354439781 45417872507912599378957459)
        ·
          refine ⟨68126808761868899068436189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45417872507912599378957459 68126808761868899068436189)
          ·
            refine ⟨25547553285700837150663571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68126808761868899068436189 25547553285700837150663571)
            ·
              refine ⟨38321329928551255725995357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25547553285700837150663571 38321329928551255725995357)
              ·
                refine ⟨14370498723206720897248259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38321329928551255725995357 14370498723206720897248259)
                ·
                  refine ⟨21555748084810081345872389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14370498723206720897248259 21555748084810081345872389)
                  ·
                    refine ⟨4041702765901890252351073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21555748084810081345872389 4041702765901890252351073)
                    ·
                      refine ⟨3031277074426417689263305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041702765901890252351073 3031277074426417689263305)
                      ·
                        rfl

theorem cell23_5903391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_5903391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903391 prefixEnd_5903391 := by exact prefixLift 5903391
  have htrace : WordTrace (prefixWord ++ tailWord_5903391) baseStart_5903391 baseEnd_5903391 := by
    simpa [prefixWord, tailWord_5903391, baseEnd_5903391] using wordTrace_append hprefix tailTrace_5903391
  have hstable : (prefixWord ++ tailWord_5903391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903391).length < 2 ^ (prefixWord ++ tailWord_5903391).sum := by decide
  have hdescent : baseEnd_5903391 < baseStart_5903391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903412 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5903412 : Nat := 118140960795 + 5903412 * 2 ^ 59
def prefixEnd_5903412 : Nat := 4983230072969 + 3 ^ 40 * 5903412 * 2
def baseEnd_5903412 : Nat := 3031287857520162107100709

theorem tailTrace_5903412 : CollatzResearch.WordTrace tailWord_5903412 prefixEnd_5903412 3031287857520162107100709 := by
  unfold tailWord_5903412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107657562244477010673008245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143543416325969347564010993 107657562244477010673008245)
  ·
    refine ⟨10092896460419719750594523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107657562244477010673008245 10092896460419719750594523)
    ·
      refine ⟨15139344690629579625891785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10092896460419719750594523 15139344690629579625891785)
      ·
        refine ⟨11354508517972184719418839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15139344690629579625891785 11354508517972184719418839)
        ·
          refine ⟨17031762776958277079128259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354508517972184719418839 17031762776958277079128259)
          ·
            refine ⟨25547644165437415618692389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17031762776958277079128259 25547644165437415618692389)
            ·
              refine ⟨4790183281019515428504823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25547644165437415618692389 4790183281019515428504823)
              ·
                refine ⟨7185274921529273142757235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790183281019515428504823 7185274921529273142757235)
                ·
                  refine ⟨10777912382293909714135853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185274921529273142757235 10777912382293909714135853)
                  ·
                    refine ⟨4041717143360216142800945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10777912382293909714135853 4041717143360216142800945)
                    ·
                      refine ⟨3031287857520162107100709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041717143360216142800945 3031287857520162107100709)
                      ·
                        rfl

theorem cell23_5903412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5903412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903412 prefixEnd_5903412 := by exact prefixLift 5903412
  have htrace : WordTrace (prefixWord ++ tailWord_5903412) baseStart_5903412 baseEnd_5903412 := by
    simpa [prefixWord, tailWord_5903412, baseEnd_5903412] using wordTrace_append hprefix tailTrace_5903412
  have hstable : (prefixWord ++ tailWord_5903412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903412).length < 2 ^ (prefixWord ++ tailWord_5903412).sum := by decide
  have hdescent : baseEnd_5903412 < baseStart_5903412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903424 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_5903424 : Nat := 118140960795 + 5903424 * 2 ^ 59
def prefixEnd_5903424 : Nat := 4983230072969 + 3 ^ 40 * 5903424 * 2
def baseEnd_5903424 : Nat := 3031294019288016060150653

theorem tailTrace_5903424 : CollatzResearch.WordTrace tailWord_5903424 prefixEnd_5903424 3031294019288016060150653 := by
  unfold tailWord_5903424
  simp only [CollatzResearch.WordTrace]
  refine ⟨107657781082455273697726663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143543708109940364930302217 107657781082455273697726663)
  ·
    refine ⟨161486671623682910546589995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107657781082455273697726663 161486671623682910546589995)
    ·
      refine ⟨242230007435524365819884993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161486671623682910546589995 242230007435524365819884993)
      ·
        refine ⟨181672505576643274364913745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242230007435524365819884993 181672505576643274364913745)
        ·
          refine ⟨136254379182482455773685309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181672505576643274364913745 136254379182482455773685309)
          ·
            refine ⟨51095392193430920915131991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136254379182482455773685309 51095392193430920915131991)
            ·
              refine ⟨76643088290146381372697987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51095392193430920915131991 76643088290146381372697987)
              ·
                refine ⟨114964632435219572059046981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76643088290146381372697987 114964632435219572059046981)
                ·
                  refine ⟨21555868581603669761071309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114964632435219572059046981 21555868581603669761071309)
                  ·
                    refine ⟨8083450718101376160401741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21555868581603669761071309 8083450718101376160401741)
                    ·
                      refine ⟨3031294019288016060150653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083450718101376160401741 3031294019288016060150653)
                      ·
                        rfl

theorem cell23_5903424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_5903424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903424 prefixEnd_5903424 := by exact prefixLift 5903424
  have htrace : WordTrace (prefixWord ++ tailWord_5903424) baseStart_5903424 baseEnd_5903424 := by
    simpa [prefixWord, tailWord_5903424, baseEnd_5903424] using wordTrace_append hprefix tailTrace_5903424
  have hstable : (prefixWord ++ tailWord_5903424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903424).length < 2 ^ (prefixWord ++ tailWord_5903424).sum := by decide
  have hdescent : baseEnd_5903424 < baseStart_5903424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903425 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5903425 : Nat := 118140960795 + 5903425 * 2 ^ 59
def prefixEnd_5903425 : Nat := 4983230072969 + 3 ^ 40 * 5903425 * 2
def baseEnd_5903425 : Nat := 3031294532768670556238149

theorem tailTrace_5903425 : CollatzResearch.WordTrace tailWord_5903425 prefixEnd_5903425 3031294532768670556238149 := by
  unfold tailWord_5903425
  simp only [CollatzResearch.WordTrace]
  refine ⟨215315598637906924566239729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143543732425271283044159819 215315598637906924566239729)
  ·
    refine ⟨161486698978430193424679797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215315598637906924566239729 161486698978430193424679797)
    ·
      refine ⟨15139378029227830633563731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161486698978430193424679797 15139378029227830633563731)
      ·
        refine ⟨22709067043841745950345597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139378029227830633563731 22709067043841745950345597)
        ·
          refine ⟨8515900141440654731379599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22709067043841745950345597 8515900141440654731379599)
          ·
            refine ⟨12773850212160982097069399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515900141440654731379599 12773850212160982097069399)
            ·
              refine ⟨19160775318241473145604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773850212160982097069399 19160775318241473145604099)
              ·
                refine ⟨28741162977362209718406149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19160775318241473145604099 28741162977362209718406149)
                ·
                  refine ⟨5388968058255414322201153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28741162977362209718406149 5388968058255414322201153)
                  ·
                    refine ⟨4041726043691560741650865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5388968058255414322201153 4041726043691560741650865)
                    ·
                      refine ⟨3031294532768670556238149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041726043691560741650865 3031294532768670556238149)
                      ·
                        rfl

theorem cell23_5903425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5903425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903425 prefixEnd_5903425 := by exact prefixLift 5903425
  have htrace : WordTrace (prefixWord ++ tailWord_5903425) baseStart_5903425 baseEnd_5903425 := by
    simpa [prefixWord, tailWord_5903425, baseEnd_5903425] using wordTrace_append hprefix tailTrace_5903425
  have hstable : (prefixWord ++ tailWord_5903425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903425).length < 2 ^ (prefixWord ++ tailWord_5903425).sum := by decide
  have hdescent : baseEnd_5903425 < baseStart_5903425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903431 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 5]
def baseStart_5903431 : Nat := 118140960795 + 5903431 * 2 ^ 59
def prefixEnd_5903431 : Nat := 4983230072969 + 3 ^ 40 * 5903431 * 2
def baseEnd_5903431 : Nat := 336810845961399725862569

theorem tailTrace_5903431 : CollatzResearch.WordTrace tailWord_5903431 prefixEnd_5903431 336810845961399725862569 := by
  unfold tailWord_5903431
  simp only [CollatzResearch.WordTrace]
  refine ⟨215315817475885187590958147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143543878317256791727305431 215315817475885187590958147)
  ·
    refine ⟨322973726213827781386437221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215315817475885187590958147 322973726213827781386437221)
    ·
      refine ⟨60557573665092709009956979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322973726213827781386437221 60557573665092709009956979)
      ·
        refine ⟨90836360497639063514935469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60557573665092709009956979 90836360497639063514935469)
        ·
          refine ⟨34063635186614648818100801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90836360497639063514935469 34063635186614648818100801)
          ·
            refine ⟨25547726389960986613575601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34063635186614648818100801 25547726389960986613575601)
            ·
              refine ⟨19160794792470739960181701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25547726389960986613575601 19160794792470739960181701)
              ·
                refine ⟨3592649023588263742534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19160794792470739960181701 3592649023588263742534069)
                ·
                  refine ⟨336810845961399725862569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3592649023588263742534069 336810845961399725862569)
                  ·
                    rfl

theorem cell23_5903431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 5].length) (baseStart_5903431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903431 prefixEnd_5903431 := by exact prefixLift 5903431
  have htrace : WordTrace (prefixWord ++ tailWord_5903431) baseStart_5903431 baseEnd_5903431 := by
    simpa [prefixWord, tailWord_5903431, baseEnd_5903431] using wordTrace_append hprefix tailTrace_5903431
  have hstable : (prefixWord ++ tailWord_5903431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903431).length < 2 ^ (prefixWord ++ tailWord_5903431).sum := by decide
  have hdescent : baseEnd_5903431 < baseStart_5903431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903442 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_5903442 : Nat := 118140960795 + 5903442 * 2 ^ 59
def prefixEnd_5903442 : Nat := 4983230072969 + 3 ^ 40 * 5903442 * 2
def baseEnd_5903442 : Nat := 3031303261939796989725571

theorem tailTrace_5903442 : CollatzResearch.WordTrace tailWord_5903442 prefixEnd_5903442 3031303261939796989725571 := by
  unfold tailWord_5903442
  simp only [CollatzResearch.WordTrace]
  refine ⟨53829054669711334117402145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143544145785896890979739053 53829054669711334117402145)
  ·
    refine ⟨40371791002283500588051609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53829054669711334117402145 40371791002283500588051609)
    ·
      refine ⟨30278843251712625441038707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40371791002283500588051609 30278843251712625441038707)
      ·
        refine ⟨45418264877568938161558061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30278843251712625441038707 45418264877568938161558061)
        ·
          refine ⟨17031849329088351810584273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45418264877568938161558061 17031849329088351810584273)
          ·
            refine ⟨12773886996816263857938205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17031849329088351810584273 12773886996816263857938205)
            ·
              refine ⟨4790207623806098946726827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12773886996816263857938205 4790207623806098946726827)
              ·
                refine ⟨7185311435709148420090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790207623806098946726827 7185311435709148420090241)
                ·
                  refine ⟨5388983576781861315067681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185311435709148420090241 5388983576781861315067681)
                  ·
                    refine ⟨4041737682586395986300761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5388983576781861315067681 4041737682586395986300761)
                    ·
                      refine ⟨3031303261939796989725571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041737682586395986300761 3031303261939796989725571)
                      ·
                        rfl

theorem cell23_5903442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_5903442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903442 prefixEnd_5903442 := by exact prefixLift 5903442
  have htrace : WordTrace (prefixWord ++ tailWord_5903442) baseStart_5903442 baseEnd_5903442 := by
    simpa [prefixWord, tailWord_5903442, baseEnd_5903442] using wordTrace_append hprefix tailTrace_5903442
  have hstable : (prefixWord ++ tailWord_5903442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903442).length < 2 ^ (prefixWord ++ tailWord_5903442).sum := by decide
  have hdescent : baseEnd_5903442 < baseStart_5903442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903444 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_5903444 : Nat := 118140960795 + 5903444 * 2 ^ 59
def prefixEnd_5903444 : Nat := 4983230072969 + 3 ^ 40 * 5903444 * 2
def baseEnd_5903444 : Nat := 1010434762967035327300187

theorem tailTrace_5903444 : CollatzResearch.WordTrace tailWord_5903444 prefixEnd_5903444 1010434762967035327300187 := by
  unfold tailWord_5903444
  simp only [CollatzResearch.WordTrace]
  refine ⟨107658145812419045405590693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143544194416558727207454257 107658145812419045405590693)
  ·
    refine ⟨20185902339828571013548255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107658145812419045405590693 20185902339828571013548255)
    ·
      refine ⟨30278853509742856520322383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20185902339828571013548255 30278853509742856520322383)
      ·
        refine ⟨45418280264614284780483575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30278853509742856520322383 45418280264614284780483575)
        ·
          refine ⟨68127420396921427170725363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45418280264614284780483575 68127420396921427170725363)
          ·
            refine ⟨102191130595382140756088045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68127420396921427170725363 102191130595382140756088045)
            ·
              refine ⟨38321673973268302783533017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102191130595382140756088045 38321673973268302783533017)
              ·
                refine ⟨28741255479951227087649763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38321673973268302783533017 28741255479951227087649763)
                ·
                  refine ⟨43111883219926840631474645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28741255479951227087649763 43111883219926840631474645)
                  ·
                    refine ⟨1010434762967035327300187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43111883219926840631474645 1010434762967035327300187)
                    ·
                      rfl

theorem cell23_5903444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_5903444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903444 prefixEnd_5903444 := by exact prefixLift 5903444
  have htrace : WordTrace (prefixWord ++ tailWord_5903444) baseStart_5903444 baseEnd_5903444 := by
    simpa [prefixWord, tailWord_5903444, baseEnd_5903444] using wordTrace_append hprefix tailTrace_5903444
  have hstable : (prefixWord ++ tailWord_5903444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903444).length < 2 ^ (prefixWord ++ tailWord_5903444).sum := by decide
  have hdescent : baseEnd_5903444 < baseStart_5903444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903571 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 6, 2]
def baseStart_5903571 : Nat := 118140960795 + 5903571 * 2 ^ 59
def prefixEnd_5903571 : Nat := 4983230072969 + 3 ^ 40 * 5903571 * 2
def baseEnd_5903571 : Nat := 3031369500944226985012477

theorem tailTrace_5903571 : CollatzResearch.WordTrace tailWord_5903571 prefixEnd_5903571 3031369500944226985012477 := by
  unfold tailWord_5903571
  simp only [CollatzResearch.WordTrace]
  refine ⟨215320923695377991501054567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143547282463585327667369711 215320923695377991501054567)
  ·
    refine ⟨322981385543066987251581851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215320923695377991501054567 322981385543066987251581851)
    ·
      refine ⟨484472078314600480877372777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322981385543066987251581851 484472078314600480877372777)
      ·
        refine ⟨363354058735950360658029583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484472078314600480877372777 363354058735950360658029583)
        ·
          refine ⟨545031088103925540987044375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363354058735950360658029583 545031088103925540987044375)
          ·
            refine ⟨817546632155888311480566563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545031088103925540987044375 817546632155888311480566563)
            ·
              refine ⟨1226319948233832467220849845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817546632155888311480566563 1226319948233832467220849845)
              ·
                refine ⟨114967495146921793801954673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1226319948233832467220849845 114967495146921793801954673)
                ·
                  refine ⟨86225621360191345351466005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114967495146921793801954673 86225621360191345351466005)
                  ·
                    refine ⟨4041826001258969313349969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86225621360191345351466005 4041826001258969313349969)
                    ·
                      refine ⟨3031369500944226985012477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041826001258969313349969 3031369500944226985012477)
                      ·
                        rfl

theorem cell23_5903571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6, 2].length) (baseStart_5903571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903571 prefixEnd_5903571 := by exact prefixLift 5903571
  have htrace : WordTrace (prefixWord ++ tailWord_5903571) baseStart_5903571 baseEnd_5903571 := by
    simpa [prefixWord, tailWord_5903571, baseEnd_5903571] using wordTrace_append hprefix tailTrace_5903571
  have hstable : (prefixWord ++ tailWord_5903571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903571).length < 2 ^ (prefixWord ++ tailWord_5903571).sum := by decide
  have hdescent : baseEnd_5903571 < baseStart_5903571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903585 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_5903585 : Nat := 118140960795 + 5903585 * 2 ^ 59
def prefixEnd_5903585 : Nat := 4983230072969 + 3 ^ 40 * 5903585 * 2
def baseEnd_5903585 : Nat := 1010458896557796643412471

theorem tailTrace_5903585 : CollatzResearch.WordTrace tailWord_5903585 prefixEnd_5903585 1010458896557796643412471 := by
  unfold tailWord_5903585
  simp only [CollatzResearch.WordTrace]
  refine ⟨215321434317327271892064209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143547622878218181261376139 215321434317327271892064209)
  ·
    refine ⟨161491075737995453919048157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215321434317327271892064209 161491075737995453919048157)
    ·
      refine ⟨60559153401748295219643059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161491075737995453919048157 60559153401748295219643059)
      ·
        refine ⟨90838730102622442829464589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60559153401748295219643059 90838730102622442829464589)
        ·
          refine ⟨34064523788483416061049221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90838730102622442829464589 34064523788483416061049221)
          ·
            refine ⟨6387098210340640511446729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34064523788483416061049221 6387098210340640511446729)
            ·
              refine ⟨4790323657755480383585047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6387098210340640511446729 4790323657755480383585047)
              ·
                refine ⟨7185485486633220575377571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790323657755480383585047 7185485486633220575377571)
                ·
                  refine ⟨10778228229949830863066357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185485486633220575377571 10778228229949830863066357)
                  ·
                    refine ⟨1010458896557796643412471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10778228229949830863066357 1010458896557796643412471)
                    ·
                      rfl

theorem cell23_5903585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_5903585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903585 prefixEnd_5903585 := by exact prefixLift 5903585
  have htrace : WordTrace (prefixWord ++ tailWord_5903585) baseStart_5903585 baseEnd_5903585 := by
    simpa [prefixWord, tailWord_5903585, baseEnd_5903585] using wordTrace_append hprefix tailTrace_5903585
  have hstable : (prefixWord ++ tailWord_5903585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903585).length < 2 ^ (prefixWord ++ tailWord_5903585).sum := by decide
  have hdescent : baseEnd_5903585 < baseStart_5903585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903615 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 2, 4]
def baseStart_5903615 : Nat := 118140960795 + 5903615 * 2 ^ 59
def prefixEnd_5903615 : Nat := 4983230072969 + 3 ^ 40 * 5903615 * 2
def baseEnd_5903615 : Nat := 1010464031364341604287425

theorem tailTrace_5903615 : CollatzResearch.WordTrace tailWord_5903615 prefixEnd_5903615 1010464031364341604287425 := by
  unfold tailWord_5903615
  simp only [CollatzResearch.WordTrace]
  refine ⟨215322528507218587015656299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143548352338145724677104199 215322528507218587015656299)
  ·
    refine ⟨322983792760827880523484449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215322528507218587015656299 322983792760827880523484449)
    ·
      refine ⟨242237844570620910392613337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322983792760827880523484449 242237844570620910392613337)
      ·
        refine ⟨181678383427965682794460003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242237844570620910392613337 181678383427965682794460003)
        ·
          refine ⟨272517575141948524191690005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181678383427965682794460003 272517575141948524191690005)
          ·
            refine ⟨12774261334778837071485469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272517575141948524191690005 12774261334778837071485469)
            ·
              refine ⟨4790348000542063901807051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12774261334778837071485469 4790348000542063901807051)
              ·
                refine ⟨7185522000813095852710577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790348000542063901807051 7185522000813095852710577)
                ·
                  refine ⟨5389141500609821889532933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185522000813095852710577 5389141500609821889532933)
                  ·
                    refine ⟨1010464031364341604287425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389141500609821889532933 1010464031364341604287425)
                    ·
                      rfl

theorem cell23_5903615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_5903615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903615 prefixEnd_5903615 := by exact prefixLift 5903615
  have htrace : WordTrace (prefixWord ++ tailWord_5903615) baseStart_5903615 baseEnd_5903615 := by
    simpa [prefixWord, tailWord_5903615, baseEnd_5903615] using wordTrace_append hprefix tailTrace_5903615
  have hstable : (prefixWord ++ tailWord_5903615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903615).length < 2 ^ (prefixWord ++ tailWord_5903615).sum := by decide
  have hdescent : baseEnd_5903615 < baseStart_5903615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903628 : List Nat := [2, 2, 1, 2, 2, 5, 2, 7]
def baseStart_5903628 : Nat := 118140960795 + 5903628 * 2 ^ 59
def prefixEnd_5903628 : Nat := 4983230072969 + 3 ^ 40 * 5903628 * 2
def baseEnd_5903628 : Nat := 112274028494130861555545

theorem tailTrace_5903628 : CollatzResearch.WordTrace tailWord_5903628 prefixEnd_5903628 112274028494130861555545 := by
  unfold tailWord_5903628
  simp only [CollatzResearch.WordTrace]
  refine ⟨107661501328085745117939769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143548668437447660157253025 107661501328085745117939769)
  ·
    refine ⟨80746125996064308838454827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107661501328085745117939769 80746125996064308838454827)
    ·
      refine ⟨121119188994096463257682241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80746125996064308838454827 121119188994096463257682241)
      ·
        refine ⟨90839391745572347443261681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121119188994096463257682241 90839391745572347443261681)
        ·
          refine ⟨68129543809179260582446261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90839391745572347443261681 68129543809179260582446261)
          ·
            refine ⟨6387144732110555679604337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68129543809179260582446261 6387144732110555679604337)
            ·
              refine ⟨4790358549082916759703253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6387144732110555679604337 4790358549082916759703253)
              ·
                refine ⟨112274028494130861555545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4790358549082916759703253 112274028494130861555545)
                ·
                  rfl

theorem cell23_5903628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 7].length) (baseStart_5903628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903628 prefixEnd_5903628 := by exact prefixLift 5903628
  have htrace : WordTrace (prefixWord ++ tailWord_5903628) baseStart_5903628 baseEnd_5903628 := by
    simpa [prefixWord, tailWord_5903628, baseEnd_5903628] using wordTrace_append hprefix tailTrace_5903628
  have hstable : (prefixWord ++ tailWord_5903628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903628).length < 2 ^ (prefixWord ++ tailWord_5903628).sum := by decide
  have hdescent : baseEnd_5903628 < baseStart_5903628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903656 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5903656 : Nat := 118140960795 + 5903656 * 2 ^ 59
def prefixEnd_5903656 : Nat := 4983230072969 + 3 ^ 40 * 5903656 * 2
def baseEnd_5903656 : Nat := 3031413146799859152449587

theorem tailTrace_5903656 : CollatzResearch.WordTrace tailWord_5903656 prefixEnd_5903656 3031413146799859152449587 := by
  unfold tailWord_5903656
  simp only [CollatzResearch.WordTrace]
  refine ⟨107662011950035025508949411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143549349266713367345265881 107662011950035025508949411)
  ·
    refine ⟨161493017925052538263424117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107662011950035025508949411 161493017925052538263424117)
    ·
      refine ⟨15139970430473675462196011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161493017925052538263424117 15139970430473675462196011)
      ·
        refine ⟨22709955645710513193294017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139970430473675462196011 22709955645710513193294017)
        ·
          refine ⟨17032466734282884894970513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22709955645710513193294017 17032466734282884894970513)
          ·
            refine ⟨12774350050712163671227885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17032466734282884894970513 12774350050712163671227885)
            ·
              refine ⟨4790381269017061376710457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12774350050712163671227885 4790381269017061376710457)
              ·
                refine ⟨3592785951762796032532843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790381269017061376710457 3592785951762796032532843)
                ·
                  refine ⟨5389178927644194048799265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592785951762796032532843 5389178927644194048799265)
                  ·
                    refine ⟨4041884195733145536599449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5389178927644194048799265 4041884195733145536599449)
                    ·
                      refine ⟨3031413146799859152449587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041884195733145536599449 3031413146799859152449587)
                      ·
                        rfl

theorem cell23_5903656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5903656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903656 prefixEnd_5903656 := by exact prefixLift 5903656
  have htrace : WordTrace (prefixWord ++ tailWord_5903656) baseStart_5903656 baseEnd_5903656 := by
    simpa [prefixWord, tailWord_5903656, baseEnd_5903656] using wordTrace_append hprefix tailTrace_5903656
  have hstable : (prefixWord ++ tailWord_5903656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903656).length < 2 ^ (prefixWord ++ tailWord_5903656).sum := by decide
  have hdescent : baseEnd_5903656 < baseStart_5903656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903712 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2]
def baseStart_5903712 : Nat := 118140960795 + 5903712 * 2 ^ 59
def prefixEnd_5903712 : Nat := 4983230072969 + 3 ^ 40 * 5903712 * 2
def baseEnd_5903712 : Nat := 3031441901716510933349329

theorem tailTrace_5903712 : CollatzResearch.WordTrace tailWord_5903712 prefixEnd_5903712 3031441901716510933349329 := by
  unfold tailWord_5903712
  simp only [CollatzResearch.WordTrace]
  refine ⟨107663033193933586290968695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143550710925244781721291593 107663033193933586290968695)
  ·
    refine ⟨161494549790900379436453043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107663033193933586290968695 161494549790900379436453043)
    ·
      refine ⟨242241824686350569154679565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161494549790900379436453043 242241824686350569154679565)
      ·
        refine ⟨90840684257381463433004837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242241824686350569154679565 90840684257381463433004837)
        ·
          refine ⟨17032628298259024393688407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90840684257381463433004837 17032628298259024393688407)
          ·
            refine ⟨25548942447388536590532611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17032628298259024393688407 25548942447388536590532611)
            ·
              refine ⟨38323413671082804885798917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548942447388536590532611 38323413671082804885798917)
              ·
                refine ⟨7185640063328025916087297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38323413671082804885798917 7185640063328025916087297)
                ·
                  refine ⟨5389230047496019437065473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185640063328025916087297 5389230047496019437065473)
                  ·
                    refine ⟨4041922535622014577799105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5389230047496019437065473 4041922535622014577799105)
                    ·
                      refine ⟨3031441901716510933349329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4041922535622014577799105 3031441901716510933349329)
                      ·
                        rfl

theorem cell23_5903712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_5903712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903712 prefixEnd_5903712 := by exact prefixLift 5903712
  have htrace : WordTrace (prefixWord ++ tailWord_5903712) baseStart_5903712 baseEnd_5903712 := by
    simpa [prefixWord, tailWord_5903712, baseEnd_5903712] using wordTrace_append hprefix tailTrace_5903712
  have hstable : (prefixWord ++ tailWord_5903712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903712).length < 2 ^ (prefixWord ++ tailWord_5903712).sum := by decide
  have hdescent : baseEnd_5903712 < baseStart_5903712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903728 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_5903728 : Nat := 118140960795 + 5903728 * 2 ^ 59
def prefixEnd_5903728 : Nat := 4983230072969 + 3 ^ 40 * 5903728 * 2
def baseEnd_5903728 : Nat := 3031450117406982870749255

theorem tailTrace_5903728 : CollatzResearch.WordTrace tailWord_5903728 prefixEnd_5903728 3031450117406982870749255 := by
  unfold tailWord_5903728
  simp only [CollatzResearch.WordTrace]
  refine ⟨107663324977904603657259919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143551099970539471543013225 107663324977904603657259919)
  ·
    refine ⟨161494987466856905485889879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107663324977904603657259919 161494987466856905485889879)
    ·
      refine ⟨242242481200285358228834819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161494987466856905485889879 242242481200285358228834819)
      ·
        refine ⟨363363721800428037343252229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242242481200285358228834819 363363721800428037343252229)
        ·
          refine ⟨68130697837580257001859793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363363721800428037343252229 68130697837580257001859793)
          ·
            refine ⟨51098023378185192751394845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68130697837580257001859793 51098023378185192751394845)
            ·
              refine ⟨19161758766819447281773067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51098023378185192751394845 19161758766819447281773067)
              ·
                refine ⟨28742638150229170922659601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19161758766819447281773067 28742638150229170922659601)
                ·
                  refine ⟨21556978612671878191994701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28742638150229170922659601 21556978612671878191994701)
                  ·
                    refine ⟨8083866979751954321998013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21556978612671878191994701 8083866979751954321998013)
                    ·
                      refine ⟨3031450117406982870749255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083866979751954321998013 3031450117406982870749255)
                      ·
                        rfl

theorem cell23_5903728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_5903728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903728 prefixEnd_5903728 := by exact prefixLift 5903728
  have htrace : WordTrace (prefixWord ++ tailWord_5903728) baseStart_5903728 baseEnd_5903728 := by
    simpa [prefixWord, tailWord_5903728, baseEnd_5903728] using wordTrace_append hprefix tailTrace_5903728
  have hstable : (prefixWord ++ tailWord_5903728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903728).length < 2 ^ (prefixWord ++ tailWord_5903728).sum := by decide
  have hdescent : baseEnd_5903728 < baseStart_5903728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903748 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_5903748 : Nat := 118140960795 + 5903748 * 2 ^ 59
def prefixEnd_5903748 : Nat := 4983230072969 + 3 ^ 40 * 5903748 * 2
def baseEnd_5903748 : Nat := 1010486795673357597499721

theorem tailTrace_5903748 : CollatzResearch.WordTrace tailWord_5903748 prefixEnd_5903748 1010486795673357597499721 := by
  unfold tailWord_5903748
  simp only [CollatzResearch.WordTrace]
  refine ⟨107663689707868375365123949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143551586277157833820165265 107663689707868375365123949)
  ·
    refine ⟨40373883640450640761921481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107663689707868375365123949 40373883640450640761921481)
    ·
      refine ⟨30280412730337980571441111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40373883640450640761921481 30280412730337980571441111)
      ·
        refine ⟨45420619095506970857161667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30280412730337980571441111 45420619095506970857161667)
        ·
          refine ⟨68130928643260456285742501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45420619095506970857161667 68130928643260456285742501)
          ·
            refine ⟨12774549120611335553576719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68130928643260456285742501 12774549120611335553576719)
            ·
              refine ⟨19161823680917003330365079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12774549120611335553576719 19161823680917003330365079)
              ·
                refine ⟨28742735521375504995547619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19161823680917003330365079 28742735521375504995547619)
                ·
                  refine ⟨43114103282063257493321429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28742735521375504995547619 43114103282063257493321429)
                  ·
                    refine ⟨1010486795673357597499721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43114103282063257493321429 1010486795673357597499721)
                    ·
                      rfl

theorem cell23_5903748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_5903748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903748 prefixEnd_5903748 := by exact prefixLift 5903748
  have htrace : WordTrace (prefixWord ++ tailWord_5903748) baseStart_5903748 baseEnd_5903748 := by
    simpa [prefixWord, tailWord_5903748, baseEnd_5903748] using wordTrace_append hprefix tailTrace_5903748
  have hstable : (prefixWord ++ tailWord_5903748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903748).length < 2 ^ (prefixWord ++ tailWord_5903748).sum := by decide
  have hdescent : baseEnd_5903748 < baseStart_5903748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903788 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_5903788 : Nat := 118140960795 + 5903788 * 2 ^ 59
def prefixEnd_5903788 : Nat := 4983230072969 + 3 ^ 40 * 5903788 * 2
def baseEnd_5903788 : Nat := 3031480926246252635998979

theorem tailTrace_5903788 : CollatzResearch.WordTrace tailWord_5903788 prefixEnd_5903788 3031480926246252635998979 := by
  unfold tailWord_5903788
  simp only [CollatzResearch.WordTrace]
  refine ⟨107664419167795918780852009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143552558890394558374469345 107664419167795918780852009)
  ·
    refine ⟨80748314375846939085639007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107664419167795918780852009 80748314375846939085639007)
    ·
      refine ⟨121122471563770408628458511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80748314375846939085639007 121122471563770408628458511)
      ·
        refine ⟨181683707345655612942687767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121122471563770408628458511 181683707345655612942687767)
        ·
          refine ⟨272525561018483419414031651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181683707345655612942687767 272525561018483419414031651)
          ·
            refine ⟨408788341527725129121047477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272525561018483419414031651 408788341527725129121047477)
            ·
              refine ⟨38323907018224230855098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408788341527725129121047477 38323907018224230855098201)
              ·
                refine ⟨28742930263668173141323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38323907018224230855098201 28742930263668173141323651)
                ·
                  refine ⟨43114395395502259711985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28742930263668173141323651 43114395395502259711985477)
                  ·
                    refine ⟨8083949136656673695997277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43114395395502259711985477 8083949136656673695997277)
                    ·
                      refine ⟨3031480926246252635998979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083949136656673695997277 3031480926246252635998979)
                      ·
                        rfl

theorem cell23_5903788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_5903788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903788 prefixEnd_5903788 := by exact prefixLift 5903788
  have htrace : WordTrace (prefixWord ++ tailWord_5903788) baseStart_5903788 baseEnd_5903788 := by
    simpa [prefixWord, tailWord_5903788, baseEnd_5903788] using wordTrace_append hprefix tailTrace_5903788
  have hstable : (prefixWord ++ tailWord_5903788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903788).length < 2 ^ (prefixWord ++ tailWord_5903788).sum := by decide
  have hdescent : baseEnd_5903788 < baseStart_5903788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903805 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5903805 : Nat := 118140960795 + 5903805 * 2 ^ 59
def prefixEnd_5903805 : Nat := 4983230072969 + 3 ^ 40 * 5903805 * 2
def baseEnd_5903805 : Nat := 3031489655417379069486401

theorem tailTrace_5903805 : CollatzResearch.WordTrace tailWord_5903805 prefixEnd_5903805 3031489655417379069486401 := by
  unfold tailWord_5903805
  simp only [CollatzResearch.WordTrace]
  refine ⟨215329458376530249465072869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143552972251020166310048579 215329458376530249465072869)
  ·
    refine ⟨40374273445599421774701163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215329458376530249465072869 40374273445599421774701163)
    ·
      refine ⟨60561410168399132662051745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40374273445599421774701163 60561410168399132662051745)
      ·
        refine ⟨45421057626299349496538809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60561410168399132662051745 45421057626299349496538809)
        ·
          refine ⟨34065793219724512122404107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45421057626299349496538809 34065793219724512122404107)
          ·
            refine ⟨51098689829586768183606161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34065793219724512122404107 51098689829586768183606161)
            ·
              refine ⟨38324017372190076137704621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51098689829586768183606161 38324017372190076137704621)
              ·
                refine ⟨14371506514571278551639233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38324017372190076137704621 14371506514571278551639233)
                ·
                  refine ⟨10778629885928458913729425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14371506514571278551639233 10778629885928458913729425)
                  ·
                    refine ⟨8083972414446344185297069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10778629885928458913729425 8083972414446344185297069)
                    ·
                      refine ⟨3031489655417379069486401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8083972414446344185297069 3031489655417379069486401)
                      ·
                        rfl

theorem cell23_5903805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5903805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903805 prefixEnd_5903805 := by exact prefixLift 5903805
  have htrace : WordTrace (prefixWord ++ tailWord_5903805) baseStart_5903805 baseEnd_5903805 := by
    simpa [prefixWord, tailWord_5903805, baseEnd_5903805] using wordTrace_append hprefix tailTrace_5903805
  have hstable : (prefixWord ++ tailWord_5903805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903805).length < 2 ^ (prefixWord ++ tailWord_5903805).sum := by decide
  have hdescent : baseEnd_5903805 < baseStart_5903805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903829 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_5903829 : Nat := 118140960795 + 5903829 * 2 ^ 59
def prefixEnd_5903829 : Nat := 4983230072969 + 3 ^ 40 * 5903829 * 2
def baseEnd_5903829 : Nat := 1010500659651028991862097

theorem tailTrace_5903829 : CollatzResearch.WordTrace tailWord_5903829 prefixEnd_5903829 1010500659651028991862097 := by
  unfold tailWord_5903829
  simp only [CollatzResearch.WordTrace]
  refine ⟨215330333728443301563946541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143553555818962201042631027 215330333728443301563946541)
  ·
    refine ⟨80748875148166238086479953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215330333728443301563946541 80748875148166238086479953)
    ·
      refine ⟨60561656361124678564859965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80748875148166238086479953 60561656361124678564859965)
      ·
        refine ⟨22710621135421754461822487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60561656361124678564859965 22710621135421754461822487)
        ·
          refine ⟨34065931703132631692733731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22710621135421754461822487 34065931703132631692733731)
          ·
            refine ⟨51098897554698947539100597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34065931703132631692733731 51098897554698947539100597)
            ·
              refine ⟨4790521645753026331790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51098897554698947539100597 4790521645753026331790681)
              ·
                refine ⟨3592891234314769748843011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4790521645753026331790681 3592891234314769748843011)
                ·
                  refine ⟨5389336851472154623264517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592891234314769748843011 5389336851472154623264517)
                  ·
                    refine ⟨1010500659651028991862097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389336851472154623264517 1010500659651028991862097)
                    ·
                      rfl

theorem cell23_5903829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_5903829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903829 prefixEnd_5903829 := by exact prefixLift 5903829
  have htrace : WordTrace (prefixWord ++ tailWord_5903829) baseStart_5903829 baseEnd_5903829 := by
    simpa [prefixWord, tailWord_5903829, baseEnd_5903829] using wordTrace_append hprefix tailTrace_5903829
  have hstable : (prefixWord ++ tailWord_5903829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903829).length < 2 ^ (prefixWord ++ tailWord_5903829).sum := by decide
  have hdescent : baseEnd_5903829 < baseStart_5903829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903855 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 1, 5]
def baseStart_5903855 : Nat := 118140960795 + 5903855 * 2 ^ 59
def prefixEnd_5903855 : Nat := 4983230072969 + 3 ^ 40 * 5903855 * 2
def baseEnd_5903855 : Nat := 1010505109816701291287057

theorem tailTrace_5903855 : CollatzResearch.WordTrace tailWord_5903855 prefixEnd_5903855 1010505109816701291287057 := by
  unfold tailWord_5903855
  simp only [CollatzResearch.WordTrace]
  refine ⟨215331282026349108004393019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143554188017566072002928679 215331282026349108004393019)
  ·
    refine ⟨322996923039523662006589529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215331282026349108004393019 322996923039523662006589529)
    ·
      refine ⟨242247692279642746504942147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322996923039523662006589529 242247692279642746504942147)
      ·
        refine ⟨363371538419464119757413221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242247692279642746504942147 363371538419464119757413221)
        ·
          refine ⟨68132163453649522454514979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363371538419464119757413221 68132163453649522454514979)
          ·
            refine ⟨102198245180474283681772469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68132163453649522454514979 102198245180474283681772469)
            ·
              refine ⟨9581085485669464095166169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102198245180474283681772469 9581085485669464095166169)
              ·
                refine ⟨7185814114252098071374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9581085485669464095166169 7185814114252098071374627)
                ·
                  refine ⟨10778721171378147107061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185814114252098071374627 10778721171378147107061941)
                  ·
                    refine ⟨1010505109816701291287057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10778721171378147107061941 1010505109816701291287057)
                    ·
                      rfl

theorem cell23_5903855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_5903855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903855 prefixEnd_5903855 := by exact prefixLift 5903855
  have htrace : WordTrace (prefixWord ++ tailWord_5903855) baseStart_5903855 baseEnd_5903855 := by
    simpa [prefixWord, tailWord_5903855, baseEnd_5903855] using wordTrace_append hprefix tailTrace_5903855
  have hstable : (prefixWord ++ tailWord_5903855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903855).length < 2 ^ (prefixWord ++ tailWord_5903855).sum := by decide
  have hdescent : baseEnd_5903855 < baseStart_5903855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903868 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_5903868 : Nat := 118140960795 + 5903868 * 2 ^ 59
def prefixEnd_5903868 : Nat := 4983230072969 + 3 ^ 40 * 5903868 * 2
def baseEnd_5903868 : Nat := 1010507334899537440999537

theorem tailTrace_5903868 : CollatzResearch.WordTrace tailWord_5903868 prefixEnd_5903868 1010507334899537440999537 := by
  unfold tailWord_5903868
  simp only [CollatzResearch.WordTrace]
  refine ⟨107665878087651005612308129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143554504116868007483077505 107665878087651005612308129)
  ·
    refine ⟨80749408565738254209231097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107665878087651005612308129 80749408565738254209231097)
    ·
      refine ⟨60562056424303690656923323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80749408565738254209231097 60562056424303690656923323)
      ·
        refine ⟨90843084636455535985384985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60562056424303690656923323 90843084636455535985384985)
        ·
          refine ⟨68132313477341651989038739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90843084636455535985384985 68132313477341651989038739)
          ·
            refine ⟨102198470216012477983558109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68132313477341651989038739 102198470216012477983558109)
            ·
              refine ⟨38324426331004679243834291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102198470216012477983558109 38324426331004679243834291)
              ·
                refine ⟨57486639496507018865751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38324426331004679243834291 57486639496507018865751437)
                ·
                  refine ⟨21557489811190132074656789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57486639496507018865751437 21557489811190132074656789)
                  ·
                    refine ⟨1010507334899537440999537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21557489811190132074656789 1010507334899537440999537)
                    ·
                      rfl

theorem cell23_5903868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_5903868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903868 prefixEnd_5903868 := by exact prefixLift 5903868
  have htrace : WordTrace (prefixWord ++ tailWord_5903868) baseStart_5903868 baseEnd_5903868 := by
    simpa [prefixWord, tailWord_5903868, baseEnd_5903868] using wordTrace_append hprefix tailTrace_5903868
  have hstable : (prefixWord ++ tailWord_5903868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903868).length < 2 ^ (prefixWord ++ tailWord_5903868).sum := by decide
  have hdescent : baseEnd_5903868 < baseStart_5903868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903886 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5903886 : Nat := 118140960795 + 5903886 * 2 ^ 59
def prefixEnd_5903886 : Nat := 4983230072969 + 3 ^ 40 * 5903886 * 2
def baseEnd_5903886 : Nat := 3031531247350393252573529

theorem tailTrace_5903886 : CollatzResearch.WordTrace tailWord_5903886 prefixEnd_5903886 3031531247350393252573529 := by
  unfold tailWord_5903886
  simp only [CollatzResearch.WordTrace]
  refine ⟨26916551586154600037346439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143554941792824533532514341 26916551586154600037346439)
  ·
    refine ⟨40374827379231900056019659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26916551586154600037346439 40374827379231900056019659)
    ·
      refine ⟨60562241068847850084029489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40374827379231900056019659 60562241068847850084029489)
      ·
        refine ⟨45421680801635887563022117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60562241068847850084029489 45421680801635887563022117)
        ·
          refine ⟨8516565150306728918066647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45421680801635887563022117 8516565150306728918066647)
          ·
            refine ⟨12774847725460093377099971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8516565150306728918066647 12774847725460093377099971)
            ·
              refine ⟨19162271588190140065649957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12774847725460093377099971 19162271588190140065649957)
              ·
                refine ⟨3592925922785651262309367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19162271588190140065649957 3592925922785651262309367)
                ·
                  refine ⟨5389388884178476893464051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592925922785651262309367 5389388884178476893464051)
                  ·
                    refine ⟨8084083326267715340196077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5389388884178476893464051 8084083326267715340196077)
                    ·
                      refine ⟨3031531247350393252573529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084083326267715340196077 3031531247350393252573529)
                      ·
                        rfl

theorem cell23_5903886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5903886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903886 prefixEnd_5903886 := by exact prefixLift 5903886
  have htrace : WordTrace (prefixWord ++ tailWord_5903886) baseStart_5903886 baseEnd_5903886 := by
    simpa [prefixWord, tailWord_5903886, baseEnd_5903886] using wordTrace_append hprefix tailTrace_5903886
  have hstable : (prefixWord ++ tailWord_5903886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903886).length < 2 ^ (prefixWord ++ tailWord_5903886).sum := by decide
  have hdescent : baseEnd_5903886 < baseStart_5903886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903905 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5903905 : Nat := 118140960795 + 5903905 * 2 ^ 59
def prefixEnd_5903905 : Nat := 4983230072969 + 3 ^ 40 * 5903905 * 2
def baseEnd_5903905 : Nat := 3031541003482828678235941

theorem tailTrace_5903905 : CollatzResearch.WordTrace tailWord_5903905 prefixEnd_5903905 3031541003482828678235941 := by
  unfold tailWord_5903905
  simp only [CollatzResearch.WordTrace]
  refine ⟨215333105676167966543713169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143555403784111977695808779 215333105676167966543713169)
  ·
    refine ⟨161499829257125974907784877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215333105676167966543713169 161499829257125974907784877)
    ·
      refine ⟨60562435971422240590419329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161499829257125974907784877 60562435971422240590419329)
      ·
        refine ⟨45421826978566680442814497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60562435971422240590419329 45421826978566680442814497)
        ·
          refine ⟨34066370233925010332110873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45421826978566680442814497 34066370233925010332110873)
          ·
            refine ⟨25549777675443757749083155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34066370233925010332110873 25549777675443757749083155)
            ·
              refine ⟨38324666513165636623624733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25549777675443757749083155 38324666513165636623624733)
              ·
                refine ⟨14371749942437113733859275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38324666513165636623624733 14371749942437113733859275)
                ·
                  refine ⟨21557624913655670600788913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14371749942437113733859275 21557624913655670600788913)
                  ·
                    refine ⟨16168218685241752950591685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21557624913655670600788913 16168218685241752950591685)
                    ·
                      refine ⟨3031541003482828678235941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16168218685241752950591685 3031541003482828678235941)
                      ·
                        rfl

theorem cell23_5903905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5903905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903905 prefixEnd_5903905 := by exact prefixLift 5903905
  have htrace : WordTrace (prefixWord ++ tailWord_5903905) baseStart_5903905 baseEnd_5903905 := by
    simpa [prefixWord, tailWord_5903905, baseEnd_5903905] using wordTrace_append hprefix tailTrace_5903905
  have hstable : (prefixWord ++ tailWord_5903905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903905).length < 2 ^ (prefixWord ++ tailWord_5903905).sum := by decide
  have hdescent : baseEnd_5903905 < baseStart_5903905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903929 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5903929 : Nat := 118140960795 + 5903929 * 2 ^ 59
def prefixEnd_5903929 : Nat := 4983230072969 + 3 ^ 40 * 5903929 * 2
def baseEnd_5903929 : Nat := 3031553327018536584335831

theorem tailTrace_5903929 : CollatzResearch.WordTrace tailWord_5903929 prefixEnd_5903929 3031553327018536584335831 := by
  unfold tailWord_5903929
  simp only [CollatzResearch.WordTrace]
  refine ⟨215333981028081018642586841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143555987352054012428391227 215333981028081018642586841)
  ·
    refine ⟨161500485771060763981940131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215333981028081018642586841 161500485771060763981940131)
    ·
      refine ⟨242250728656591145972910197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161500485771060763981940131 242250728656591145972910197)
      ·
        refine ⟨22711005811555419934960331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242250728656591145972910197 22711005811555419934960331)
        ·
          refine ⟨34066508717333129902440497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22711005811555419934960331 34066508717333129902440497)
          ·
            refine ⟨25549881537999847426830373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34066508717333129902440497 25549881537999847426830373)
            ·
              refine ⟨4790602788374971392530695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25549881537999847426830373 4790602788374971392530695)
              ·
                refine ⟨7185904182562457088796043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790602788374971392530695 7185904182562457088796043)
                ·
                  refine ⟨10778856273843685633194065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185904182562457088796043 10778856273843685633194065)
                  ·
                    refine ⟨8084142205382764224895549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10778856273843685633194065 8084142205382764224895549)
                    ·
                      refine ⟨3031553327018536584335831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084142205382764224895549 3031553327018536584335831)
                      ·
                        rfl

theorem cell23_5903929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5903929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903929 prefixEnd_5903929 := by exact prefixLift 5903929
  have htrace : WordTrace (prefixWord ++ tailWord_5903929) baseStart_5903929 baseEnd_5903929 := by
    simpa [prefixWord, tailWord_5903929, baseEnd_5903929] using wordTrace_append hprefix tailTrace_5903929
  have hstable : (prefixWord ++ tailWord_5903929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903929).length < 2 ^ (prefixWord ++ tailWord_5903929).sum := by decide
  have hdescent : baseEnd_5903929 < baseStart_5903929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5903969 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_5903969 : Nat := 118140960795 + 5903969 * 2 ^ 59
def prefixEnd_5903969 : Nat := 4983230072969 + 3 ^ 40 * 5903969 * 2
def baseEnd_5903969 : Nat := 3031573866244716427835647

theorem tailTrace_5903969 : CollatzResearch.WordTrace tailWord_5903969 prefixEnd_5903969 3031573866244716427835647 := by
  unfold tailWord_5903969
  simp only [CollatzResearch.WordTrace]
  refine ⟨215335439947936105474042961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143556959965290736982695307 215335439947936105474042961)
  ·
    refine ⟨161501579960952079105532221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215335439947936105474042961 161501579960952079105532221)
    ·
      refine ⟨60563092485357029664574583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161501579960952079105532221 60563092485357029664574583)
      ·
        refine ⟨90844638728035544496861875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60563092485357029664574583 90844638728035544496861875)
        ·
          refine ⟨136266958092053316745292813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90844638728035544496861875 136266958092053316745292813)
          ·
            refine ⟨51100109284519993779484805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136266958092053316745292813 51100109284519993779484805)
            ·
              refine ⟨9581270490847498833653401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51100109284519993779484805 9581270490847498833653401)
              ·
                refine ⟨7185952868135624125240051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9581270490847498833653401 7185952868135624125240051)
                ·
                  refine ⟨10778929302203436187860077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7185952868135624125240051 10778929302203436187860077)
                  ·
                    refine ⟨4042098488326288570447529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10778929302203436187860077 4042098488326288570447529)
                    ·
                      refine ⟨3031573866244716427835647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042098488326288570447529 3031573866244716427835647)
                      ·
                        rfl

theorem cell23_5903969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_5903969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5903969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5903969 prefixEnd_5903969 := by exact prefixLift 5903969
  have htrace : WordTrace (prefixWord ++ tailWord_5903969) baseStart_5903969 baseEnd_5903969 := by
    simpa [prefixWord, tailWord_5903969, baseEnd_5903969] using wordTrace_append hprefix tailTrace_5903969
  have hstable : (prefixWord ++ tailWord_5903969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5903969).length < 2 ^ (prefixWord ++ tailWord_5903969).sum := by decide
  have hdescent : baseEnd_5903969 < baseStart_5903969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5903969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904020 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5904020 : Nat := 118140960795 + 5904020 * 2 ^ 59
def prefixEnd_5904020 : Nat := 4983230072969 + 3 ^ 40 * 5904020 * 2
def baseEnd_5904020 : Nat := 3031600053758095728297913

theorem tailTrace_5904020 : CollatzResearch.WordTrace tailWord_5904020 prefixEnd_5904020 3031600053758095728297913 := by
  unfold tailWord_5904020
  simp only [CollatzResearch.WordTrace]
  refine ⟨107668650035375670592074757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143558200047167560789433009 107668650035375670592074757)
  ·
    refine ⟨20187871881632938236014017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107668650035375670592074757 20187871881632938236014017)
    ·
      refine ⟨15140903911224703677010513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20187871881632938236014017 15140903911224703677010513)
      ·
        refine ⟨11355677933418527757757885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15140903911224703677010513 11355677933418527757757885)
        ·
          refine ⟨4258379225031947909159207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11355677933418527757757885 4258379225031947909159207)
          ·
            refine ⟨6387568837547921863738811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258379225031947909159207 6387568837547921863738811)
            ·
              refine ⟨9581353256321882795608217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387568837547921863738811 9581353256321882795608217)
              ·
                refine ⟨7186014942241412096706163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9581353256321882795608217 7186014942241412096706163)
                ·
                  refine ⟨10779022413362118145059245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186014942241412096706163 10779022413362118145059245)
                  ·
                    refine ⟨4042133405010794304397217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10779022413362118145059245 4042133405010794304397217)
                    ·
                      refine ⟨3031600053758095728297913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042133405010794304397217 3031600053758095728297913)
                      ·
                        rfl

theorem cell23_5904020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5904020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904020 prefixEnd_5904020 := by exact prefixLift 5904020
  have htrace : WordTrace (prefixWord ++ tailWord_5904020) baseStart_5904020 baseEnd_5904020 := by
    simpa [prefixWord, tailWord_5904020, baseEnd_5904020] using wordTrace_append hprefix tailTrace_5904020
  have hstable : (prefixWord ++ tailWord_5904020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904020).length < 2 ^ (prefixWord ++ tailWord_5904020).sum := by decide
  have hdescent : baseEnd_5904020 < baseStart_5904020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904062 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5904062 : Nat := 118140960795 + 5904062 * 2 ^ 59
def prefixEnd_5904062 : Nat := 4983230072969 + 3 ^ 40 * 5904062 * 2
def baseEnd_5904062 : Nat := 3031621619945584563972719

theorem tailTrace_5904062 : CollatzResearch.WordTrace tailWord_5904062 prefixEnd_5904062 3031621619945584563972719 := by
  unfold tailWord_5904062
  simp only [CollatzResearch.WordTrace]
  refine ⟨26917353992074897794647305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143559221291066121571452293 26917353992074897794647305)
  ·
    refine ⟨20188015494056173345985479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26917353992074897794647305 20188015494056173345985479)
    ·
      refine ⟨30282023241084260018978219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188015494056173345985479 30282023241084260018978219)
      ·
        refine ⟨45423034861626390028467329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30282023241084260018978219 45423034861626390028467329)
        ·
          refine ⟨34067276146219792521350497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45423034861626390028467329 34067276146219792521350497)
          ·
            refine ⟨25550457109664844391012873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34067276146219792521350497 25550457109664844391012873)
            ·
              refine ⟨19162842832248633293259655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25550457109664844391012873 19162842832248633293259655)
              ·
                refine ⟨28744264248372949939889483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19162842832248633293259655 28744264248372949939889483)
                ·
                  refine ⟨43116396372559424909834225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28744264248372949939889483 43116396372559424909834225)
                  ·
                    refine ⟨32337297279419568682375669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43116396372559424909834225 32337297279419568682375669)
                    ·
                      refine ⟨3031621619945584563972719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32337297279419568682375669 3031621619945584563972719)
                      ·
                        rfl

theorem cell23_5904062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5904062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904062 prefixEnd_5904062 := by exact prefixLift 5904062
  have htrace : WordTrace (prefixWord ++ tailWord_5904062) baseStart_5904062 baseEnd_5904062 := by
    simpa [prefixWord, tailWord_5904062, baseEnd_5904062] using wordTrace_append hprefix tailTrace_5904062
  have hstable : (prefixWord ++ tailWord_5904062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904062).length < 2 ^ (prefixWord ++ tailWord_5904062).sum := by decide
  have hdescent : baseEnd_5904062 < baseStart_5904062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904086 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5904086 : Nat := 118140960795 + 5904086 * 2 ^ 59
def prefixEnd_5904086 : Nat := 4983230072969 + 3 ^ 40 * 5904086 * 2
def baseEnd_5904086 : Nat := 1010544647827097490024203

theorem tailTrace_5904086 : CollatzResearch.WordTrace tailWord_5904086 prefixEnd_5904086 1010544647827097490024203 := by
  unfold tailWord_5904086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458731705532014653503257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143559804859008156304034741 13458731705532014653503257)
  ·
    refine ⟨10094048779149010990127443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13458731705532014653503257 10094048779149010990127443)
    ·
      refine ⟨15141073168723516485191165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10094048779149010990127443 15141073168723516485191165)
      ·
        refine ⟨5677902438271318681946687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15141073168723516485191165 5677902438271318681946687)
        ·
          refine ⟨8516853657406978022920031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677902438271318681946687 8516853657406978022920031)
          ·
            refine ⟨12775280486110467034380047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8516853657406978022920031 12775280486110467034380047)
            ·
              refine ⟨19162920729165700551570071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12775280486110467034380047 19162920729165700551570071)
              ·
                refine ⟨28744381093748550827355107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19162920729165700551570071 28744381093748550827355107)
                ·
                  refine ⟨43116571640622826241032661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28744381093748550827355107 43116571640622826241032661)
                  ·
                    refine ⟨1010544647827097490024203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43116571640622826241032661 1010544647827097490024203)
                    ·
                      rfl

theorem cell23_5904086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5904086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904086 prefixEnd_5904086 := by exact prefixLift 5904086
  have htrace : WordTrace (prefixWord ++ tailWord_5904086) baseStart_5904086 baseEnd_5904086 := by
    simpa [prefixWord, tailWord_5904086, baseEnd_5904086] using wordTrace_append hprefix tailTrace_5904086
  have hstable : (prefixWord ++ tailWord_5904086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904086).length < 2 ^ (prefixWord ++ tailWord_5904086).sum := by decide
  have hdescent : baseEnd_5904086 < baseStart_5904086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904089 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_5904089 : Nat := 118140960795 + 5904089 * 2 ^ 59
def prefixEnd_5904089 : Nat := 4983230072969 + 3 ^ 40 * 5904089 * 2
def baseEnd_5904089 : Nat := 3031635483923255958335095

theorem tailTrace_5904089 : CollatzResearch.WordTrace tailWord_5904089 prefixEnd_5904089 3031635483923255958335095 := by
  unfold tailWord_5904089
  simp only [CollatzResearch.WordTrace]
  refine ⟨215339816707501365968411321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143559877805000910645607547 215339816707501365968411321)
  ·
    refine ⟨161504862530626024476308491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215339816707501365968411321 161504862530626024476308491)
    ·
      refine ⟨242257293795939036714462737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161504862530626024476308491 242257293795939036714462737)
      ·
        refine ⟨181692970346954277535847053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242257293795939036714462737 181692970346954277535847053)
        ·
          refine ⟨68134863880107854075942645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181692970346954277535847053 68134863880107854075942645)
          ·
            refine ⟨6387643488760111319619623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68134863880107854075942645 6387643488760111319619623)
            ·
              refine ⟨9581465233140166979429435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6387643488760111319619623 9581465233140166979429435)
              ·
                refine ⟨14372197849710250469144153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581465233140166979429435 14372197849710250469144153)
                ·
                  refine ⟨10779148387282687851858115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14372197849710250469144153 10779148387282687851858115)
                  ·
                    refine ⟨16168722580924031777787173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10779148387282687851858115 16168722580924031777787173)
                    ·
                      refine ⟨3031635483923255958335095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16168722580924031777787173 3031635483923255958335095)
                      ·
                        rfl

theorem cell23_5904089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_5904089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904089 prefixEnd_5904089 := by exact prefixLift 5904089
  have htrace : WordTrace (prefixWord ++ tailWord_5904089) baseStart_5904089 baseEnd_5904089 := by
    simpa [prefixWord, tailWord_5904089, baseEnd_5904089] using wordTrace_append hprefix tailTrace_5904089
  have hstable : (prefixWord ++ tailWord_5904089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904089).length < 2 ^ (prefixWord ++ tailWord_5904089).sum := by decide
  have hdescent : baseEnd_5904089 < baseStart_5904089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904095 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 8]
def baseStart_5904095 : Nat := 118140960795 + 5904095 * 2 ^ 59
def prefixEnd_5904095 : Nat := 4983230072969 + 3 ^ 40 * 5904095 * 2
def baseEnd_5904095 : Nat := 336848729423020326095563

theorem tailTrace_5904095 : CollatzResearch.WordTrace tailWord_5904095 prefixEnd_5904095 336848729423020326095563 := by
  unfold tailWord_5904095
  simp only [CollatzResearch.WordTrace]
  refine ⟨215340035545479628993129739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143560023696986419328753159 215340035545479628993129739)
  ·
    refine ⟨323010053318219443489694609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215340035545479628993129739 323010053318219443489694609)
    ·
      refine ⟨242257539988664582617270957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323010053318219443489694609 242257539988664582617270957)
      ·
        refine ⟨90846577495749218481476609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242257539988664582617270957 90846577495749218481476609)
        ·
          refine ⟨68134933121811913861107457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90846577495749218481476609 68134933121811913861107457)
          ·
            refine ⟨51101199841358935395830593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68134933121811913861107457 51101199841358935395830593)
            ·
              refine ⟨38325899881019201546872945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51101199841358935395830593 38325899881019201546872945)
              ·
                refine ⟨28744424910764401160154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38325899881019201546872945 28744424910764401160154709)
                ·
                  refine ⟨336848729423020326095563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28744424910764401160154709 336848729423020326095563)
                  ·
                    rfl

theorem cell23_5904095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 8].length) (baseStart_5904095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904095 prefixEnd_5904095 := by exact prefixLift 5904095
  have htrace : WordTrace (prefixWord ++ tailWord_5904095) baseStart_5904095 baseEnd_5904095 := by
    simpa [prefixWord, tailWord_5904095, baseEnd_5904095] using wordTrace_append hprefix tailTrace_5904095
  have hstable : (prefixWord ++ tailWord_5904095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904095).length < 2 ^ (prefixWord ++ tailWord_5904095).sum := by decide
  have hdescent : baseEnd_5904095 < baseStart_5904095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904115 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_5904115 : Nat := 118140960795 + 5904115 * 2 ^ 59
def prefixEnd_5904115 : Nat := 4983230072969 + 3 ^ 40 * 5904115 * 2
def baseEnd_5904115 : Nat := 3031648834420272856609975

theorem tailTrace_5904115 : CollatzResearch.WordTrace tailWord_5904115 prefixEnd_5904115 3031648834420272856609975 := by
  unfold tailWord_5904115
  simp only [CollatzResearch.WordTrace]
  refine ⟨215340765005407172408857799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143560510003604781605905199 215340765005407172408857799)
  ·
    refine ⟨323011147508110758613286699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215340765005407172408857799 323011147508110758613286699)
    ·
      refine ⟨484516721262166137919930049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323011147508110758613286699 484516721262166137919930049)
      ·
        refine ⟨363387540946624603439947537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484516721262166137919930049 363387540946624603439947537)
        ·
          refine ⟨272540655709968452579960653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363387540946624603439947537 272540655709968452579960653)
          ·
            refine ⟨102202745891238169717485245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272540655709968452579960653 102202745891238169717485245)
            ·
              refine ⟨38326029709214313644056967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102202745891238169717485245 38326029709214313644056967)
              ·
                refine ⟨57489044563821470466085451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38326029709214313644056967 57489044563821470466085451)
                ·
                  refine ⟨86233566845732205699128177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57489044563821470466085451 86233566845732205699128177)
                  ·
                    refine ⟨64675175134299154274346133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86233566845732205699128177 64675175134299154274346133)
                    ·
                      refine ⟨3031648834420272856609975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64675175134299154274346133 3031648834420272856609975)
                      ·
                        rfl

theorem cell23_5904115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_5904115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904115 prefixEnd_5904115 := by exact prefixLift 5904115
  have htrace : WordTrace (prefixWord ++ tailWord_5904115) baseStart_5904115 baseEnd_5904115 := by
    simpa [prefixWord, tailWord_5904115, baseEnd_5904115] using wordTrace_append hprefix tailTrace_5904115
  have hstable : (prefixWord ++ tailWord_5904115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904115).length < 2 ^ (prefixWord ++ tailWord_5904115).sum := by decide
  have hdescent : baseEnd_5904115 < baseStart_5904115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904125 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5904125 : Nat := 118140960795 + 5904125 * 2 ^ 59
def prefixEnd_5904125 : Nat := 4983230072969 + 3 ^ 40 * 5904125 * 2
def baseEnd_5904125 : Nat := 1010551323075605939161643

theorem tailTrace_5904125 : CollatzResearch.WordTrace tailWord_5904125 prefixEnd_5904125 1010551323075605939161643 := by
  unfold tailWord_5904125
  simp only [CollatzResearch.WordTrace]
  refine ⟨215341129735370944116721829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143560753156913962744481219 215341129735370944116721829)
  ·
    refine ⟨40376461825382052021885343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215341129735370944116721829 40376461825382052021885343)
    ·
      refine ⟨60564692738073078032828015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40376461825382052021885343 60564692738073078032828015)
      ·
        refine ⟨90847039107109617049242023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60564692738073078032828015 90847039107109617049242023)
        ·
          refine ⟨136270558660664425573863035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90847039107109617049242023 136270558660664425573863035)
          ·
            refine ⟨204405837990996638360794553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136270558660664425573863035 204405837990996638360794553)
            ·
              refine ⟨153304378493247478770595915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204405837990996638360794553 153304378493247478770595915)
              ·
                refine ⟨229956567739871218155893873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153304378493247478770595915 229956567739871218155893873)
                ·
                  refine ⟨172467425804903413616920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229956567739871218155893873 172467425804903413616920405)
                  ·
                    refine ⟨1010551323075605939161643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172467425804903413616920405 1010551323075605939161643)
                    ·
                      rfl

theorem cell23_5904125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5904125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904125 prefixEnd_5904125 := by exact prefixLift 5904125
  have htrace : WordTrace (prefixWord ++ tailWord_5904125) baseStart_5904125 baseEnd_5904125 := by
    simpa [prefixWord, tailWord_5904125, baseEnd_5904125] using wordTrace_append hprefix tailTrace_5904125
  have hstable : (prefixWord ++ tailWord_5904125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904125).length < 2 ^ (prefixWord ++ tailWord_5904125).sum := by decide
  have hdescent : baseEnd_5904125 < baseStart_5904125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904139 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 3]
def baseStart_5904139 : Nat := 118140960795 + 5904139 * 2 ^ 59
def prefixEnd_5904139 : Nat := 4983230072969 + 3 ^ 40 * 5904139 * 2
def baseEnd_5904139 : Nat := 3031661157955980762709865

theorem tailTrace_5904139 : CollatzResearch.WordTrace tailWord_5904139 prefixEnd_5904139 3031661157955980762709865 := by
  unfold tailWord_5904139
  simp only [CollatzResearch.WordTrace]
  refine ⟨215341640357320224507731471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143561093571546816338487647 215341640357320224507731471)
  ·
    refine ⟨323012460535980336761597207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215341640357320224507731471 323012460535980336761597207)
    ·
      refine ⟨484518690803970505142395811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323012460535980336761597207 484518690803970505142395811)
      ·
        refine ⟨726778036205955757713593717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484518690803970505142395811 726778036205955757713593717)
        ·
          refine ⟨68135440894308352285649411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 726778036205955757713593717 68135440894308352285649411)
          ·
            refine ⟨102203161341462528428474117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68135440894308352285649411 102203161341462528428474117)
            ·
              refine ⟨19163092751524224080338897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102203161341462528428474117 19163092751524224080338897)
              ·
                refine ⟨14372319563643168060254173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19163092751524224080338897 14372319563643168060254173)
                ·
                  refine ⟨5389619836366188022595315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14372319563643168060254173 5389619836366188022595315)
                  ·
                    refine ⟨8084429754549282033892973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5389619836366188022595315 8084429754549282033892973)
                    ·
                      refine ⟨3031661157955980762709865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8084429754549282033892973 3031661157955980762709865)
                      ·
                        rfl

theorem cell23_5904139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 3].length) (baseStart_5904139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904139 prefixEnd_5904139 := by exact prefixLift 5904139
  have htrace : WordTrace (prefixWord ++ tailWord_5904139) baseStart_5904139 baseEnd_5904139 := by
    simpa [prefixWord, tailWord_5904139, baseEnd_5904139] using wordTrace_append hprefix tailTrace_5904139
  have hstable : (prefixWord ++ tailWord_5904139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904139).length < 2 ^ (prefixWord ++ tailWord_5904139).sum := by decide
  have hdescent : baseEnd_5904139 < baseStart_5904139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904142 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_5904142 : Nat := 118140960795 + 5904142 * 2 ^ 59
def prefixEnd_5904142 : Nat := 4983230072969 + 3 ^ 40 * 5904142 * 2
def baseEnd_5904142 : Nat := 1010554232799314750324117

theorem tailTrace_5904142 : CollatzResearch.WordTrace tailWord_5904142 prefixEnd_5904142 1010554232799314750324117 := by
  unfold tailWord_5904142
  simp only [CollatzResearch.WordTrace]
  refine ⟨26917718722038669502511335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143561166517539570680060453 26917718722038669502511335)
  ·
    refine ⟨40376578083058004253767003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26917718722038669502511335 40376578083058004253767003)
    ·
      refine ⟨60564867124587006380650505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40376578083058004253767003 60564867124587006380650505)
      ·
        refine ⟨45423650343440254785487879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60564867124587006380650505 45423650343440254785487879)
        ·
          refine ⟨68135475515160382178231819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45423650343440254785487879 68135475515160382178231819)
          ·
            refine ⟨102203213272740573267347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68135475515160382178231819 102203213272740573267347729)
            ·
              refine ⟨76652409954555429950510797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102203213272740573267347729 76652409954555429950510797)
              ·
                refine ⟨28744653732958286231441549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76652409954555429950510797 28744653732958286231441549)
                ·
                  refine ⟨10779245149859357336790581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28744653732958286231441549 10779245149859357336790581)
                  ·
                    refine ⟨1010554232799314750324117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10779245149859357336790581 1010554232799314750324117)
                    ·
                      rfl

theorem cell23_5904142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_5904142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904142 prefixEnd_5904142 := by exact prefixLift 5904142
  have htrace : WordTrace (prefixWord ++ tailWord_5904142) baseStart_5904142 baseEnd_5904142 := by
    simpa [prefixWord, tailWord_5904142, baseEnd_5904142] using wordTrace_append hprefix tailTrace_5904142
  have hstable : (prefixWord ++ tailWord_5904142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904142).length < 2 ^ (prefixWord ++ tailWord_5904142).sum := by decide
  have hdescent : baseEnd_5904142 < baseStart_5904142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904149 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_5904149 : Nat := 118140960795 + 5904149 * 2 ^ 59
def prefixEnd_5904149 : Nat := 4983230072969 + 3 ^ 40 * 5904149 * 2
def baseEnd_5904149 : Nat := 3031666292762525723584819

theorem tailTrace_5904149 : CollatzResearch.WordTrace tailWord_5904149 prefixEnd_5904149 3031666292762525723584819 := by
  unfold tailWord_5904149
  simp only [CollatzResearch.WordTrace]
  refine ⟨215342005087283996215595501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143561336724855997477063667 215342005087283996215595501)
  ·
    refine ⟨80753251907731498580848313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215342005087283996215595501 80753251907731498580848313)
    ·
      refine ⟨60564938930798623935636235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80753251907731498580848313 60564938930798623935636235)
      ·
        refine ⟨90847408396197935903454353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60564938930798623935636235 90847408396197935903454353)
        ·
          refine ⟨68135556297148451927590765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90847408396197935903454353 68135556297148451927590765)
          ·
            refine ⟨25550833611430669472846537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68135556297148451927590765 25550833611430669472846537)
            ·
              refine ⟨19163125208573002104634903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25550833611430669472846537 19163125208573002104634903)
              ·
                refine ⟨28744687812859503156952355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19163125208573002104634903 28744687812859503156952355)
                ·
                  refine ⟨43117031719289254735428533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28744687812859503156952355 43117031719289254735428533)
                  ·
                    refine ⟨4042221723683367631446425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43117031719289254735428533 4042221723683367631446425)
                    ·
                      refine ⟨3031666292762525723584819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4042221723683367631446425 3031666292762525723584819)
                      ·
                        rfl

theorem cell23_5904149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_5904149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904149 prefixEnd_5904149 := by exact prefixLift 5904149
  have htrace : WordTrace (prefixWord ++ tailWord_5904149) baseStart_5904149 baseEnd_5904149 := by
    simpa [prefixWord, tailWord_5904149, baseEnd_5904149] using wordTrace_append hprefix tailTrace_5904149
  have hstable : (prefixWord ++ tailWord_5904149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904149).length < 2 ^ (prefixWord ++ tailWord_5904149).sum := by decide
  have hdescent : baseEnd_5904149 < baseStart_5904149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5904209 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_5904209 : Nat := 118140960795 + 5904209 * 2 ^ 59
def prefixEnd_5904209 : Nat := 4983230072969 + 3 ^ 40 * 5904209 * 2
def baseEnd_5904209 : Nat := 3031697101601795488834543

theorem tailTrace_5904209 : CollatzResearch.WordTrace tailWord_5904209 prefixEnd_5904209 3031697101601795488834543 := by
  unfold tailWord_5904209
  simp only [CollatzResearch.WordTrace]
  refine ⟨215344193467066626462779681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143562795644711084308519787 215344193467066626462779681)
  ·
    refine ⟨161508145100299969847084761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215344193467066626462779681 161508145100299969847084761)
    ·
      refine ⟨121131108825224977385313571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161508145100299969847084761 121131108825224977385313571)
      ·
        refine ⟨181696663237837466077970357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121131108825224977385313571 181696663237837466077970357)
        ·
          refine ⟨17034062178547262444809721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181696663237837466077970357 17034062178547262444809721)
          ·
            refine ⟨12775546633910446833607291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17034062178547262444809721 12775546633910446833607291)
            ·
              refine ⟨19163319950865670250410937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12775546633910446833607291 19163319950865670250410937)
              ·
                refine ⟨14372489963149252687808203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19163319950865670250410937 14372489963149252687808203)
                ·
                  refine ⟨21558734944723879031712305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14372489963149252687808203 21558734944723879031712305)
                  ·
                    refine ⟨16169051208542909273784229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21558734944723879031712305 16169051208542909273784229)
                    ·
                      refine ⟨3031697101601795488834543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16169051208542909273784229 3031697101601795488834543)
                      ·
                        rfl

theorem cell23_5904209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_5904209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5904209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5904209 prefixEnd_5904209 := by exact prefixLift 5904209
  have htrace : WordTrace (prefixWord ++ tailWord_5904209) baseStart_5904209 baseEnd_5904209 := by
    simpa [prefixWord, tailWord_5904209, baseEnd_5904209] using wordTrace_append hprefix tailTrace_5904209
  have hstable : (prefixWord ++ tailWord_5904209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5904209).length < 2 ^ (prefixWord ++ tailWord_5904209).sum := by decide
  have hdescent : baseEnd_5904209 < baseStart_5904209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5904209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
