import V185TrunkScan23Chunk0512

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3033671 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 6]
def baseStart_3033671 : Nat := 118140960795 + 3033671 * 2 ^ 59
def prefixEnd_3033671 : Nat := 4983230072969 + 3 ^ 40 * 3033671 * 2
def baseEnd_3033671 : Nat := 173081263400656164662323

theorem tailTrace_3033671 : CollatzResearch.WordTrace tailWord_3033671 prefixEnd_3033671 173081263400656164662323 := by
  unfold tailWord_3033671
  simp only [CollatzResearch.WordTrace]
  refine ⟨110647071392535551603084867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73764714261690367735389911 110647071392535551603084867)
  ·
    refine ⟨165970607088803327404627301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110647071392535551603084867 165970607088803327404627301)
    ·
      refine ⟨31119488829150623888367619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165970607088803327404627301 31119488829150623888367619)
      ·
        refine ⟨46679233243725935832551429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31119488829150623888367619 46679233243725935832551429)
        ·
          refine ⟨8752356233198612968603393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46679233243725935832551429 8752356233198612968603393)
          ·
            refine ⟨6564267174898959726452545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8752356233198612968603393 6564267174898959726452545)
            ·
              refine ⟨4923200381174219794839409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564267174898959726452545 4923200381174219794839409)
              ·
                refine ⟨3692400285880664846129557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923200381174219794839409 3692400285880664846129557)
                ·
                  refine ⟨173081263400656164662323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3692400285880664846129557 173081263400656164662323)
                  ·
                    rfl

theorem cell23_3033671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 6].length) (baseStart_3033671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033671 prefixEnd_3033671 := by exact prefixLift 3033671
  have htrace : WordTrace (prefixWord ++ tailWord_3033671) baseStart_3033671 baseEnd_3033671 := by
    simpa [prefixWord, tailWord_3033671, baseEnd_3033671] using wordTrace_append hprefix tailTrace_3033671
  have hstable : (prefixWord ++ tailWord_3033671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033671).length < 2 ^ (prefixWord ++ tailWord_3033671).sum := by decide
  have hdescent : baseEnd_3033671 < baseStart_3033671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033708 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_3033708 : Nat := 118140960795 + 3033708 * 2 ^ 59
def prefixEnd_3033708 : Nat := 4983230072969 + 3 ^ 40 * 3033708 * 2
def baseEnd_3033708 : Nat := 1557750369390121837198237

theorem tailTrace_3033708 : CollatzResearch.WordTrace tailWord_3033708 prefixEnd_3033708 1557750369390121837198237 := by
  unfold tailWord_3033708
  simp only [CollatzResearch.WordTrace]
  refine ⟨55324210446700753461090889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73765613928934337948121185 55324210446700753461090889)
  ·
    refine ⟨41493157835025565095818167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55324210446700753461090889 41493157835025565095818167)
    ·
      refine ⟨62239736752538347643727251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41493157835025565095818167 62239736752538347643727251)
      ·
        refine ⟨93359605128807521465590877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62239736752538347643727251 93359605128807521465590877)
        ·
          refine ⟨35009851923302820549596579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93359605128807521465590877 35009851923302820549596579)
          ·
            refine ⟨52514777884954230824394869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35009851923302820549596579 52514777884954230824394869)
            ·
              refine ⟨4923260426714459139787019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52514777884954230824394869 4923260426714459139787019)
              ·
                refine ⟨7384890640071688709680529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923260426714459139787019 7384890640071688709680529)
                ·
                  refine ⟨5538667980053766532260397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384890640071688709680529 5538667980053766532260397)
                  ·
                    refine ⟨2077000492520162449597649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5538667980053766532260397 2077000492520162449597649)
                    ·
                      refine ⟨1557750369390121837198237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077000492520162449597649 1557750369390121837198237)
                      ·
                        rfl

theorem cell23_3033708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_3033708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033708 prefixEnd_3033708 := by exact prefixLift 3033708
  have htrace : WordTrace (prefixWord ++ tailWord_3033708) baseStart_3033708 baseEnd_3033708 := by
    simpa [prefixWord, tailWord_3033708, baseEnd_3033708] using wordTrace_append hprefix tailTrace_3033708
  have hstable : (prefixWord ++ tailWord_3033708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033708).length < 2 ^ (prefixWord ++ tailWord_3033708).sum := by decide
  have hdescent : baseEnd_3033708 < baseStart_3033708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033748 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3033748 : Nat := 118140960795 + 3033748 * 2 ^ 59
def prefixEnd_3033748 : Nat := 4983230072969 + 3 ^ 40 * 3033748 * 2
def baseEnd_3033748 : Nat := 519256969538767226899351

theorem tailTrace_3033748 : CollatzResearch.WordTrace tailWord_3033748 prefixEnd_3033748 519256969538767226899351 := by
  unfold tailWord_3033748
  simp only [CollatzResearch.WordTrace]
  refine ⟨55324939906628296876818949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73766586542171062502425265 55324939906628296876818949)
  ·
    refine ⟨10373426232492805664403553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55324939906628296876818949 10373426232492805664403553)
    ·
      refine ⟨7780069674369604248302665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373426232492805664403553 7780069674369604248302665)
      ·
        refine ⟨5835052255777203186226999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7780069674369604248302665 5835052255777203186226999)
        ·
          refine ⟨8752578383665804779340499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835052255777203186226999 8752578383665804779340499)
          ·
            refine ⟨13128867575498707169010749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752578383665804779340499 13128867575498707169010749)
            ·
              refine ⟨4923325340812015188379031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13128867575498707169010749 4923325340812015188379031)
              ·
                refine ⟨7384988011218022782568547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923325340812015188379031 7384988011218022782568547)
                ·
                  refine ⟨11077482016827034173852821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384988011218022782568547 11077482016827034173852821)
                  ·
                    refine ⟨519256969538767226899351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11077482016827034173852821 519256969538767226899351)
                    ·
                      rfl

theorem cell23_3033748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3033748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033748 prefixEnd_3033748 := by exact prefixLift 3033748
  have htrace : WordTrace (prefixWord ++ tailWord_3033748) baseStart_3033748 baseEnd_3033748 := by
    simpa [prefixWord, tailWord_3033748, baseEnd_3033748] using wordTrace_append hprefix tailTrace_3033748
  have hstable : (prefixWord ++ tailWord_3033748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033748).length < 2 ^ (prefixWord ++ tailWord_3033748).sum := by decide
  have hdescent : baseEnd_3033748 < baseStart_3033748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033761 : List Nat := [1, 2, 3, 3, 3, 1, 1, 9]
def baseStart_3033761 : Nat := 118140960795 + 3033761 * 2 ^ 59
def prefixEnd_3033761 : Nat := 4983230072969 + 3 ^ 40 * 3033761 * 2
def baseEnd_3033761 : Nat := 57695466069067041845759

theorem tailTrace_3033761 : CollatzResearch.WordTrace tailWord_3033761 prefixEnd_3033761 57695466069067041845759 := by
  unfold tailWord_3033761
  simp only [CollatzResearch.WordTrace]
  refine ⟨110650353962209496973861137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73766902641472997982574091 110650353962209496973861137)
  ·
    refine ⟨82987765471657122730395853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110650353962209496973861137 82987765471657122730395853)
    ·
      refine ⟨31120412051871421023898445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82987765471657122730395853 31120412051871421023898445)
      ·
        refine ⟨11670154519451782883961917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31120412051871421023898445 11670154519451782883961917)
        ·
          refine ⟨4376307944794418581485719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11670154519451782883961917 4376307944794418581485719)
          ·
            refine ⟨6564461917191627872228579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376307944794418581485719 6564461917191627872228579)
            ·
              refine ⟨9846692875787441808342869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6564461917191627872228579 9846692875787441808342869)
              ·
                refine ⟨57695466069067041845759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9846692875787441808342869 57695466069067041845759)
                ·
                  rfl

theorem cell23_3033761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 9].length) (baseStart_3033761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033761 prefixEnd_3033761 := by exact prefixLift 3033761
  have htrace : WordTrace (prefixWord ++ tailWord_3033761) baseStart_3033761 baseEnd_3033761 := by
    simpa [prefixWord, tailWord_3033761, baseEnd_3033761] using wordTrace_append hprefix tailTrace_3033761
  have hstable : (prefixWord ++ tailWord_3033761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033761).length < 2 ^ (prefixWord ++ tailWord_3033761).sum := by decide
  have hdescent : baseEnd_3033761 < baseStart_3033761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033788 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3033788 : Nat := 118140960795 + 3033788 * 2 ^ 59
def prefixEnd_3033788 : Nat := 4983230072969 + 3 ^ 40 * 3033788 * 2
def baseEnd_3033788 : Nat := 1557791447842481524197869

theorem tailTrace_3033788 : CollatzResearch.WordTrace tailWord_3033788 prefixEnd_3033788 1557791447842481524197869 := by
  unfold tailWord_3033788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55325669366555840292547009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73767559155407787056729345 55325669366555840292547009)
  ·
    refine ⟨41494252024916880219410257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55325669366555840292547009 41494252024916880219410257)
    ·
      refine ⟨31120689018687660164557693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41494252024916880219410257 31120689018687660164557693)
      ·
        refine ⟨11670258382007872561709135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31120689018687660164557693 11670258382007872561709135)
        ·
          refine ⟨17505387573011808842563703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670258382007872561709135 17505387573011808842563703)
          ·
            refine ⟨26258081359517713263845555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17505387573011808842563703 26258081359517713263845555)
            ·
              refine ⟨39387122039276569895768333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26258081359517713263845555 39387122039276569895768333)
              ·
                refine ⟨14770170764728713710913125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39387122039276569895768333 14770170764728713710913125)
                ·
                  refine ⟨2769407018386633820796211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14770170764728713710913125 2769407018386633820796211)
                  ·
                    refine ⟨4154110527579950731194317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2769407018386633820796211 4154110527579950731194317)
                    ·
                      refine ⟨1557791447842481524197869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154110527579950731194317 1557791447842481524197869)
                      ·
                        rfl

theorem cell23_3033788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3033788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033788 prefixEnd_3033788 := by exact prefixLift 3033788
  have htrace : WordTrace (prefixWord ++ tailWord_3033788) baseStart_3033788 baseEnd_3033788 := by
    simpa [prefixWord, tailWord_3033788, baseEnd_3033788] using wordTrace_append hprefix tailTrace_3033788
  have hstable : (prefixWord ++ tailWord_3033788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033788).length < 2 ^ (prefixWord ++ tailWord_3033788).sum := by decide
  have hdescent : baseEnd_3033788 < baseStart_3033788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033789 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_3033789 : Nat := 118140960795 + 3033789 * 2 ^ 59
def prefixEnd_3033789 : Nat := 4983230072969 + 3 ^ 40 * 3033789 * 2
def baseEnd_3033789 : Nat := 1557791961323136020285365

theorem tailTrace_3033789 : CollatzResearch.WordTrace tailWord_3033789 prefixEnd_3033789 1557791961323136020285365 := by
  unfold tailWord_3033789
  simp only [CollatzResearch.WordTrace]
  refine ⟨110651375206108057755880421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73767583470738705170586947 110651375206108057755880421)
  ·
    refine ⟨20747132851145260829227579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110651375206108057755880421 20747132851145260829227579)
    ·
      refine ⟨31120699276717891243841369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20747132851145260829227579 31120699276717891243841369)
      ·
        refine ⟨23340524457538418432881027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31120699276717891243841369 23340524457538418432881027)
        ·
          refine ⟨35010786686307627649321541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23340524457538418432881027 35010786686307627649321541)
          ·
            refine ⟨6564522503682680184247789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35010786686307627649321541 6564522503682680184247789)
            ·
              refine ⟨2461695938881005069092921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6564522503682680184247789 2461695938881005069092921)
              ·
                refine ⟨1846271954160753801819691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461695938881005069092921 1846271954160753801819691)
                ·
                  refine ⟨2769407931241130702729537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846271954160753801819691 2769407931241130702729537)
                  ·
                    refine ⟨2077055948430848027047153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769407931241130702729537 2077055948430848027047153)
                    ·
                      refine ⟨1557791961323136020285365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077055948430848027047153 1557791961323136020285365)
                      ·
                        rfl

theorem cell23_3033789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_3033789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033789 prefixEnd_3033789 := by exact prefixLift 3033789
  have htrace : WordTrace (prefixWord ++ tailWord_3033789) baseStart_3033789 baseEnd_3033789 := by
    simpa [prefixWord, tailWord_3033789, baseEnd_3033789] using wordTrace_append hprefix tailTrace_3033789
  have hstable : (prefixWord ++ tailWord_3033789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033789).length < 2 ^ (prefixWord ++ tailWord_3033789).sum := by decide
  have hdescent : baseEnd_3033789 < baseStart_3033789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 10, 2]
def baseStart_3033811 : Nat := 118140960795 + 3033811 * 2 ^ 59
def prefixEnd_3033811 : Nat := 4983230072969 + 3 ^ 40 * 3033811 * 2
def baseEnd_3033811 : Nat := 1557803257897534934210263

theorem tailTrace_3033811 : CollatzResearch.WordTrace tailWord_3033811 prefixEnd_3033811 1557803257897534934210263 := by
  unfold tailWord_3033811
  simp only [CollatzResearch.WordTrace]
  refine ⟨110652177612028355513181287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73768118408018903675454191 110652177612028355513181287)
  ·
    refine ⟨165978266418042533269771931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110652177612028355513181287 165978266418042533269771931)
    ·
      refine ⟨248967399627063799904657897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165978266418042533269771931 248967399627063799904657897)
      ·
        refine ⟨186725549720297849928493423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248967399627063799904657897 186725549720297849928493423)
        ·
          refine ⟨280088324580446774892740135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186725549720297849928493423 280088324580446774892740135)
          ·
            refine ⟨420132486870670162339110203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280088324580446774892740135 420132486870670162339110203)
            ·
              refine ⟨630198730306005243508665305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420132486870670162339110203 630198730306005243508665305)
              ·
                refine ⟨472649047729503932631498979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630198730306005243508665305 472649047729503932631498979)
                ·
                  refine ⟨708973571594255898947248469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472649047729503932631498979 708973571594255898947248469)
                  ·
                    refine ⟨2077071010530046578947017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 708973571594255898947248469 2077071010530046578947017)
                    ·
                      refine ⟨1557803257897534934210263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077071010530046578947017 1557803257897534934210263)
                      ·
                        rfl

theorem cell23_3033811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10, 2].length) (baseStart_3033811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033811 prefixEnd_3033811 := by exact prefixLift 3033811
  have htrace : WordTrace (prefixWord ++ tailWord_3033811) baseStart_3033811 baseEnd_3033811 := by
    simpa [prefixWord, tailWord_3033811, baseEnd_3033811] using wordTrace_append hprefix tailTrace_3033811
  have hstable : (prefixWord ++ tailWord_3033811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033811).length < 2 ^ (prefixWord ++ tailWord_3033811).sum := by decide
  have hdescent : baseEnd_3033811 < baseStart_3033811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033815 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_3033815 : Nat := 118140960795 + 3033815 * 2 ^ 59
def prefixEnd_3033815 : Nat := 4983230072969 + 3 ^ 40 * 3033815 * 2
def baseEnd_3033815 : Nat := 1557805311820152918560245

theorem tailTrace_3033815 : CollatzResearch.WordTrace tailWord_3033815 prefixEnd_3033815 1557805311820152918560245 := by
  unfold tailWord_3033815
  simp only [CollatzResearch.WordTrace]
  refine ⟨110652323504013864196326899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73768215669342576130884599 110652323504013864196326899)
  ·
    refine ⟨165978485256020796294490349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110652323504013864196326899 165978485256020796294490349)
    ·
      refine ⟨62241931971007798610433881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165978485256020796294490349 62241931971007798610433881)
      ·
        refine ⟨46681448978255848957825411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62241931971007798610433881 46681448978255848957825411)
        ·
          refine ⟨70022173467383773436738117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46681448978255848957825411 70022173467383773436738117)
          ·
            refine ⟨13129157525134457519388397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70022173467383773436738117 13129157525134457519388397)
            ·
              refine ⟨4923434071925421569770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13129157525134457519388397 4923434071925421569770649)
              ·
                refine ⟨3692575553944066177327987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923434071925421569770649 3692575553944066177327987)
                ·
                  refine ⟨5538863330916099265991981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692575553944066177327987 5538863330916099265991981)
                  ·
                    refine ⟨2077073749093537224746993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5538863330916099265991981 2077073749093537224746993)
                    ·
                      refine ⟨1557805311820152918560245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077073749093537224746993 1557805311820152918560245)
                      ·
                        rfl

theorem cell23_3033815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_3033815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033815 prefixEnd_3033815 := by exact prefixLift 3033815
  have htrace : WordTrace (prefixWord ++ tailWord_3033815) baseStart_3033815 baseEnd_3033815 := by
    simpa [prefixWord, tailWord_3033815, baseEnd_3033815] using wordTrace_append hprefix tailTrace_3033815
  have hstable : (prefixWord ++ tailWord_3033815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033815).length < 2 ^ (prefixWord ++ tailWord_3033815).sum := by decide
  have hdescent : baseEnd_3033815 < baseStart_3033815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033828 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_3033828 : Nat := 118140960795 + 3033828 * 2 ^ 59
def prefixEnd_3033828 : Nat := 4983230072969 + 3 ^ 40 * 3033828 * 2
def baseEnd_3033828 : Nat := 1557811987068661367697685

theorem tailTrace_3033828 : CollatzResearch.WordTrace tailWord_3033828 prefixEnd_3033828 1557811987068661367697685 := by
  unfold tailWord_3033828
  simp only [CollatzResearch.WordTrace]
  refine ⟨55326398826483383708275069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73768531768644511611033425 55326398826483383708275069)
  ·
    refine ⟨20747399559931268890603151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55326398826483383708275069 20747399559931268890603151)
    ·
      refine ⟨31121099339896903335904727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20747399559931268890603151 31121099339896903335904727)
      ·
        refine ⟨46681649009845355003857091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31121099339896903335904727 46681649009845355003857091)
        ·
          refine ⟨70022473514768032505785637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46681649009845355003857091 70022473514768032505785637)
          ·
            refine ⟨13129213784019006094834807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70022473514768032505785637 13129213784019006094834807)
            ·
              refine ⟨19693820676028509142252211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13129213784019006094834807 19693820676028509142252211)
              ·
                refine ⟨29540731014042763713378317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19693820676028509142252211 29540731014042763713378317)
                ·
                  refine ⟨11077774130266036392516869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29540731014042763713378317 11077774130266036392516869)
                  ·
                    refine ⟨2077082649424881823596913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11077774130266036392516869 2077082649424881823596913)
                    ·
                      refine ⟨1557811987068661367697685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077082649424881823596913 1557811987068661367697685)
                      ·
                        rfl

theorem cell23_3033828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_3033828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033828 prefixEnd_3033828 := by exact prefixLift 3033828
  have htrace : WordTrace (prefixWord ++ tailWord_3033828) baseStart_3033828 baseEnd_3033828 := by
    simpa [prefixWord, tailWord_3033828, baseEnd_3033828] using wordTrace_append hprefix tailTrace_3033828
  have hstable : (prefixWord ++ tailWord_3033828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033828).length < 2 ^ (prefixWord ++ tailWord_3033828).sum := by decide
  have hdescent : baseEnd_3033828 < baseStart_3033828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033841 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3033841 : Nat := 118140960795 + 3033841 * 2 ^ 59
def prefixEnd_3033841 : Nat := 4983230072969 + 3 ^ 40 * 3033841 * 2
def baseEnd_3033841 : Nat := 1557818662317169816835125

theorem tailTrace_3033841 : CollatzResearch.WordTrace tailWord_3033841 prefixEnd_3033841 1557818662317169816835125 := by
  unfold tailWord_3033841
  simp only [CollatzResearch.WordTrace]
  refine ⟨110653271801919670636773377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73768847867946447091182251 110653271801919670636773377)
  ·
    refine ⟨82989953851439752977580033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110653271801919670636773377 82989953851439752977580033)
    ·
      refine ⟨62242465388579814733185025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82989953851439752977580033 62242465388579814733185025)
      ·
        refine ⟨46681849041434861049888769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62242465388579814733185025 46681849041434861049888769)
        ·
          refine ⟨35011386781076145787416577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46681849041434861049888769 35011386781076145787416577)
          ·
            refine ⟨26258540085807109340562433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35011386781076145787416577 26258540085807109340562433)
            ·
              refine ⟨19693905064355332005421825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26258540085807109340562433 19693905064355332005421825)
              ·
                refine ⟨14770428798266499004066369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19693905064355332005421825 14770428798266499004066369)
                ·
                  refine ⟨11077821598699874253049777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14770428798266499004066369 11077821598699874253049777)
                  ·
                    refine ⟨8308366199024905689787333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11077821598699874253049777 8308366199024905689787333)
                    ·
                      refine ⟨1557818662317169816835125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8308366199024905689787333 1557818662317169816835125)
                      ·
                        rfl

theorem cell23_3033841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3033841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033841 prefixEnd_3033841 := by exact prefixLift 3033841
  have htrace : WordTrace (prefixWord ++ tailWord_3033841) baseStart_3033841 baseEnd_3033841 := by
    simpa [prefixWord, tailWord_3033841, baseEnd_3033841] using wordTrace_append hprefix tailTrace_3033841
  have hstable : (prefixWord ++ tailWord_3033841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033841).length < 2 ^ (prefixWord ++ tailWord_3033841).sum := by decide
  have hdescent : baseEnd_3033841 < baseStart_3033841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033858 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3033858 : Nat := 118140960795 + 3033858 * 2 ^ 59
def prefixEnd_3033858 : Nat := 4983230072969 + 3 ^ 40 * 3033858 * 2
def baseEnd_3033858 : Nat := 1557827391488296250322547

theorem tailTrace_3033858 : CollatzResearch.WordTrace tailWord_3033858 prefixEnd_3033858 1557827391488296250322547 := by
  unfold tailWord_3033858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663472960714520635035557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73769261228572055026761485 27663472960714520635035557)
  ·
    refine ⟨5186901180133972619069167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27663472960714520635035557 5186901180133972619069167)
    ·
      refine ⟨7780351770200958928603751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186901180133972619069167 7780351770200958928603751)
      ·
        refine ⟨11670527655301438392905627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780351770200958928603751 11670527655301438392905627)
        ·
          refine ⟨17505791482952157589358441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670527655301438392905627 17505791482952157589358441)
          ·
            refine ⟨13129343612214118192018831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17505791482952157589358441 13129343612214118192018831)
            ·
              refine ⟨19694015418321177288028247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13129343612214118192018831 19694015418321177288028247)
              ·
                refine ⟨29541023127481765932042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19694015418321177288028247 29541023127481765932042371)
                ·
                  refine ⟨44311534691222648898063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29541023127481765932042371 44311534691222648898063557)
                  ·
                    refine ⟨8308412754604246668386917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44311534691222648898063557 8308412754604246668386917)
                    ·
                      refine ⟨1557827391488296250322547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8308412754604246668386917 1557827391488296250322547)
                      ·
                        rfl

theorem cell23_3033858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3033858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033858 prefixEnd_3033858 := by exact prefixLift 3033858
  have htrace : WordTrace (prefixWord ++ tailWord_3033858) baseStart_3033858 baseEnd_3033858 := by
    simpa [prefixWord, tailWord_3033858, baseEnd_3033858] using wordTrace_append hprefix tailTrace_3033858
  have hstable : (prefixWord ++ tailWord_3033858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033858).length < 2 ^ (prefixWord ++ tailWord_3033858).sum := by decide
  have hdescent : baseEnd_3033858 < baseStart_3033858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033881 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_3033881 : Nat := 118140960795 + 3033881 * 2 ^ 59
def prefixEnd_3033881 : Nat := 4983230072969 + 3 ^ 40 * 3033881 * 2
def baseEnd_3033881 : Nat := 519279733847783220111647

theorem tailTrace_3033881 : CollatzResearch.WordTrace tailWord_3033881 prefixEnd_3033881 519279733847783220111647 := by
  unfold tailWord_3033881
  simp only [CollatzResearch.WordTrace]
  refine ⟨110654730721774757468229497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73769820481183171645486331 110654730721774757468229497)
  ·
    refine ⟨82991048041331068101172123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110654730721774757468229497 82991048041331068101172123)
    ·
      refine ⟨124486572061996602151758185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82991048041331068101172123 124486572061996602151758185)
      ·
        refine ⟨93364929046497451613818639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124486572061996602151758185 93364929046497451613818639)
        ·
          refine ⟨140047393569746177420727959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93364929046497451613818639 140047393569746177420727959)
          ·
            refine ⟨210071090354619266131091939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140047393569746177420727959 210071090354619266131091939)
            ·
              refine ⟨315106635531928899196637909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210071090354619266131091939 315106635531928899196637909)
              ·
                refine ⟨7385311770279583574921201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315106635531928899196637909 7385311770279583574921201)
                ·
                  refine ⟨5538983827709687681190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385311770279583574921201 5538983827709687681190901)
                  ·
                    refine ⟨519279733847783220111647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5538983827709687681190901 519279733847783220111647)
                    ·
                      rfl

theorem cell23_3033881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_3033881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033881 prefixEnd_3033881 := by exact prefixLift 3033881
  have htrace : WordTrace (prefixWord ++ tailWord_3033881) baseStart_3033881 baseEnd_3033881 := by
    simpa [prefixWord, tailWord_3033881, baseEnd_3033881] using wordTrace_append hprefix tailTrace_3033881
  have hstable : (prefixWord ++ tailWord_3033881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033881).length < 2 ^ (prefixWord ++ tailWord_3033881).sum := by decide
  have hdescent : baseEnd_3033881 < baseStart_3033881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033928 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3033928 : Nat := 118140960795 + 3033928 * 2 ^ 59
def prefixEnd_3033928 : Nat := 4983230072969 + 3 ^ 40 * 3033928 * 2
def baseEnd_3033928 : Nat := 519287778378036992149075

theorem tailTrace_3033928 : CollatzResearch.WordTrace tailWord_3033928 prefixEnd_3033928 519287778378036992149075 := by
  unfold tailWord_3033928
  simp only [CollatzResearch.WordTrace]
  refine ⟨55328222476302242247595219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73770963301736322996793625 55328222476302242247595219)
  ·
    refine ⟨82992333714453363371392829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55328222476302242247595219 82992333714453363371392829)
    ·
      refine ⟨31122125142920011264272311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82992333714453363371392829 31122125142920011264272311)
      ·
        refine ⟨46683187714380016896408467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31122125142920011264272311 46683187714380016896408467)
        ·
          refine ⟨70024781571570025344612701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46683187714380016896408467 70024781571570025344612701)
          ·
            refine ⟨26259293089338759504229763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70024781571570025344612701 26259293089338759504229763)
            ·
              refine ⟨39388939634008139256344645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26259293089338759504229763 39388939634008139256344645)
              ·
                refine ⟨7385426181376526110564621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39388939634008139256344645 7385426181376526110564621)
                ·
                  refine ⟨2769534818016197291461733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7385426181376526110564621 2769534818016197291461733)
                  ·
                    refine ⟨519287778378036992149075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769534818016197291461733 519287778378036992149075)
                    ·
                      rfl

theorem cell23_3033928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3033928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033928 prefixEnd_3033928 := by exact prefixLift 3033928
  have htrace : WordTrace (prefixWord ++ tailWord_3033928) baseStart_3033928 baseEnd_3033928 := by
    simpa [prefixWord, tailWord_3033928, baseEnd_3033928] using wordTrace_append hprefix tailTrace_3033928
  have hstable : (prefixWord ++ tailWord_3033928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033928).length < 2 ^ (prefixWord ++ tailWord_3033928).sum := by decide
  have hdescent : baseEnd_3033928 < baseStart_3033928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033938 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3033938 : Nat := 118140960795 + 3033938 * 2 ^ 59
def prefixEnd_3033938 : Nat := 4983230072969 + 3 ^ 40 * 3033938 * 2
def baseEnd_3033938 : Nat := 1557868469940655937322179

theorem tailTrace_3033938 : CollatzResearch.WordTrace tailWord_3033938 prefixEnd_3033938 1557868469940655937322179 := by
  unfold tailWord_3033938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27664202420642064050763617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73771206455045504135369645 27664202420642064050763617)
  ·
    refine ⟨20748151815481548038072713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27664202420642064050763617 20748151815481548038072713)
    ·
      refine ⟨15561113861611161028554535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20748151815481548038072713 15561113861611161028554535)
      ·
        refine ⟨23341670792416741542831803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15561113861611161028554535 23341670792416741542831803)
        ·
          refine ⟨35012506188625112314247705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341670792416741542831803 35012506188625112314247705)
          ·
            refine ⟨26259379641468834235685779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35012506188625112314247705 26259379641468834235685779)
            ·
              refine ⟨39389069462203251353528669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26259379641468834235685779 39389069462203251353528669)
              ·
                refine ⟨14770901048326219257573251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39389069462203251353528669 14770901048326219257573251)
                ·
                  refine ⟨22156351572489328886359877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14770901048326219257573251 22156351572489328886359877)
                  ·
                    refine ⟨4154315919841749166192477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22156351572489328886359877 4154315919841749166192477)
                    ·
                      refine ⟨1557868469940655937322179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154315919841749166192477 1557868469940655937322179)
                      ·
                        rfl

theorem cell23_3033938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3033938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033938 prefixEnd_3033938 := by exact prefixLift 3033938
  have htrace : WordTrace (prefixWord ++ tailWord_3033938) baseStart_3033938 baseEnd_3033938 := by
    simpa [prefixWord, tailWord_3033938, baseEnd_3033938] using wordTrace_append hprefix tailTrace_3033938
  have hstable : (prefixWord ++ tailWord_3033938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033938).length < 2 ^ (prefixWord ++ tailWord_3033938).sum := by decide
  have hdescent : baseEnd_3033938 < baseStart_3033938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033941 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 10]
def baseStart_3033941 : Nat := 118140960795 + 3033941 * 2 ^ 59
def prefixEnd_3033941 : Nat := 4983230072969 + 3 ^ 40 * 3033941 * 2
def baseEnd_3033941 : Nat := 173096667820291047287185

theorem tailTrace_3033941 : CollatzResearch.WordTrace tailWord_3033941 prefixEnd_3033941 173096667820291047287185 := by
  unfold tailWord_3033941
  simp only [CollatzResearch.WordTrace]
  refine ⟨110656919101557387715413677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73771279401038258476942451 110656919101557387715413677)
  ·
    refine ⟨41496344663084020393280129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110656919101557387715413677 41496344663084020393280129)
    ·
      refine ⟨31122258497313015294960097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41496344663084020393280129 31122258497313015294960097)
      ·
        refine ⟨23341693872984761471220073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31122258497313015294960097 23341693872984761471220073)
        ·
          refine ⟨17506270404738571103415055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23341693872984761471220073 17506270404738571103415055)
          ·
            refine ⟨26259405607107856655122583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17506270404738571103415055 26259405607107856655122583)
            ·
              refine ⟨39389108410661784982683875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26259405607107856655122583 39389108410661784982683875)
              ·
                refine ⟨59083662615992677474025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39389108410661784982683875 59083662615992677474025813)
                ·
                  refine ⟨173096667820291047287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59083662615992677474025813 173096667820291047287185)
                  ·
                    rfl

theorem cell23_3033941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_3033941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033941 prefixEnd_3033941 := by exact prefixLift 3033941
  have htrace : WordTrace (prefixWord ++ tailWord_3033941) baseStart_3033941 baseEnd_3033941 := by
    simpa [prefixWord, tailWord_3033941, baseEnd_3033941] using wordTrace_append hprefix tailTrace_3033941
  have hstable : (prefixWord ++ tailWord_3033941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033941).length < 2 ^ (prefixWord ++ tailWord_3033941).sum := by decide
  have hdescent : baseEnd_3033941 < baseStart_3033941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033955 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3033955 : Nat := 118140960795 + 3033955 * 2 ^ 59
def prefixEnd_3033955 : Nat := 4983230072969 + 3 ^ 40 * 3033955 * 2
def baseEnd_3033955 : Nat := 1557877199111782370809601

theorem tailTrace_3033955 : CollatzResearch.WordTrace tailWord_3033955 prefixEnd_3033955 1557877199111782370809601 := by
  unfold tailWord_3033955
  simp only [CollatzResearch.WordTrace]
  refine ⟨110657429723506668106423319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73771619815671112070948879 110657429723506668106423319)
  ·
    refine ⟨165986144585260002159634979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110657429723506668106423319 165986144585260002159634979)
    ·
      refine ⟨248979216877890003239452469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165986144585260002159634979 248979216877890003239452469)
      ·
        refine ⟨23341801582302187803698669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248979216877890003239452469 23341801582302187803698669)
        ·
          refine ⟨8753175593363320426387001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23341801582302187803698669 8753175593363320426387001)
          ·
            refine ⟨6564881695022490319790251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8753175593363320426387001 6564881695022490319790251)
            ·
              refine ⟨9847322542533735479685377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6564881695022490319790251 9847322542533735479685377)
              ·
                refine ⟨7385491906900301609764033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9847322542533735479685377 7385491906900301609764033)
                ·
                  refine ⟨5539118930175226207323025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385491906900301609764033 5539118930175226207323025)
                  ·
                    refine ⟨4154339197631419655492269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539118930175226207323025 4154339197631419655492269)
                    ·
                      refine ⟨1557877199111782370809601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154339197631419655492269 1557877199111782370809601)
                      ·
                        rfl

theorem cell23_3033955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3033955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033955 prefixEnd_3033955 := by exact prefixLift 3033955
  have htrace : WordTrace (prefixWord ++ tailWord_3033955) baseStart_3033955 baseEnd_3033955 := by
    simpa [prefixWord, tailWord_3033955, baseEnd_3033955] using wordTrace_append hprefix tailTrace_3033955
  have hstable : (prefixWord ++ tailWord_3033955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033955).length < 2 ^ (prefixWord ++ tailWord_3033955).sum := by decide
  have hdescent : baseEnd_3033955 < baseStart_3033955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033995 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 2, 3, 2]
def baseStart_3033995 : Nat := 118140960795 + 3033995 * 2 ^ 59
def prefixEnd_3033995 : Nat := 4983230072969 + 3 ^ 40 * 3033995 * 2
def baseEnd_3033995 : Nat := 1557897738337962214309417

theorem tailTrace_3033995 : CollatzResearch.WordTrace tailWord_3033995 prefixEnd_3033995 1557897738337962214309417 := by
  unfold tailWord_3033995
  simp only [CollatzResearch.WordTrace]
  refine ⟨110658888643361754937879439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73772592428907836625252959 110658888643361754937879439)
  ·
    refine ⟨165988332965042632406819159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110658888643361754937879439 165988332965042632406819159)
    ·
      refine ⟨248982499447563948610228739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165988332965042632406819159 248982499447563948610228739)
      ·
        refine ⟨373473749171345922915343109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248982499447563948610228739 373473749171345922915343109)
        ·
          refine ⟨70026327969627360546626833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373473749171345922915343109 70026327969627360546626833)
          ·
            refine ⟨52519745977220520409970125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70026327969627360546626833 52519745977220520409970125)
            ·
              refine ⟨19694904741457695153738797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52519745977220520409970125 19694904741457695153738797)
              ·
                refine ⟨7385589278046635682652049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19694904741457695153738797 7385589278046635682652049)
                ·
                  refine ⟨5539191958534976761989037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385589278046635682652049 5539191958534976761989037)
                  ·
                    refine ⟨2077196984450616285745889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5539191958534976761989037 2077196984450616285745889)
                    ·
                      refine ⟨1557897738337962214309417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077196984450616285745889 1557897738337962214309417)
                      ·
                        rfl

theorem cell23_3033995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3, 2].length) (baseStart_3033995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033995 prefixEnd_3033995 := by exact prefixLift 3033995
  have htrace : WordTrace (prefixWord ++ tailWord_3033995) baseStart_3033995 baseEnd_3033995 := by
    simpa [prefixWord, tailWord_3033995, baseEnd_3033995] using wordTrace_append hprefix tailTrace_3033995
  have hstable : (prefixWord ++ tailWord_3033995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033995).length < 2 ^ (prefixWord ++ tailWord_3033995).sum := by decide
  have hdescent : baseEnd_3033995 < baseStart_3033995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034019 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 1, 1, 3]
def baseStart_3034019 : Nat := 118140960795 + 3034019 * 2 ^ 59
def prefixEnd_3034019 : Nat := 4983230072969 + 3 ^ 40 * 3034019 * 2
def baseEnd_3034019 : Nat := 1557910061873670120409307

theorem tailTrace_3034019 : CollatzResearch.WordTrace tailWord_3034019 prefixEnd_3034019 1557910061873670120409307 := by
  unfold tailWord_3034019
  simp only [CollatzResearch.WordTrace]
  refine ⟨110659763995274807036753111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73773175996849871357835407 110659763995274807036753111)
  ·
    refine ⟨165989645992912210555129667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110659763995274807036753111 165989645992912210555129667)
    ·
      refine ⟨248984468989368315832694501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165989645992912210555129667 248984468989368315832694501)
      ·
        refine ⟨46684587935506559218630219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248984468989368315832694501 46684587935506559218630219)
        ·
          refine ⟨70026881903259838827945329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46684587935506559218630219 70026881903259838827945329)
          ·
            refine ⟨52520161427444879120958997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70026881903259838827945329 52520161427444879120958997)
            ·
              refine ⟨2461882566911478708794953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52520161427444879120958997 2461882566911478708794953)
              ·
                refine ⟨1846411925183609031596215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461882566911478708794953 1846411925183609031596215)
                ·
                  refine ⟨2769617887775413547394323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846411925183609031596215 2769617887775413547394323)
                  ·
                    refine ⟨4154426831663120321091485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2769617887775413547394323 4154426831663120321091485)
                    ·
                      refine ⟨1557910061873670120409307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154426831663120321091485 1557910061873670120409307)
                      ·
                        rfl

theorem cell23_3034019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_3034019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034019 prefixEnd_3034019 := by exact prefixLift 3034019
  have htrace : WordTrace (prefixWord ++ tailWord_3034019) baseStart_3034019 baseEnd_3034019 := by
    simpa [prefixWord, tailWord_3034019, baseEnd_3034019] using wordTrace_append hprefix tailTrace_3034019
  have hstable : (prefixWord ++ tailWord_3034019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034019).length < 2 ^ (prefixWord ++ tailWord_3034019).sum := by decide
  have hdescent : baseEnd_3034019 < baseStart_3034019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034031 : List Nat := [1, 1, 2, 1, 2, 2, 2, 12]
def baseStart_3034031 : Nat := 118140960795 + 3034031 * 2 ^ 59
def prefixEnd_3034031 : Nat := 4983230072969 + 3 ^ 40 * 3034031 * 2
def baseEnd_3034031 : Nat := 57700600875612002720713

theorem tailTrace_3034031 : CollatzResearch.WordTrace tailWord_3034031 prefixEnd_3034031 57700600875612002720713 := by
  unfold tailWord_3034031
  simp only [CollatzResearch.WordTrace]
  refine ⟨110660201671231333086189947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73773467780820888724126631 110660201671231333086189947)
  ·
    refine ⟨165990302506846999629284921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110660201671231333086189947 165990302506846999629284921)
    ·
      refine ⟨124492726880135249721963691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165990302506846999629284921 124492726880135249721963691)
      ·
        refine ⟨186739090320202874582945537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124492726880135249721963691 186739090320202874582945537)
        ·
          refine ⟨140054317740152155937209153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186739090320202874582945537 140054317740152155937209153)
          ·
            refine ⟨105040738305114116952906865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140054317740152155937209153 105040738305114116952906865)
            ·
              refine ⟨78780553728835587714680149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105040738305114116952906865 78780553728835587714680149)
              ·
                refine ⟨57700600875612002720713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 78780553728835587714680149 57700600875612002720713)
                ·
                  rfl

theorem cell23_3034031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 12].length) (baseStart_3034031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034031 prefixEnd_3034031 := by exact prefixLift 3034031
  have htrace : WordTrace (prefixWord ++ tailWord_3034031) baseStart_3034031 baseEnd_3034031 := by
    simpa [prefixWord, tailWord_3034031, baseEnd_3034031] using wordTrace_append hprefix tailTrace_3034031
  have hstable : (prefixWord ++ tailWord_3034031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034031).length < 2 ^ (prefixWord ++ tailWord_3034031).sum := by decide
  have hdescent : baseEnd_3034031 < baseStart_3034031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034042 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_3034042 : Nat := 118140960795 + 3034042 * 2 ^ 59
def prefixEnd_3034042 : Nat := 4983230072969 + 3 ^ 40 * 3034042 * 2
def baseEnd_3034042 : Nat := 1557921871928723530421701

theorem tailTrace_3034042 : CollatzResearch.WordTrace tailWord_3034042 prefixEnd_3034042 1557921871928723530421701 := by
  unfold tailWord_3034042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27665150718547870491210095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73773735249460987976560253 27665150718547870491210095)
  ·
    refine ⟨41497726077821805736815143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27665150718547870491210095 41497726077821805736815143)
    ·
      refine ⟨62246589116732708605222715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41497726077821805736815143 62246589116732708605222715)
      ·
        refine ⟨93369883675099062907834073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62246589116732708605222715 93369883675099062907834073)
        ·
          refine ⟨70027412756324297180875555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93369883675099062907834073 70027412756324297180875555)
          ·
            refine ⟨105041119134486445771313333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70027412756324297180875555 105041119134486445771313333)
            ·
              refine ⟨9847604918858104291060625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105041119134486445771313333 9847604918858104291060625)
              ·
                refine ⟨7385703689143578218295469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9847604918858104291060625 7385703689143578218295469)
                ·
                  refine ⟨2769638883428841831860801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7385703689143578218295469 2769638883428841831860801)
                  ·
                    refine ⟨2077229162571631373895601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769638883428841831860801 2077229162571631373895601)
                    ·
                      refine ⟨1557921871928723530421701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077229162571631373895601 1557921871928723530421701)
                      ·
                        rfl

theorem cell23_3034042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_3034042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034042 prefixEnd_3034042 := by exact prefixLift 3034042
  have htrace : WordTrace (prefixWord ++ tailWord_3034042) baseStart_3034042 baseEnd_3034042 := by
    simpa [prefixWord, tailWord_3034042, baseEnd_3034042] using wordTrace_append hprefix tailTrace_3034042
  have hstable : (prefixWord ++ tailWord_3034042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034042).length < 2 ^ (prefixWord ++ tailWord_3034042).sum := by decide
  have hdescent : baseEnd_3034042 < baseStart_3034042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034059 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 1, 2, 2]
def baseStart_3034059 : Nat := 118140960795 + 3034059 * 2 ^ 59
def prefixEnd_3034059 : Nat := 4983230072969 + 3 ^ 40 * 3034059 * 2
def baseEnd_3034059 : Nat := 1557930601099849963909123

theorem tailTrace_3034059 : CollatzResearch.WordTrace tailWord_3034059 prefixEnd_3034059 1557930601099849963909123 := by
  unfold tailWord_3034059
  simp only [CollatzResearch.WordTrace]
  refine ⟨110661222915129893868209231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73774148610086595912139487 110661222915129893868209231)
  ·
    refine ⟨165991834372694840802313847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110661222915129893868209231 165991834372694840802313847)
    ·
      refine ⟨248987751559042261203470771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165991834372694840802313847 248987751559042261203470771)
      ·
        refine ⟨373481627338563391805206157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248987751559042261203470771 373481627338563391805206157)
        ·
          refine ⟨140055610251961271926952309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373481627338563391805206157 140055610251961271926952309)
          ·
            refine ⟨13130213461121369243151779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140055610251961271926952309 13130213461121369243151779)
            ·
              refine ⟨19695320191682053864727669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130213461121369243151779 19695320191682053864727669)
              ·
                refine ⟨1846436267970192549818219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19695320191682053864727669 1846436267970192549818219)
                ·
                  refine ⟨2769654401955288824727329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846436267970192549818219 2769654401955288824727329)
                  ·
                    refine ⟨2077240801466466618545497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769654401955288824727329 2077240801466466618545497)
                    ·
                      refine ⟨1557930601099849963909123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077240801466466618545497 1557930601099849963909123)
                      ·
                        rfl

theorem cell23_3034059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 2, 2].length) (baseStart_3034059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034059 prefixEnd_3034059 := by exact prefixLift 3034059
  have htrace : WordTrace (prefixWord ++ tailWord_3034059) baseStart_3034059 baseEnd_3034059 := by
    simpa [prefixWord, tailWord_3034059, baseEnd_3034059] using wordTrace_append hprefix tailTrace_3034059
  have hstable : (prefixWord ++ tailWord_3034059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034059).length < 2 ^ (prefixWord ++ tailWord_3034059).sum := by decide
  have hdescent : baseEnd_3034059 < baseStart_3034059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034062 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_3034062 : Nat := 118140960795 + 3034062 * 2 ^ 59
def prefixEnd_3034062 : Nat := 4983230072969 + 3 ^ 40 * 3034062 * 2
def baseEnd_3034062 : Nat := 1557932141541813452171609

theorem tailTrace_3034062 : CollatzResearch.WordTrace tailWord_3034062 prefixEnd_3034062 1557932141541813452171609 := by
  unfold tailWord_3034062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13832666541764878172571055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73774221556079350253712293 13832666541764878172571055)
  ·
    refine ⟨20748999812647317258856583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13832666541764878172571055 20748999812647317258856583)
    ·
      refine ⟨31123499718970975888284875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20748999812647317258856583 31123499718970975888284875)
      ·
        refine ⟨46685249578456463832427313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31123499718970975888284875 46685249578456463832427313)
        ·
          refine ⟨35013937183842347874320485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46685249578456463832427313 35013937183842347874320485)
          ·
            refine ⟨6565113221970440226435091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35013937183842347874320485 6565113221970440226435091)
            ·
              refine ⟨9847669832955660339652637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565113221970440226435091 9847669832955660339652637)
              ·
                refine ⟨3692876187358372627369739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9847669832955660339652637 3692876187358372627369739)
                ·
                  refine ⟨5539314281037558941054609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692876187358372627369739 5539314281037558941054609)
                  ·
                    refine ⟨4154485710778169205790957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539314281037558941054609 4154485710778169205790957)
                    ·
                      refine ⟨1557932141541813452171609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154485710778169205790957 1557932141541813452171609)
                      ·
                        rfl

theorem cell23_3034062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_3034062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034062 prefixEnd_3034062 := by exact prefixLift 3034062
  have htrace : WordTrace (prefixWord ++ tailWord_3034062) baseStart_3034062 baseEnd_3034062 := by
    simpa [prefixWord, tailWord_3034062, baseEnd_3034062] using wordTrace_append hprefix tailTrace_3034062
  have hstable : (prefixWord ++ tailWord_3034062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034062).length < 2 ^ (prefixWord ++ tailWord_3034062).sum := by decide
  have hdescent : baseEnd_3034062 < baseStart_3034062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034069 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_3034069 : Nat := 118140960795 + 3034069 * 2 ^ 59
def prefixEnd_3034069 : Nat := 4983230072969 + 3 ^ 40 * 3034069 * 2
def baseEnd_3034069 : Nat := 519311911968798308261359

theorem tailTrace_3034069 : CollatzResearch.WordTrace tailWord_3034069 prefixEnd_3034069 519311911968798308261359 := by
  unfold tailWord_3034069
  simp only [CollatzResearch.WordTrace]
  refine ⟨110661587645093665576073261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73774391763395777050715507 110661587645093665576073261)
  ·
    refine ⟨41498095366910124591027473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110661587645093665576073261 41498095366910124591027473)
    ·
      refine ⟨31123571525182593443270605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41498095366910124591027473 31123571525182593443270605)
      ·
        refine ⟨11671339321943472541226477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31123571525182593443270605 11671339321943472541226477)
        ·
          refine ⟨4376752245728802202959929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11671339321943472541226477 4376752245728802202959929)
          ·
            refine ⟨3282564184296601652219947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376752245728802202959929 3282564184296601652219947)
            ·
              refine ⟨4923846276444902478329921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282564184296601652219947 4923846276444902478329921)
              ·
                refine ⟨3692884707333676858747441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923846276444902478329921 3692884707333676858747441)
                ·
                  refine ⟨2769663530500257644060581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692884707333676858747441 2769663530500257644060581)
                  ·
                    refine ⟨519311911968798308261359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769663530500257644060581 519311911968798308261359)
                    ·
                      rfl

theorem cell23_3034069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_3034069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034069 prefixEnd_3034069 := by exact prefixLift 3034069
  have htrace : WordTrace (prefixWord ++ tailWord_3034069) baseStart_3034069 baseEnd_3034069 := by
    simpa [prefixWord, tailWord_3034069, baseEnd_3034069] using wordTrace_append hprefix tailTrace_3034069
  have hstable : (prefixWord ++ tailWord_3034069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034069).length < 2 ^ (prefixWord ++ tailWord_3034069).sum := by decide
  have hdescent : baseEnd_3034069 < baseStart_3034069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034110 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3034110 : Nat := 118140960795 + 3034110 * 2 ^ 59
def prefixEnd_3034110 : Nat := 4983230072969 + 3 ^ 40 * 3034110 * 2
def baseEnd_3034110 : Nat := 1557956788613229264371389

theorem tailTrace_3034110 : CollatzResearch.WordTrace tailWord_3034110 prefixEnd_3034110 1557956788613229264371389 := by
  unfold tailWord_3034110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13832885379743141197289473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73775388691963419718877189 13832885379743141197289473)
  ·
    refine ⟨10374664034807355897967105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13832885379743141197289473 10374664034807355897967105)
    ·
      refine ⟨7780998026105516923475329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10374664034807355897967105 7780998026105516923475329)
      ·
        refine ⟨5835748519579137692606497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7780998026105516923475329 5835748519579137692606497)
        ·
          refine ⟨4376811389684353269454873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5835748519579137692606497 4376811389684353269454873)
          ·
            refine ⟨3282608542263264952091155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376811389684353269454873 3282608542263264952091155)
            ·
              refine ⟨4923912813394897428136733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282608542263264952091155 4923912813394897428136733)
              ·
                refine ⟨1846467305023086535551275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4923912813394897428136733 1846467305023086535551275)
                ·
                  refine ⟨2769700957534629803326913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846467305023086535551275 2769700957534629803326913)
                  ·
                    refine ⟨2077275718150972352495185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769700957534629803326913 2077275718150972352495185)
                    ·
                      refine ⟨1557956788613229264371389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077275718150972352495185 1557956788613229264371389)
                      ·
                        rfl

theorem cell23_3034110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3034110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034110 prefixEnd_3034110 := by exact prefixLift 3034110
  have htrace : WordTrace (prefixWord ++ tailWord_3034110) baseStart_3034110 baseEnd_3034110 := by
    simpa [prefixWord, tailWord_3034110, baseEnd_3034110] using wordTrace_append hprefix tailTrace_3034110
  have hstable : (prefixWord ++ tailWord_3034110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034110).length < 2 ^ (prefixWord ++ tailWord_3034110).sum := by decide
  have hdescent : baseEnd_3034110 < baseStart_3034110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034149 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_3034149 : Nat := 118140960795 + 3034149 * 2 ^ 59
def prefixEnd_3034149 : Nat := 4983230072969 + 3 ^ 40 * 3034149 * 2
def baseEnd_3034149 : Nat := 1557976814358754611783709

theorem tailTrace_3034149 : CollatzResearch.WordTrace tailWord_3034149 prefixEnd_3034149 1557976814358754611783709 := by
  unfold tailWord_3034149
  simp only [CollatzResearch.WordTrace]
  refine ⟨110664505484803839238985501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73776336989869226159323667 110664505484803839238985501)
  ·
    refine ⟨41499189556801439714619563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110664505484803839238985501 41499189556801439714619563)
    ·
      refine ⟨62248784335202159571929345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41499189556801439714619563 62248784335202159571929345)
      ·
        refine ⟨46686588251401619678947009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62248784335202159571929345 46686588251401619678947009)
        ·
          refine ⟨35014941188551214759210257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46686588251401619678947009 35014941188551214759210257)
          ·
            refine ⟨26261205891413411069407693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35014941188551214759210257 26261205891413411069407693)
            ·
              refine ⟨9847952209280029151027885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26261205891413411069407693 9847952209280029151027885)
              ·
                refine ⟨3692982078480010931635457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9847952209280029151027885 3692982078480010931635457)
                ·
                  refine ⟨2769736558860008198726593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692982078480010931635457 2769736558860008198726593)
                  ·
                    refine ⟨2077302419145006149044945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769736558860008198726593 2077302419145006149044945)
                    ·
                      refine ⟨1557976814358754611783709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077302419145006149044945 1557976814358754611783709)
                      ·
                        rfl

theorem cell23_3034149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_3034149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034149 prefixEnd_3034149 := by exact prefixLift 3034149
  have htrace : WordTrace (prefixWord ++ tailWord_3034149) baseStart_3034149 baseEnd_3034149 := by
    simpa [prefixWord, tailWord_3034149, baseEnd_3034149] using wordTrace_append hprefix tailTrace_3034149
  have hstable : (prefixWord ++ tailWord_3034149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034149).length < 2 ^ (prefixWord ++ tailWord_3034149).sum := by decide
  have hdescent : baseEnd_3034149 < baseStart_3034149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034165 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3034165 : Nat := 118140960795 + 3034165 * 2 ^ 59
def prefixEnd_3034165 : Nat := 4983230072969 + 3 ^ 40 * 3034165 * 2
def baseEnd_3034165 : Nat := 1557985030049226549183635

theorem tailTrace_3034165 : CollatzResearch.WordTrace tailWord_3034165 prefixEnd_3034165 1557985030049226549183635 := by
  unfold tailWord_3034165
  simp only [CollatzResearch.WordTrace]
  refine ⟨110665089052745873971567949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73776726035163915981045299 110665089052745873971567949)
  ·
    refine ⟨41499408394779702739337981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110665089052745873971567949 41499408394779702739337981)
    ·
      refine ⟨15562278148042388527251743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41499408394779702739337981 15562278148042388527251743)
      ·
        refine ⟨23343417222063582790877615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15562278148042388527251743 23343417222063582790877615)
        ·
          refine ⟨35015125833095374186316423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23343417222063582790877615 35015125833095374186316423)
          ·
            refine ⟨52522688749643061279474635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35015125833095374186316423 52522688749643061279474635)
            ·
              refine ⟨78784033124464591919211953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52522688749643061279474635 78784033124464591919211953)
              ·
                refine ⟨59088024843348443939408965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78784033124464591919211953 59088024843348443939408965)
                ·
                  refine ⟨11079004658127833238639181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59088024843348443939408965 11079004658127833238639181)
                  ·
                    refine ⟨4154626746797937464489693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11079004658127833238639181 4154626746797937464489693)
                    ·
                      refine ⟨1557985030049226549183635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154626746797937464489693 1557985030049226549183635)
                      ·
                        rfl

theorem cell23_3034165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3034165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034165 prefixEnd_3034165 := by exact prefixLift 3034165
  have htrace : WordTrace (prefixWord ++ tailWord_3034165) baseStart_3034165 baseEnd_3034165 := by
    simpa [prefixWord, tailWord_3034165, baseEnd_3034165] using wordTrace_append hprefix tailTrace_3034165
  have hstable : (prefixWord ++ tailWord_3034165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034165).length < 2 ^ (prefixWord ++ tailWord_3034165).sum := by decide
  have hdescent : baseEnd_3034165 < baseStart_3034165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034189 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3034189 : Nat := 118140960795 + 3034189 * 2 ^ 59
def prefixEnd_3034189 : Nat := 4983230072969 + 3 ^ 40 * 3034189 * 2
def baseEnd_3034189 : Nat := 173110817064992717253725

theorem tailTrace_3034189 : CollatzResearch.WordTrace tailWord_3034189 prefixEnd_3034189 173110817064992717253725 := by
  unfold tailWord_3034189
  simp only [CollatzResearch.WordTrace]
  refine ⟨110665964404658926070441621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73777309603105950713627747 110665964404658926070441621)
  ·
    refine ⟨5187467081468387159551951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110665964404658926070441621 5187467081468387159551951)
    ·
      refine ⟨7781200622202580739327927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187467081468387159551951 7781200622202580739327927)
      ·
        refine ⟨11671800933303871108991891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781200622202580739327927 11671800933303871108991891)
        ·
          refine ⟨17507701399955806663487837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11671800933303871108991891 17507701399955806663487837)
          ·
            refine ⟨6565388024983427498807939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17507701399955806663487837 6565388024983427498807939)
            ·
              refine ⟨9848082037475141248211909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565388024983427498807939 9848082037475141248211909)
              ·
                refine ⟨1846515382026588984039733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9848082037475141248211909 1846515382026588984039733)
                ·
                  refine ⟨173110817064992717253725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1846515382026588984039733 173110817064992717253725)
                  ·
                    rfl

theorem cell23_3034189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3034189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034189 prefixEnd_3034189 := by exact prefixLift 3034189
  have htrace : WordTrace (prefixWord ++ tailWord_3034189) baseStart_3034189 baseEnd_3034189 := by
    simpa [prefixWord, tailWord_3034189, baseEnd_3034189] using wordTrace_append hprefix tailTrace_3034189
  have hstable : (prefixWord ++ tailWord_3034189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034189).length < 2 ^ (prefixWord ++ tailWord_3034189).sum := by decide
  have hdescent : baseEnd_3034189 < baseStart_3034189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034222 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3034222 : Nat := 118140960795 + 3034222 * 2 ^ 59
def prefixEnd_3034222 : Nat := 4983230072969 + 3 ^ 40 * 3034222 * 2
def baseEnd_3034222 : Nat := 1558014298446532826170873

theorem tailTrace_3034222 : CollatzResearch.WordTrace tailWord_3034222 prefixEnd_3034222 1558014298446532826170873 := by
  unfold tailWord_3034222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833396001692421588299115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73778112009026248470928613 13833396001692421588299115)
  ·
    refine ⟨20750094002538632382448673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13833396001692421588299115 20750094002538632382448673)
    ·
      refine ⟨15562570501903974286836505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20750094002538632382448673 15562570501903974286836505)
      ·
        refine ⟨11671927876427980715127379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562570501903974286836505 11671927876427980715127379)
        ·
          refine ⟨17507891814641971072691069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11671927876427980715127379 17507891814641971072691069)
          ·
            refine ⟨6565459430490739152259151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17507891814641971072691069 6565459430490739152259151)
            ·
              refine ⟨9848189145736108728388727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565459430490739152259151 9848189145736108728388727)
              ·
                refine ⟨14772283718604163092583091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848189145736108728388727 14772283718604163092583091)
                ·
                  refine ⟨22158425577906244638874637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14772283718604163092583091 22158425577906244638874637)
                  ·
                    refine ⟨8309409591714841739577989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22158425577906244638874637 8309409591714841739577989)
                    ·
                      refine ⟨1558014298446532826170873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8309409591714841739577989 1558014298446532826170873)
                      ·
                        rfl

theorem cell23_3034222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3034222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034222 prefixEnd_3034222 := by exact prefixLift 3034222
  have htrace : WordTrace (prefixWord ++ tailWord_3034222) baseStart_3034222 baseEnd_3034222 := by
    simpa [prefixWord, tailWord_3034222, baseEnd_3034222] using wordTrace_append hprefix tailTrace_3034222
  have hstable : (prefixWord ++ tailWord_3034222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034222).length < 2 ^ (prefixWord ++ tailWord_3034222).sum := by decide
  have hdescent : baseEnd_3034222 < baseStart_3034222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034249 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 1, 4]
def baseStart_3034249 : Nat := 118140960795 + 3034249 * 2 ^ 59
def prefixEnd_3034249 : Nat := 4983230072969 + 3 ^ 40 * 3034249 * 2
def baseEnd_3034249 : Nat := 519342720808068073511083

theorem tailTrace_3034249 : CollatzResearch.WordTrace tailWord_3034249 prefixEnd_3034249 519342720808068073511083 := by
  unfold tailWord_3034249
  simp only [CollatzResearch.WordTrace]
  refine ⟨110668152784441556317625801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73778768522961037545083867 110668152784441556317625801)
  ·
    refine ⟨83001114588331167238219351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110668152784441556317625801 83001114588331167238219351)
    ·
      refine ⟨124501671882496750857329027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83001114588331167238219351 124501671882496750857329027)
      ·
        refine ⟨186752507823745126285993541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124501671882496750857329027 186752507823745126285993541)
        ·
          refine ⟨35016095216952211178623789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186752507823745126285993541 35016095216952211178623789)
          ·
            refine ⟨13131035706357079191983921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35016095216952211178623789 13131035706357079191983921)
            ·
              refine ⟨9848276779767809393987941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13131035706357079191983921 9848276779767809393987941)
              ·
                refine ⟨1846551896206464261372739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9848276779767809393987941 1846551896206464261372739)
                ·
                  refine ⟨2769827844309696392059109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846551896206464261372739 2769827844309696392059109)
                  ·
                    refine ⟨519342720808068073511083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769827844309696392059109 519342720808068073511083)
                    ·
                      rfl

theorem cell23_3034249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_3034249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034249 prefixEnd_3034249 := by exact prefixLift 3034249
  have htrace : WordTrace (prefixWord ++ tailWord_3034249) baseStart_3034249 baseEnd_3034249 := by
    simpa [prefixWord, tailWord_3034249, baseEnd_3034249] using wordTrace_append hprefix tailTrace_3034249
  have hstable : (prefixWord ++ tailWord_3034249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034249).length < 2 ^ (prefixWord ++ tailWord_3034249).sum := by decide
  have hdescent : baseEnd_3034249 < baseStart_3034249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034275 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 3, 5]
def baseStart_3034275 : Nat := 118140960795 + 3034275 * 2 ^ 59
def prefixEnd_3034275 : Nat := 4983230072969 + 3 ^ 40 * 3034275 * 2
def baseEnd_3034275 : Nat := 519347170973740372936043

theorem tailTrace_3034275 : CollatzResearch.WordTrace tailWord_3034275 prefixEnd_3034275 519347170973740372936043 := by
  unfold tailWord_3034275
  simp only [CollatzResearch.WordTrace]
  refine ⟨110669101082347362758072279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73779400721564908505381519 110669101082347362758072279)
  ·
    refine ⟨166003651623521044137108419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110669101082347362758072279 166003651623521044137108419)
    ·
      refine ⟨249005477435281566205662629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166003651623521044137108419 249005477435281566205662629)
      ·
        refine ⟨46688527019115293663561743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249005477435281566205662629 46688527019115293663561743)
        ·
          refine ⟨70032790528672940495342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46688527019115293663561743 70032790528672940495342615)
          ·
            refine ⟨105049185793009410743013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70032790528672940495342615 105049185793009410743013923)
            ·
              refine ⟨157573778689514116114520885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105049185793009410743013923 157573778689514116114520885)
              ·
                refine ⟨14772541752141948385736333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157573778689514116114520885 14772541752141948385736333)
                ·
                  refine ⟨5539703157053230644651125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14772541752141948385736333 5539703157053230644651125)
                  ·
                    refine ⟨519347170973740372936043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5539703157053230644651125 519347170973740372936043)
                    ·
                      rfl

theorem cell23_3034275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].length) (baseStart_3034275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034275 prefixEnd_3034275 := by exact prefixLift 3034275
  have htrace : WordTrace (prefixWord ++ tailWord_3034275) baseStart_3034275 baseEnd_3034275 := by
    simpa [prefixWord, tailWord_3034275, baseEnd_3034275] using wordTrace_append hprefix tailTrace_3034275
  have hstable : (prefixWord ++ tailWord_3034275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034275).length < 2 ^ (prefixWord ++ tailWord_3034275).sum := by decide
  have hdescent : baseEnd_3034275 < baseStart_3034275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034315 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_3034315 : Nat := 118140960795 + 3034315 * 2 ^ 59
def prefixEnd_3034315 : Nat := 4983230072969 + 3 ^ 40 * 3034315 * 2
def baseEnd_3034315 : Nat := 1558062052147400962307945

theorem tailTrace_3034315 : CollatzResearch.WordTrace tailWord_3034315 prefixEnd_3034315 1558062052147400962307945 := by
  unfold tailWord_3034315
  simp only [CollatzResearch.WordTrace]
  refine ⟨110670560002202449589528399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73780373334801633059685599 110670560002202449589528399)
  ·
    refine ⟨166005840003303674384292599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110670560002202449589528399 166005840003303674384292599)
    ·
      refine ⟨249008760004955511576438899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166005840003303674384292599 249008760004955511576438899)
      ·
        refine ⟨373513140007433267364658349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249008760004955511576438899 373513140007433267364658349)
        ·
          refine ⟨140067427502787475261746881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373513140007433267364658349 140067427502787475261746881)
          ·
            refine ⟨105050570627090606446310161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140067427502787475261746881 105050570627090606446310161)
            ·
              refine ⟨78787927970317954834732621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105050570627090606446310161 78787927970317954834732621)
              ·
                refine ⟨29545472988869233063024733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78787927970317954834732621 29545472988869233063024733)
                ·
                  refine ⟨11079552370825962398634275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29545472988869233063024733 11079552370825962398634275)
                  ·
                    refine ⟨16619328556238943597951413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11079552370825962398634275 16619328556238943597951413)
                    ·
                      refine ⟨1558062052147400962307945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16619328556238943597951413 1558062052147400962307945)
                      ·
                        rfl

theorem cell23_3034315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_3034315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034315 prefixEnd_3034315 := by exact prefixLift 3034315
  have htrace : WordTrace (prefixWord ++ tailWord_3034315) baseStart_3034315 baseEnd_3034315 := by
    simpa [prefixWord, tailWord_3034315, baseEnd_3034315] using wordTrace_append hprefix tailTrace_3034315
  have hstable : (prefixWord ++ tailWord_3034315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034315).length < 2 ^ (prefixWord ++ tailWord_3034315).sum := by decide
  have hdescent : baseEnd_3034315 < baseStart_3034315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034322 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3034322 : Nat := 118140960795 + 3034322 * 2 ^ 59
def prefixEnd_3034322 : Nat := 4983230072969 + 3 ^ 40 * 3034322 * 2
def baseEnd_3034322 : Nat := 519355215503994144973471

theorem tailTrace_3034322 : CollatzResearch.WordTrace tailWord_3034322 prefixEnd_3034322 519355215503994144973471 := by
  unfold tailWord_3034322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27667703828294272446258305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73780543542118059856688813 27667703828294272446258305)
  ·
    refine ⟨20750777871220704334693729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27667703828294272446258305 20750777871220704334693729)
    ·
      refine ⟨15563083403415528251020297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20750777871220704334693729 15563083403415528251020297)
      ·
        refine ⟨11672312552561646188265223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15563083403415528251020297 11672312552561646188265223)
        ·
          refine ⟨17508468828842469282397835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11672312552561646188265223 17508468828842469282397835)
          ·
            refine ⟨26262703243263703923596753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17508468828842469282397835 26262703243263703923596753)
            ·
              refine ⟨19697027432447777942697565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26262703243263703923596753 19697027432447777942697565)
              ·
                refine ⟨7386385287167916728511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19697027432447777942697565 7386385287167916728511587)
                ·
                  refine ⟨11079577930751875092767381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386385287167916728511587 11079577930751875092767381)
                  ·
                    refine ⟨519355215503994144973471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11079577930751875092767381 519355215503994144973471)
                    ·
                      rfl

theorem cell23_3034322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3034322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034322 prefixEnd_3034322 := by exact prefixLift 3034322
  have htrace : WordTrace (prefixWord ++ tailWord_3034322) baseStart_3034322 baseEnd_3034322 := by
    simpa [prefixWord, tailWord_3034322, baseEnd_3034322] using wordTrace_append hprefix tailTrace_3034322
  have hstable : (prefixWord ++ tailWord_3034322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034322).length < 2 ^ (prefixWord ++ tailWord_3034322).sum := by decide
  have hdescent : baseEnd_3034322 < baseStart_3034322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034326 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3034326 : Nat := 118140960795 + 3034326 * 2 ^ 59
def prefixEnd_3034326 : Nat := 4983230072969 + 3 ^ 40 * 3034326 * 2
def baseEnd_3034326 : Nat := 519355900144866806423465

theorem tailTrace_3034326 : CollatzResearch.WordTrace tailWord_3034326 prefixEnd_3034326 519355900144866806423465 := by
  unfold tailWord_3034326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916935075322662404261177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73780640803441732312119221 6916935075322662404261177)
  ·
    refine ⟨5187701306491996803195883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6916935075322662404261177 5187701306491996803195883)
    ·
      refine ⟨7781551959737995204793825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187701306491996803195883 7781551959737995204793825)
      ·
        refine ⟨5836163969803496403595369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7781551959737995204793825 5836163969803496403595369)
        ·
          refine ⟨4377122977352622302696527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836163969803496403595369 4377122977352622302696527)
          ·
            refine ⟨6565684466028933454044791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377122977352622302696527 6565684466028933454044791)
            ·
              refine ⟨9848526699043400181067187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565684466028933454044791 9848526699043400181067187)
              ·
                refine ⟨14772790048565100271600781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848526699043400181067187 14772790048565100271600781)
                ·
                  refine ⟨5539796268211912601850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14772790048565100271600781 5539796268211912601850293)
                  ·
                    refine ⟨519355900144866806423465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5539796268211912601850293 519355900144866806423465)
                    ·
                      rfl

theorem cell23_3034326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3034326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034326 prefixEnd_3034326 := by exact prefixLift 3034326
  have htrace : WordTrace (prefixWord ++ tailWord_3034326) baseStart_3034326 baseEnd_3034326 := by
    simpa [prefixWord, tailWord_3034326, baseEnd_3034326] using wordTrace_append hprefix tailTrace_3034326
  have hstable : (prefixWord ++ tailWord_3034326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034326).length < 2 ^ (prefixWord ++ tailWord_3034326).sum := by decide
  have hdescent : baseEnd_3034326 < baseStart_3034326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034329 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 5, 2, 2]
def baseStart_3034329 : Nat := 118140960795 + 3034329 * 2 ^ 59
def prefixEnd_3034329 : Nat := 4983230072969 + 3 ^ 40 * 3034329 * 2
def baseEnd_3034329 : Nat := 1558069240876563907532881

theorem tailTrace_3034329 : CollatzResearch.WordTrace tailWord_3034329 prefixEnd_3034329 1558069240876563907532881 := by
  unfold tailWord_3034329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110671070624151729980538041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73780713749434486653692027 110671070624151729980538041)
  ·
    refine ⟨83003302968113797485403531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110671070624151729980538041 83003302968113797485403531)
    ·
      refine ⟨124504954452170696228105297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83003302968113797485403531 124504954452170696228105297)
      ·
        refine ⟨93378715839128022171078973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124504954452170696228105297 93378715839128022171078973)
        ·
          refine ⟨35017018439673008314154615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93378715839128022171078973 35017018439673008314154615)
          ·
            refine ⟨52525527659509512471231923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35017018439673008314154615 52525527659509512471231923)
            ·
              refine ⟨78788291489264268706847885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52525527659509512471231923 78788291489264268706847885)
              ·
                refine ⟨29545609308474100765067957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78788291489264268706847885 29545609308474100765067957)
                ·
                  refine ⟨2769900872669446946725121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29545609308474100765067957 2769900872669446946725121)
                  ·
                    refine ⟨2077425654502085210043841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769900872669446946725121 2077425654502085210043841)
                    ·
                      refine ⟨1558069240876563907532881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077425654502085210043841 1558069240876563907532881)
                      ·
                        rfl

theorem cell23_3034329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_3034329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034329 prefixEnd_3034329 := by exact prefixLift 3034329
  have htrace : WordTrace (prefixWord ++ tailWord_3034329) baseStart_3034329 baseEnd_3034329 := by
    simpa [prefixWord, tailWord_3034329, baseEnd_3034329] using wordTrace_append hprefix tailTrace_3034329
  have hstable : (prefixWord ++ tailWord_3034329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034329).length < 2 ^ (prefixWord ++ tailWord_3034329).sum := by decide
  have hdescent : baseEnd_3034329 < baseStart_3034329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034333 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3034333 : Nat := 118140960795 + 3034333 * 2 ^ 59
def prefixEnd_3034333 : Nat := 4983230072969 + 3 ^ 40 * 3034333 * 2
def baseEnd_3034333 : Nat := 1558071294799181891882863

theorem tailTrace_3034333 : CollatzResearch.WordTrace tailWord_3034333 prefixEnd_3034333 1558071294799181891882863 := by
  unfold tailWord_3034333
  simp only [CollatzResearch.WordTrace]
  refine ⟨110671216516137238663683653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73780811010758159109122435 110671216516137238663683653)
  ·
    refine ⟨20750853096775732249440685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110671216516137238663683653 20750853096775732249440685)
    ·
      refine ⟨7781569911290899593540257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20750853096775732249440685 7781569911290899593540257)
      ·
        refine ⟨5836177433468174695155193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7781569911290899593540257 5836177433468174695155193)
        ·
          refine ⟨4377133075101131021366395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836177433468174695155193 4377133075101131021366395)
          ·
            refine ⟨6565699612651696532049593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377133075101131021366395 6565699612651696532049593)
            ·
              refine ⟨4924274709488772399037195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565699612651696532049593 4924274709488772399037195)
              ·
                refine ⟨7386412064233158598555793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924274709488772399037195 7386412064233158598555793)
                ·
                  refine ⟨5539809048174868948916845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7386412064233158598555793 5539809048174868948916845)
                  ·
                    refine ⟨2077428393065575855843817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5539809048174868948916845 2077428393065575855843817)
                    ·
                      refine ⟨1558071294799181891882863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077428393065575855843817 1558071294799181891882863)
                      ·
                        rfl

theorem cell23_3034333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3034333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034333 prefixEnd_3034333 := by exact prefixLift 3034333
  have htrace : WordTrace (prefixWord ++ tailWord_3034333) baseStart_3034333 baseEnd_3034333 := by
    simpa [prefixWord, tailWord_3034333, baseEnd_3034333] using wordTrace_append hprefix tailTrace_3034333
  have hstable : (prefixWord ++ tailWord_3034333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034333).length < 2 ^ (prefixWord ++ tailWord_3034333).sum := by decide
  have hdescent : baseEnd_3034333 < baseStart_3034333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034335 : List Nat := [1, 1, 2, 3, 2, 1, 4, 9]
def baseStart_3034335 : Nat := 118140960795 + 3034335 * 2 ^ 59
def prefixEnd_3034335 : Nat := 4983230072969 + 3 ^ 40 * 3034335 * 2
def baseEnd_3034335 : Nat := 57706382287425588298439

theorem tailTrace_3034335 : CollatzResearch.WordTrace tailWord_3034335 prefixEnd_3034335 57706382287425588298439 := by
  unfold tailWord_3034335
  simp only [CollatzResearch.WordTrace]
  refine ⟨110671289462129993005256459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73780859641419995336837639 110671289462129993005256459)
  ·
    refine ⟨166006934193194989507884689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110671289462129993005256459 166006934193194989507884689)
    ·
      refine ⟨124505200644896242130913517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166006934193194989507884689 124505200644896242130913517)
      ·
        refine ⟨46689450241836090799092569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124505200644896242130913517 46689450241836090799092569)
        ·
          refine ⟨35017087681377068099319427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46689450241836090799092569 35017087681377068099319427)
          ·
            refine ⟨52525631522065602148979141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35017087681377068099319427 52525631522065602148979141)
            ·
              refine ⟨9848555910387300402933589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52525631522065602148979141 9848555910387300402933589)
              ·
                refine ⟨57706382287425588298439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9848555910387300402933589 57706382287425588298439)
                ·
                  rfl

theorem cell23_3034335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 9].length) (baseStart_3034335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034335 prefixEnd_3034335 := by exact prefixLift 3034335
  have htrace : WordTrace (prefixWord ++ tailWord_3034335) baseStart_3034335 baseEnd_3034335 := by
    simpa [prefixWord, tailWord_3034335, baseEnd_3034335] using wordTrace_append hprefix tailTrace_3034335
  have hstable : (prefixWord ++ tailWord_3034335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034335).length < 2 ^ (prefixWord ++ tailWord_3034335).sum := by decide
  have hdescent : baseEnd_3034335 < baseStart_3034335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034346 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_3034346 : Nat := 118140960795 + 3034346 * 2 ^ 59
def prefixEnd_3034346 : Nat := 4983230072969 + 3 ^ 40 * 3034346 * 2
def baseEnd_3034346 : Nat := 1558077970047690341020303

theorem tailTrace_3034346 : CollatzResearch.WordTrace tailWord_3034346 prefixEnd_3034346 1558077970047690341020303 := by
  unfold tailWord_3034346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27667922666272535470976723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73781127110060094589271261 27667922666272535470976723)
  ·
    refine ⟨41501883999408803206465085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27667922666272535470976723 41501883999408803206465085)
    ·
      refine ⟨15563206499778301202424407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41501883999408803206465085 15563206499778301202424407)
      ·
        refine ⟨23344809749667451803636611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15563206499778301202424407 23344809749667451803636611)
        ·
          refine ⟨35017214624501177705454917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23344809749667451803636611 35017214624501177705454917)
          ·
            refine ⟨6565727742093970819772797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35017214624501177705454917 6565727742093970819772797)
            ·
              refine ⟨2462147903285239057414799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6565727742093970819772797 2462147903285239057414799)
              ·
                refine ⟨3693221854927858586122199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462147903285239057414799 3693221854927858586122199)
                ·
                  refine ⟨5539832782391787879183299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693221854927858586122199 5539832782391787879183299)
                  ·
                    refine ⟨8309749173587681818774949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5539832782391787879183299 8309749173587681818774949)
                    ·
                      refine ⟨1558077970047690341020303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8309749173587681818774949 1558077970047690341020303)
                      ·
                        rfl

theorem cell23_3034346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_3034346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034346 prefixEnd_3034346 := by exact prefixLift 3034346
  have htrace : WordTrace (prefixWord ++ tailWord_3034346) baseStart_3034346 baseEnd_3034346 := by
    simpa [prefixWord, tailWord_3034346, baseEnd_3034346] using wordTrace_append hprefix tailTrace_3034346
  have hstable : (prefixWord ++ tailWord_3034346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034346).length < 2 ^ (prefixWord ++ tailWord_3034346).sum := by decide
  have hdescent : baseEnd_3034346 < baseStart_3034346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034349 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3034349 : Nat := 118140960795 + 3034349 * 2 ^ 59
def prefixEnd_3034349 : Nat := 4983230072969 + 3 ^ 40 * 3034349 * 2
def baseEnd_3034349 : Nat := 1558079510489653829282789

theorem tailTrace_3034349 : CollatzResearch.WordTrace tailWord_3034349 prefixEnd_3034349 1558079510489653829282789 := by
  unfold tailWord_3034349
  simp only [CollatzResearch.WordTrace]
  refine ⟨110671800084079273396266101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73781200056052848930844067 110671800084079273396266101)
  ·
    refine ⟨10375481257882431880899947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110671800084079273396266101 10375481257882431880899947)
    ·
      refine ⟨15563221886823647821349921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10375481257882431880899947 15563221886823647821349921)
      ·
        refine ⟨11672416415117735866012441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15563221886823647821349921 11672416415117735866012441)
        ·
          refine ⟨8754312311338301899509331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11672416415117735866012441 8754312311338301899509331)
          ·
            refine ⟨13131468467007452849263997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8754312311338301899509331 13131468467007452849263997)
            ·
              refine ⟨4924300675127794818473999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13131468467007452849263997 4924300675127794818473999)
              ·
                refine ⟨7386451012691692227710999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924300675127794818473999 7386451012691692227710999)
                ·
                  refine ⟨11079676519037538341566499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386451012691692227710999 11079676519037538341566499)
                  ·
                    refine ⟨16619514778556307512349749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11079676519037538341566499 16619514778556307512349749)
                    ·
                      refine ⟨1558079510489653829282789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16619514778556307512349749 1558079510489653829282789)
                      ·
                        rfl

theorem cell23_3034349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3034349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034349 prefixEnd_3034349 := by exact prefixLift 3034349
  have htrace : WordTrace (prefixWord ++ tailWord_3034349) baseStart_3034349 baseEnd_3034349 := by
    simpa [prefixWord, tailWord_3034349, baseEnd_3034349] using wordTrace_append hprefix tailTrace_3034349
  have hstable : (prefixWord ++ tailWord_3034349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034349).length < 2 ^ (prefixWord ++ tailWord_3034349).sum := by decide
  have hdescent : baseEnd_3034349 < baseStart_3034349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034362 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_3034362 : Nat := 118140960795 + 3034362 * 2 ^ 59
def prefixEnd_3034362 : Nat := 4983230072969 + 3 ^ 40 * 3034362 * 2
def baseEnd_3034362 : Nat := 1558086185738162278420229

theorem tailTrace_3034362 : CollatzResearch.WordTrace tailWord_3034362 prefixEnd_3034362 1558086185738162278420229 := by
  unfold tailWord_3034362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27668068558258044154122335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73781516155354784410992893 27668068558258044154122335)
  ·
    refine ⟨41502102837387066231183503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27668068558258044154122335 41502102837387066231183503)
    ·
      refine ⟨62253154256080599346775255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41502102837387066231183503 62253154256080599346775255)
      ·
        refine ⟨93379731384120899020162883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62253154256080599346775255 93379731384120899020162883)
        ·
          refine ⟨140069597076181348530244325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93379731384120899020162883 140069597076181348530244325)
          ·
            refine ⟨26263049451784002849420811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140069597076181348530244325 26263049451784002849420811)
            ·
              refine ⟨39394574177676004274131217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26263049451784002849420811 39394574177676004274131217)
              ·
                refine ⟨29545930633257003205598413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39394574177676004274131217 29545930633257003205598413)
                ·
                  refine ⟨11079723987471376202099405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29545930633257003205598413 11079723987471376202099405)
                  ·
                    refine ⟨4154896495301766075787277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11079723987471376202099405 4154896495301766075787277)
                    ·
                      refine ⟨1558086185738162278420229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154896495301766075787277 1558086185738162278420229)
                      ·
                        rfl

theorem cell23_3034362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_3034362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034362 prefixEnd_3034362 := by exact prefixLift 3034362
  have htrace : WordTrace (prefixWord ++ tailWord_3034362) baseStart_3034362 baseEnd_3034362 := by
    simpa [prefixWord, tailWord_3034362, baseEnd_3034362] using wordTrace_append hprefix tailTrace_3034362
  have hstable : (prefixWord ++ tailWord_3034362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034362).length < 2 ^ (prefixWord ++ tailWord_3034362).sum := by decide
  have hdescent : baseEnd_3034362 < baseStart_3034362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034379 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3]
def baseStart_3034379 : Nat := 118140960795 + 3034379 * 2 ^ 59
def prefixEnd_3034379 : Nat := 4983230072969 + 3 ^ 40 * 3034379 * 2
def baseEnd_3034379 : Nat := 1558094914909288711907651

theorem tailTrace_3034379 : CollatzResearch.WordTrace tailWord_3034379 prefixEnd_3034379 1558094914909288711907651 := by
  unfold tailWord_3034379
  simp only [CollatzResearch.WordTrace]
  refine ⟨110672894273970588519858191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73781929515980392346572127 110672894273970588519858191)
  ·
    refine ⟨166009341410955882779787287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110672894273970588519858191 166009341410955882779787287)
    ·
      refine ⟨249014012116433824169680931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166009341410955882779787287 249014012116433824169680931)
      ·
        refine ⟨373521018174650736254521397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249014012116433824169680931 373521018174650736254521397)
        ·
          refine ⟨35017595453873506523861381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373521018174650736254521397 35017595453873506523861381)
          ·
            refine ⟨6565799147601282473224009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35017595453873506523861381 6565799147601282473224009)
            ·
              refine ⟨4924349360700961854918007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565799147601282473224009 4924349360700961854918007)
              ·
                refine ⟨7386524041051442782377011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924349360700961854918007 7386524041051442782377011)
                ·
                  refine ⟨11079786061577164173565517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386524041051442782377011 11079786061577164173565517)
                  ·
                    refine ⟨4154919773091436565087069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11079786061577164173565517 4154919773091436565087069)
                    ·
                      refine ⟨1558094914909288711907651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154919773091436565087069 1558094914909288711907651)
                      ·
                        rfl

theorem cell23_3034379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].length) (baseStart_3034379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034379 prefixEnd_3034379 := by exact prefixLift 3034379
  have htrace : WordTrace (prefixWord ++ tailWord_3034379) baseStart_3034379 baseEnd_3034379 := by
    simpa [prefixWord, tailWord_3034379, baseEnd_3034379] using wordTrace_append hprefix tailTrace_3034379
  have hstable : (prefixWord ++ tailWord_3034379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034379).length < 2 ^ (prefixWord ++ tailWord_3034379).sum := by decide
  have hdescent : baseEnd_3034379 < baseStart_3034379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034395 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 8]
def baseStart_3034395 : Nat := 118140960795 + 3034395 * 2 ^ 59
def prefixEnd_3034395 : Nat := 4983230072969 + 3 ^ 40 * 3034395 * 2
def baseEnd_3034395 : Nat := 519367710199920216435859

theorem tailTrace_3034395 : CollatzResearch.WordTrace tailWord_3034395 prefixEnd_3034395 519367710199920216435859 := by
  unfold tailWord_3034395
  simp only [CollatzResearch.WordTrace]
  refine ⟨110673477841912623252440639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73782318561275082168293759 110673477841912623252440639)
  ·
    refine ⟨166010216762868934878660959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110673477841912623252440639 166010216762868934878660959)
    ·
      refine ⟨249015325144303402317991439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166010216762868934878660959 249015325144303402317991439)
      ·
        refine ⟨373522987716455103476987159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249015325144303402317991439 373522987716455103476987159)
        ·
          refine ⟨560284481574682655215480739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373522987716455103476987159 560284481574682655215480739)
          ·
            refine ⟨840426722362023982823221109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560284481574682655215480739 840426722362023982823221109)
            ·
              refine ⟨78790005221439748389676979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 840426722362023982823221109 78790005221439748389676979)
              ·
                refine ⟨118185007832159622584515469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78790005221439748389676979 118185007832159622584515469)
                ·
                  refine ⟨44319377937059858469193301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118185007832159622584515469 44319377937059858469193301)
                  ·
                    refine ⟨519367710199920216435859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44319377937059858469193301 519367710199920216435859)
                    ·
                      rfl

theorem cell23_3034395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_3034395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034395 prefixEnd_3034395 := by exact prefixLift 3034395
  have htrace : WordTrace (prefixWord ++ tailWord_3034395) baseStart_3034395 baseEnd_3034395 := by
    simpa [prefixWord, tailWord_3034395, baseEnd_3034395] using wordTrace_append hprefix tailTrace_3034395
  have hstable : (prefixWord ++ tailWord_3034395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034395).length < 2 ^ (prefixWord ++ tailWord_3034395).sum := by decide
  have hdescent : baseEnd_3034395 < baseStart_3034395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034400 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3034400 : Nat := 118140960795 + 3034400 * 2 ^ 59
def prefixEnd_3034400 : Nat := 4983230072969 + 3 ^ 40 * 3034400 * 2
def baseEnd_3034400 : Nat := 1558105698003033129745055

theorem tailTrace_3034400 : CollatzResearch.WordTrace tailWord_3034400 prefixEnd_3034400 1558105698003033129745055 := by
  unfold tailWord_3034400
  simp only [CollatzResearch.WordTrace]
  refine ⟨55336830103447254553186327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73782440137929672737581769 55336830103447254553186327)
  ·
    refine ⟨83005245155170881829779491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55336830103447254553186327 83005245155170881829779491)
    ·
      refine ⟨124507867732756322744669237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83005245155170881829779491 124507867732756322744669237)
      ·
        refine ⟨11672612599945905257312741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124507867732756322744669237 11672612599945905257312741)
        ·
          refine ⟨2188614862489857235746139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11672612599945905257312741 2188614862489857235746139)
          ·
            refine ⟨3282922293734785853619209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188614862489857235746139 3282922293734785853619209)
            ·
              refine ⟨2462191720301089390214407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282922293734785853619209 2462191720301089390214407)
              ·
                refine ⟨3693287580451634085321611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462191720301089390214407 3693287580451634085321611)
                ·
                  refine ⟨5539931370677451127982417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693287580451634085321611 5539931370677451127982417)
                  ·
                    refine ⟨4154948528008088345986813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539931370677451127982417 4154948528008088345986813)
                    ·
                      refine ⟨1558105698003033129745055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154948528008088345986813 1558105698003033129745055)
                      ·
                        rfl

theorem cell23_3034400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3034400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034400 prefixEnd_3034400 := by exact prefixLift 3034400
  have htrace : WordTrace (prefixWord ++ tailWord_3034400) baseStart_3034400 baseEnd_3034400 := by
    simpa [prefixWord, tailWord_3034400, baseEnd_3034400] using wordTrace_append hprefix tailTrace_3034400
  have hstable : (prefixWord ++ tailWord_3034400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034400).length < 2 ^ (prefixWord ++ tailWord_3034400).sum := by decide
  have hdescent : baseEnd_3034400 < baseStart_3034400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034413 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3034413 : Nat := 118140960795 + 3034413 * 2 ^ 59
def prefixEnd_3034413 : Nat := 4983230072969 + 3 ^ 40 * 3034413 * 2
def baseEnd_3034413 : Nat := 1558112373251541578882495

theorem tailTrace_3034413 : CollatzResearch.WordTrace tailWord_3034413 prefixEnd_3034413 1558112373251541578882495 := by
  unfold tailWord_3034413
  simp only [CollatzResearch.WordTrace]
  refine ⟨110674134355847412326595893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73782756237231608217730595 110674134355847412326595893)
  ·
    refine ⟨10375700095860694905618365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110674134355847412326595893 10375700095860694905618365)
    ·
      refine ⟨3890887535947760589606887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10375700095860694905618365 3890887535947760589606887)
      ·
        refine ⟨5836331303921640884410331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890887535947760589606887 5836331303921640884410331)
        ·
          refine ⟨8754496955882461326615497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836331303921640884410331 8754496955882461326615497)
          ·
            refine ⟨6565872716911845994961623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8754496955882461326615497 6565872716911845994961623)
            ·
              refine ⟨9848809075367768992442435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565872716911845994961623 9848809075367768992442435)
              ·
                refine ⟨14773213613051653488663653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848809075367768992442435 14773213613051653488663653)
                ·
                  refine ⟨2769977552447185029124435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14773213613051653488663653 2769977552447185029124435)
                  ·
                    refine ⟨4154966328670777543686653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2769977552447185029124435 4154966328670777543686653)
                    ·
                      refine ⟨1558112373251541578882495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4154966328670777543686653 1558112373251541578882495)
                      ·
                        rfl

theorem cell23_3034413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3034413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034413 prefixEnd_3034413 := by exact prefixLift 3034413
  have htrace : WordTrace (prefixWord ++ tailWord_3034413) baseStart_3034413 baseEnd_3034413 := by
    simpa [prefixWord, tailWord_3034413, baseEnd_3034413] using wordTrace_append hprefix tailTrace_3034413
  have hstable : (prefixWord ++ tailWord_3034413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034413).length < 2 ^ (prefixWord ++ tailWord_3034413).sum := by decide
  have hdescent : baseEnd_3034413 < baseStart_3034413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034432 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3034432 : Nat := 118140960795 + 3034432 * 2 ^ 59
def prefixEnd_3034432 : Nat := 4983230072969 + 3 ^ 40 * 3034432 * 2
def baseEnd_3034432 : Nat := 1558122129383977004544907

theorem tailTrace_3034432 : CollatzResearch.WordTrace tailWord_3034432 prefixEnd_3034432 1558122129383977004544907 := by
  unfold tailWord_3034432
  simp only [CollatzResearch.WordTrace]
  refine ⟨55337413671389289285768775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73783218228519052381025033 55337413671389289285768775)
  ·
    refine ⟨83006120507083933928653163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55337413671389289285768775 83006120507083933928653163)
    ·
      refine ⟨124509180760625900892979745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83006120507083933928653163 124509180760625900892979745)
      ·
        refine ⟨93381885570469425669734809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124509180760625900892979745 93381885570469425669734809)
        ·
          refine ⟨70036414177852069252301107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93381885570469425669734809 70036414177852069252301107)
          ·
            refine ⟨105054621266778103878451661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70036414177852069252301107 105054621266778103878451661)
            ·
              refine ⟨39395482975041788954419373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105054621266778103878451661 39395482975041788954419373)
              ·
                refine ⟨14773306115640670857907265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39395482975041788954419373 14773306115640670857907265)
                ·
                  refine ⟨11079979586730503143430449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14773306115640670857907265 11079979586730503143430449)
                  ·
                    refine ⟨8309984690047877357572837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11079979586730503143430449 8309984690047877357572837)
                    ·
                      refine ⟨1558122129383977004544907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8309984690047877357572837 1558122129383977004544907)
                      ·
                        rfl

theorem cell23_3034432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3034432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034432 prefixEnd_3034432 := by exact prefixLift 3034432
  have htrace : WordTrace (prefixWord ++ tailWord_3034432) baseStart_3034432 baseEnd_3034432 := by
    simpa [prefixWord, tailWord_3034432, baseEnd_3034432] using wordTrace_append hprefix tailTrace_3034432
  have hstable : (prefixWord ++ tailWord_3034432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034432).length < 2 ^ (prefixWord ++ tailWord_3034432).sum := by decide
  have hdescent : baseEnd_3034432 < baseStart_3034432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034479 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 5, 2]
def baseStart_3034479 : Nat := 118140960795 + 3034479 * 2 ^ 59
def prefixEnd_3034479 : Nat := 4983230072969 + 3 ^ 40 * 3034479 * 2
def baseEnd_3034479 : Nat := 1558146262974738320657191

theorem tailTrace_3034479 : CollatzResearch.WordTrace tailWord_3034479 prefixEnd_3034479 1558146262974738320657191 := by
  unfold tailWord_3034479
  simp only [CollatzResearch.WordTrace]
  refine ⟨110676541573608305598498491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73784361049072203732332327 110676541573608305598498491)
  ·
    refine ⟨166014812360412458397747737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110676541573608305598498491 166014812360412458397747737)
    ·
      refine ⟨124511109270309343798310803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166014812360412458397747737 124511109270309343798310803)
      ·
        refine ⟨186766663905464015697466205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124511109270309343798310803 186766663905464015697466205)
        ·
          refine ⟨70037498964549005886549827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186766663905464015697466205 70037498964549005886549827)
          ·
            refine ⟨105056248446823508829824741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70037498964549005886549827 105056248446823508829824741)
            ·
              refine ⟨19698046583779407905592139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105056248446823508829824741 19698046583779407905592139)
              ·
                refine ⟨29547069875669111858388209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19698046583779407905592139 29547069875669111858388209)
                ·
                  refine ⟨22160302406751833893791157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29547069875669111858388209 22160302406751833893791157)
                  ·
                    refine ⟨2077528350632984427542921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22160302406751833893791157 2077528350632984427542921)
                    ·
                      refine ⟨1558146262974738320657191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077528350632984427542921 1558146262974738320657191)
                      ·
                        rfl

theorem cell23_3034479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5, 2].length) (baseStart_3034479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034479 prefixEnd_3034479 := by exact prefixLift 3034479
  have htrace : WordTrace (prefixWord ++ tailWord_3034479) baseStart_3034479 baseEnd_3034479 := by
    simpa [prefixWord, tailWord_3034479, baseEnd_3034479] using wordTrace_append hprefix tailTrace_3034479
  have hstable : (prefixWord ++ tailWord_3034479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034479).length < 2 ^ (prefixWord ++ tailWord_3034479).sum := by decide
  have hdescent : baseEnd_3034479 < baseStart_3034479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034593 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_3034593 : Nat := 118140960795 + 3034593 * 2 ^ 59
def prefixEnd_3034593 : Nat := 4983230072969 + 3 ^ 40 * 3034593 * 2
def baseEnd_3034593 : Nat := 1558204799769350874631667

theorem tailTrace_3034593 : CollatzResearch.WordTrace tailWord_3034593 prefixEnd_3034593 1558204799769350874631667 := by
  unfold tailWord_3034593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110680699495195303068148433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73787132996796868712098955 110680699495195303068148433)
  ·
    refine ⟨83010524621396477301111325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110680699495195303068148433 83010524621396477301111325)
    ·
      refine ⟨31128946733023678987916747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83010524621396477301111325 31128946733023678987916747)
      ·
        refine ⟨46693420099535518481875121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31128946733023678987916747 46693420099535518481875121)
        ·
          refine ⟨35020065074651638861406341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46693420099535518481875121 35020065074651638861406341)
          ·
            refine ⟨6566262201497182286513689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35020065074651638861406341 6566262201497182286513689)
            ·
              refine ⟨4924696651122886714885267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566262201497182286513689 4924696651122886714885267)
              ·
                refine ⟨7387044976684330072327901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924696651122886714885267 7387044976684330072327901)
                ·
                  refine ⟨2770141866256623777122963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7387044976684330072327901 2770141866256623777122963)
                  ·
                    refine ⟨4155212799384935665684445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770141866256623777122963 4155212799384935665684445)
                    ·
                      refine ⟨1558204799769350874631667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155212799384935665684445 1558204799769350874631667)
                      ·
                        rfl

theorem cell23_3034593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_3034593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034593 prefixEnd_3034593 := by exact prefixLift 3034593
  have htrace : WordTrace (prefixWord ++ tailWord_3034593) baseStart_3034593 baseEnd_3034593 := by
    simpa [prefixWord, tailWord_3034593, baseEnd_3034593] using wordTrace_append hprefix tailTrace_3034593
  have hstable : (prefixWord ++ tailWord_3034593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034593).length < 2 ^ (prefixWord ++ tailWord_3034593).sum := by decide
  have hdescent : baseEnd_3034593 < baseStart_3034593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034613 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3034613 : Nat := 118140960795 + 3034613 * 2 ^ 59
def prefixEnd_3034613 : Nat := 4983230072969 + 3 ^ 40 * 3034613 * 2
def baseEnd_3034613 : Nat := 519405023127480265460525

theorem tailTrace_3034613 : CollatzResearch.WordTrace tailWord_3034613 prefixEnd_3034613 519405023127480265460525 := by
  unfold tailWord_3034613
  simp only [CollatzResearch.WordTrace]
  refine ⟨110681428955122846483876493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73787619303415230989250995 110681428955122846483876493)
  ·
    refine ⟨41505535858171067431453685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110681428955122846483876493 41505535858171067431453685)
    ·
      refine ⟨3891143986703537571698783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41505535858171067431453685 3891143986703537571698783)
      ·
        refine ⟨5836715980055306357548175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891143986703537571698783 5836715980055306357548175)
        ·
          refine ⟨8755073970082959536322263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836715980055306357548175 8755073970082959536322263)
          ·
            refine ⟨13132610955124439304483395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755073970082959536322263 13132610955124439304483395)
            ·
              refine ⟨19698916432686658956725093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13132610955124439304483395 19698916432686658956725093)
              ·
                refine ⟨3693546831128748554385955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19698916432686658956725093 3693546831128748554385955)
                ·
                  refine ⟨5540320246693122831578933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693546831128748554385955 5540320246693122831578933)
                  ·
                    refine ⟨519405023127480265460525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540320246693122831578933 519405023127480265460525)
                    ·
                      rfl

theorem cell23_3034613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3034613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034613 prefixEnd_3034613 := by exact prefixLift 3034613
  have htrace : WordTrace (prefixWord ++ tailWord_3034613) baseStart_3034613 baseEnd_3034613 := by
    simpa [prefixWord, tailWord_3034613, baseEnd_3034613] using wordTrace_append hprefix tailTrace_3034613
  have hstable : (prefixWord ++ tailWord_3034613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034613).length < 2 ^ (prefixWord ++ tailWord_3034613).sum := by decide
  have hdescent : baseEnd_3034613 < baseStart_3034613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034616 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3034616 : Nat := 118140960795 + 3034616 * 2 ^ 59
def prefixEnd_3034616 : Nat := 4983230072969 + 3 ^ 40 * 3034616 * 2
def baseEnd_3034616 : Nat := 1558216609824404284644061

theorem tailTrace_3034616 : CollatzResearch.WordTrace tailWord_3034616 prefixEnd_3034616 1558216609824404284644061 := by
  unfold tailWord_3034616
  simp only [CollatzResearch.WordTrace]
  refine ⟨55340769187055988998117851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73787692249407985330823801 55340769187055988998117851)
  ·
    refine ⟨83011153780583983497176777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55340769187055988998117851 83011153780583983497176777)
    ·
      refine ⟨62258365335437987622882583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83011153780583983497176777 62258365335437987622882583)
      ·
        refine ⟨93387548003156981434323875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62258365335437987622882583 93387548003156981434323875)
        ·
          refine ⟨140081322004735472151485813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93387548003156981434323875 140081322004735472151485813)
          ·
            refine ⟨13132623937943950514201795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140081322004735472151485813 13132623937943950514201795)
            ·
              refine ⟨19698935906915925771302693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13132623937943950514201795 19698935906915925771302693)
              ·
                refine ⟨3693550482546736082119255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19698935906915925771302693 3693550482546736082119255)
                ·
                  refine ⟨5540325723820104123178883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693550482546736082119255 5540325723820104123178883)
                  ·
                    refine ⟨8310488585730156184768325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540325723820104123178883 8310488585730156184768325)
                    ·
                      refine ⟨1558216609824404284644061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8310488585730156184768325 1558216609824404284644061)
                      ·
                        rfl

theorem cell23_3034616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3034616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034616 prefixEnd_3034616 := by exact prefixLift 3034616
  have htrace : WordTrace (prefixWord ++ tailWord_3034616) baseStart_3034616 baseEnd_3034616 := by
    simpa [prefixWord, tailWord_3034616, baseEnd_3034616] using wordTrace_append hprefix tailTrace_3034616
  have hstable : (prefixWord ++ tailWord_3034616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034616).length < 2 ^ (prefixWord ++ tailWord_3034616).sum := by decide
  have hdescent : baseEnd_3034616 < baseStart_3034616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034629 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_3034629 : Nat := 118140960795 + 3034629 * 2 ^ 59
def prefixEnd_3034629 : Nat := 4983230072969 + 3 ^ 40 * 3034629 * 2
def baseEnd_3034629 : Nat := 1558223285072912733781501

theorem tailTrace_3034629 : CollatzResearch.WordTrace tailWord_3034629 prefixEnd_3034629 1558223285072912733781501 := by
  unfold tailWord_3034629
  simp only [CollatzResearch.WordTrace]
  refine ⟨110682012523064881216458941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73788008348709920810972627 110682012523064881216458941)
  ·
    refine ⟨41505754696149330456172103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110682012523064881216458941 41505754696149330456172103)
    ·
      refine ⟨62258632044223995684258155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41505754696149330456172103 62258632044223995684258155)
      ·
        refine ⟨93387948066335993526387233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62258632044223995684258155 93387948066335993526387233)
        ·
          refine ⟨70040961049751995144790425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93387948066335993526387233 70040961049751995144790425)
          ·
            refine ⟨52530720787313996358592819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70040961049751995144790425 52530720787313996358592819)
            ·
              refine ⟨78796081180970994537889229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52530720787313996358592819 78796081180970994537889229)
              ·
                refine ⟨29548530442864122951708461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78796081180970994537889229 29548530442864122951708461)
                ·
                  refine ⟨11080698916074046106890673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29548530442864122951708461 11080698916074046106890673)
                  ·
                    refine ⟨8310524187055534580168005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11080698916074046106890673 8310524187055534580168005)
                    ·
                      refine ⟨1558223285072912733781501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8310524187055534580168005 1558223285072912733781501)
                      ·
                        rfl

theorem cell23_3034629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_3034629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034629 prefixEnd_3034629 := by exact prefixLift 3034629
  have htrace : WordTrace (prefixWord ++ tailWord_3034629) baseStart_3034629 baseEnd_3034629 := by
    simpa [prefixWord, tailWord_3034629, baseEnd_3034629] using wordTrace_append hprefix tailTrace_3034629
  have hstable : (prefixWord ++ tailWord_3034629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034629).length < 2 ^ (prefixWord ++ tailWord_3034629).sum := by decide
  have hdescent : baseEnd_3034629 < baseStart_3034629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034644 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3034644 : Nat := 118140960795 + 3034644 * 2 ^ 59
def prefixEnd_3034644 : Nat := 4983230072969 + 3 ^ 40 * 3034644 * 2
def baseEnd_3034644 : Nat := 1558230987282730175093933

theorem tailTrace_3034644 : CollatzResearch.WordTrace tailWord_3034644 prefixEnd_3034644 1558230987282730175093933 := by
  unfold tailWord_3034644
  simp only [CollatzResearch.WordTrace]
  refine ⟨55341279809005269389127493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73788373078673692518836657 55341279809005269389127493)
  ·
    refine ⟨10376489964188488010461405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55341279809005269389127493 10376489964188488010461405)
    ·
      refine ⟨3891183736570683003923027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10376489964188488010461405 3891183736570683003923027)
      ·
        refine ⟨5836775604856024505884541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891183736570683003923027 5836775604856024505884541)
        ·
          refine ⟨2188790851821009189706703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5836775604856024505884541 2188790851821009189706703)
          ·
            refine ⟨3283186277731513784560055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188790851821009189706703 3283186277731513784560055)
            ·
              refine ⟨4924779416597270676840083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283186277731513784560055 4924779416597270676840083)
              ·
                refine ⟨7387169124895906015260125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924779416597270676840083 7387169124895906015260125)
                ·
                  refine ⟨2770188421835964755722547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7387169124895906015260125 2770188421835964755722547)
                  ·
                    refine ⟨4155282632753947133583821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770188421835964755722547 4155282632753947133583821)
                    ·
                      refine ⟨1558230987282730175093933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155282632753947133583821 1558230987282730175093933)
                      ·
                        rfl

theorem cell23_3034644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3034644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034644 prefixEnd_3034644 := by exact prefixLift 3034644
  have htrace : WordTrace (prefixWord ++ tailWord_3034644) baseStart_3034644 baseEnd_3034644 := by
    simpa [prefixWord, tailWord_3034644, baseEnd_3034644] using wordTrace_append hprefix tailTrace_3034644
  have hstable : (prefixWord ++ tailWord_3034644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034644).length < 2 ^ (prefixWord ++ tailWord_3034644).sum := by decide
  have hdescent : baseEnd_3034644 < baseStart_3034644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034649 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_3034649 : Nat := 118140960795 + 3034649 * 2 ^ 59
def prefixEnd_3034649 : Nat := 4983230072969 + 3 ^ 40 * 3034649 * 2
def baseEnd_3034649 : Nat := 1558233554686002655531409

theorem tailTrace_3034649 : CollatzResearch.WordTrace tailWord_3034649 prefixEnd_3034649 1558233554686002655531409 := by
  unfold tailWord_3034649
  simp only [CollatzResearch.WordTrace]
  refine ⟨110682741982992424632187001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73788494655328283088124667 110682741982992424632187001)
  ·
    refine ⟨83012056487244318474140251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110682741982992424632187001 83012056487244318474140251)
    ·
      refine ⟨124518084730866477711210377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83012056487244318474140251 124518084730866477711210377)
      ·
        refine ⟨93388563548149858283407783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124518084730866477711210377 93388563548149858283407783)
        ·
          refine ⟨140082845322224787425111675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93388563548149858283407783 140082845322224787425111675)
          ·
            refine ⟨210124267983337181137667513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140082845322224787425111675 210124267983337181137667513)
            ·
              refine ⟨157593200987502885853250635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210124267983337181137667513 157593200987502885853250635)
              ·
                refine ⟨236389801481254328779875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157593200987502885853250635 236389801481254328779875953)
                ·
                  refine ⟨177292351110940746584906965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236389801481254328779875953 177292351110940746584906965)
                  ·
                    refine ⟨4155289479162673748083757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 177292351110940746584906965 4155289479162673748083757)
                    ·
                      refine ⟨1558233554686002655531409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155289479162673748083757 1558233554686002655531409)
                      ·
                        rfl

theorem cell23_3034649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_3034649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034649 prefixEnd_3034649 := by exact prefixLift 3034649
  have htrace : WordTrace (prefixWord ++ tailWord_3034649) baseStart_3034649 baseEnd_3034649 := by
    simpa [prefixWord, tailWord_3034649, baseEnd_3034649] using wordTrace_append hprefix tailTrace_3034649
  have hstable : (prefixWord ++ tailWord_3034649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034649).length < 2 ^ (prefixWord ++ tailWord_3034649).sum := by decide
  have hdescent : baseEnd_3034649 < baseStart_3034649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034656 : List Nat := [2, 1, 1, 6, 1, 2, 2, 8]
def baseStart_3034656 : Nat := 118140960795 + 3034656 * 2 ^ 59
def prefixEnd_3034656 : Nat := 4983230072969 + 3 ^ 40 * 3034656 * 2
def baseEnd_3034656 : Nat := 57712487001873486227551

theorem tailTrace_3034656 : CollatzResearch.WordTrace tailWord_3034656 prefixEnd_3034656 57712487001873486227551 := by
  unfold tailWord_3034656
  simp only [CollatzResearch.WordTrace]
  refine ⟨55341498646983532413845911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73788664862644709885127881 55341498646983532413845911)
  ·
    refine ⟨83012247970475298620768867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55341498646983532413845911 83012247970475298620768867)
    ·
      refine ⟨124518371955712947931153301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83012247970475298620768867 124518371955712947931153301)
      ·
        refine ⟨5836798685424044434272811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124518371955712947931153301 5836798685424044434272811)
        ·
          refine ⟨8755198028136066651409217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836798685424044434272811 8755198028136066651409217)
          ·
            refine ⟨6566398521102049988556913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8755198028136066651409217 6566398521102049988556913)
            ·
              refine ⟨4924798890826537491417685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566398521102049988556913 4924798890826537491417685)
              ·
                refine ⟨57712487001873486227551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4924798890826537491417685 57712487001873486227551)
                ·
                  rfl

theorem cell23_3034656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_3034656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034656 prefixEnd_3034656 := by exact prefixLift 3034656
  have htrace : WordTrace (prefixWord ++ tailWord_3034656) baseStart_3034656 baseEnd_3034656 := by
    simpa [prefixWord, tailWord_3034656, baseEnd_3034656] using wordTrace_append hprefix tailTrace_3034656
  have hstable : (prefixWord ++ tailWord_3034656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034656).length < 2 ^ (prefixWord ++ tailWord_3034656).sum := by decide
  have hdescent : baseEnd_3034656 < baseStart_3034656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034670 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3034670 : Nat := 118140960795 + 3034670 * 2 ^ 59
def prefixEnd_3034670 : Nat := 4983230072969 + 3 ^ 40 * 3034670 * 2
def baseEnd_3034670 : Nat := 1558244337779747073368813

theorem tailTrace_3034670 : CollatzResearch.WordTrace tailWord_3034670 prefixEnd_3034670 1558244337779747073368813 := by
  unfold tailWord_3034670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835438489489543152337683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73789005277277563479134309 13835438489489543152337683)
  ·
    refine ⟨20753157734234314728506525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13835438489489543152337683 20753157734234314728506525)
    ·
      refine ⟨7782434150337868023189947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20753157734234314728506525 7782434150337868023189947)
      ·
        refine ⟨11673651225506802034784921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782434150337868023189947 11673651225506802034784921)
        ·
          refine ⟨8755238419130101526088691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11673651225506802034784921 8755238419130101526088691)
          ·
            refine ⟨13132857628695152289133037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755238419130101526088691 13132857628695152289133037)
            ·
              refine ⟨4924821610760682108424889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13132857628695152289133037 4924821610760682108424889)
              ·
                refine ⟨3693616208070511581318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924821610760682108424889 3693616208070511581318667)
                ·
                  refine ⟨5540424312105767371978001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693616208070511581318667 5540424312105767371978001)
                  ·
                    refine ⟨4155318234079325528983501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5540424312105767371978001 4155318234079325528983501)
                    ·
                      refine ⟨1558244337779747073368813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155318234079325528983501 1558244337779747073368813)
                      ·
                        rfl

theorem cell23_3034670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3034670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034670 prefixEnd_3034670 := by exact prefixLift 3034670
  have htrace : WordTrace (prefixWord ++ tailWord_3034670) baseStart_3034670 baseEnd_3034670 := by
    simpa [prefixWord, tailWord_3034670, baseEnd_3034670] using wordTrace_append hprefix tailTrace_3034670
  have hstable : (prefixWord ++ tailWord_3034670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034670).length < 2 ^ (prefixWord ++ tailWord_3034670).sum := by decide
  have hdescent : baseEnd_3034670 < baseStart_3034670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034699 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 2, 6]
def baseStart_3034699 : Nat := 118140960795 + 3034699 * 2 ^ 59
def prefixEnd_3034699 : Nat := 4983230072969 + 3 ^ 40 * 3034699 * 2
def baseEnd_3034699 : Nat := 519419742906242486635393

theorem tailTrace_3034699 : CollatzResearch.WordTrace tailWord_3034699 prefixEnd_3034699 519419742906242486635393 := by
  unfold tailWord_3034699
  simp only [CollatzResearch.WordTrace]
  refine ⟨110684565632811283171507151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73789710421874188781004767 110684565632811283171507151)
  ·
    refine ⟨166026848449216924757260727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110684565632811283171507151 166026848449216924757260727)
    ·
      refine ⟨249040272673825387135891091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166026848449216924757260727 249040272673825387135891091)
      ·
        refine ⟨373560409010738080703836637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249040272673825387135891091 373560409010738080703836637)
        ·
          refine ⟨140085153379026780263938739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373560409010738080703836637 140085153379026780263938739)
          ·
            refine ⟨210127730068540170395908109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140085153379026780263938739 210127730068540170395908109)
            ·
              refine ⟨78797898775702563898465541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210127730068540170395908109 78797898775702563898465541)
              ·
                refine ⟨14774606020444230730962289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78797898775702563898465541 14774606020444230730962289)
                ·
                  refine ⟨11080954515333173048221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14774606020444230730962289 11080954515333173048221717)
                  ·
                    refine ⟨519419742906242486635393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11080954515333173048221717 519419742906242486635393)
                    ·
                      rfl

theorem cell23_3034699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_3034699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034699 prefixEnd_3034699 := by exact prefixLift 3034699
  have htrace : WordTrace (prefixWord ++ tailWord_3034699) baseStart_3034699 baseEnd_3034699 := by
    simpa [prefixWord, tailWord_3034699, baseEnd_3034699] using wordTrace_append hprefix tailTrace_3034699
  have hstable : (prefixWord ++ tailWord_3034699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034699).length < 2 ^ (prefixWord ++ tailWord_3034699).sum := by decide
  have hdescent : baseEnd_3034699 < baseStart_3034699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034700 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3034700 : Nat := 118140960795 + 3034700 * 2 ^ 59
def prefixEnd_3034700 : Nat := 4983230072969 + 3 ^ 40 * 3034700 * 2
def baseEnd_3034700 : Nat := 1558259742199381955993675

theorem tailTrace_3034700 : CollatzResearch.WordTrace tailWord_3034700 prefixEnd_3034700 1558259742199381955993675 := by
  unfold tailWord_3034700
  simp only [CollatzResearch.WordTrace]
  refine ⟨55342301052903830171146777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73789734737205106894862369 55342301052903830171146777)
  ·
    refine ⟨41506725789677872628360083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55342301052903830171146777 41506725789677872628360083)
    ·
      refine ⟨62260088684516808942540125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41506725789677872628360083 62260088684516808942540125)
      ·
        refine ⟨23347533256693803353452547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62260088684516808942540125 23347533256693803353452547)
        ·
          refine ⟨35021299885040705030178821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23347533256693803353452547 35021299885040705030178821)
          ·
            refine ⟨6566493728445132193158529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35021299885040705030178821 6566493728445132193158529)
            ·
              refine ⟨4924870296333849144868897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566493728445132193158529 4924870296333849144868897)
              ·
                refine ⟨3693652722250386858651673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924870296333849144868897 3693652722250386858651673)
                ·
                  refine ⟨2770239541687790143988755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3693652722250386858651673 2770239541687790143988755)
                  ·
                    refine ⟨4155359312531685215983133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770239541687790143988755 4155359312531685215983133)
                    ·
                      refine ⟨1558259742199381955993675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155359312531685215983133 1558259742199381955993675)
                      ·
                        rfl

theorem cell23_3034700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3034700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034700 prefixEnd_3034700 := by exact prefixLift 3034700
  have htrace : WordTrace (prefixWord ++ tailWord_3034700) baseStart_3034700 baseEnd_3034700 := by
    simpa [prefixWord, tailWord_3034700, baseEnd_3034700] using wordTrace_append hprefix tailTrace_3034700
  have hstable : (prefixWord ++ tailWord_3034700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034700).length < 2 ^ (prefixWord ++ tailWord_3034700).sum := by decide
  have hdescent : baseEnd_3034700 < baseStart_3034700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034706 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3034706 : Nat := 118140960795 + 3034706 * 2 ^ 59
def prefixEnd_3034706 : Nat := 4983230072969 + 3 ^ 40 * 3034706 * 2
def baseEnd_3034706 : Nat := 1558262823083308932518647

theorem tailTrace_3034706 : CollatzResearch.WordTrace tailWord_3034706 prefixEnd_3034706 1558262823083308932518647 := by
  unfold tailWord_3034706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671205235946480841752993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73789880629190615578007981 27671205235946480841752993)
  ·
    refine ⟨20753403926959860631314745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27671205235946480841752993 20753403926959860631314745)
    ·
      refine ⟨15565052945219895473486059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20753403926959860631314745 15565052945219895473486059)
      ·
        refine ⟨23347579417829843210229089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15565052945219895473486059 23347579417829843210229089)
        ·
          refine ⟨17510684563372382407671817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23347579417829843210229089 17510684563372382407671817)
          ·
            refine ⟨13133013422529286805753863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17510684563372382407671817 13133013422529286805753863)
            ·
              refine ⟨19699520133793930208630795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133013422529286805753863 19699520133793930208630795)
              ·
                refine ⟨29549280200690895312946193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19699520133793930208630795 29549280200690895312946193)
                ·
                  refine ⟨22161960150518171484709645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29549280200690895312946193 22161960150518171484709645)
                  ·
                    refine ⟨8310735056444314306766117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22161960150518171484709645 8310735056444314306766117)
                    ·
                      refine ⟨1558262823083308932518647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8310735056444314306766117 1558262823083308932518647)
                      ·
                        rfl

theorem cell23_3034706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3034706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034706 prefixEnd_3034706 := by exact prefixLift 3034706
  have htrace : WordTrace (prefixWord ++ tailWord_3034706) baseStart_3034706 baseEnd_3034706 := by
    simpa [prefixWord, tailWord_3034706, baseEnd_3034706] using wordTrace_append hprefix tailTrace_3034706
  have hstable : (prefixWord ++ tailWord_3034706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034706).length < 2 ^ (prefixWord ++ tailWord_3034706).sum := by decide
  have hdescent : baseEnd_3034706 < baseStart_3034706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034716 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3034716 : Nat := 118140960795 + 3034716 * 2 ^ 59
def prefixEnd_3034716 : Nat := 4983230072969 + 3 ^ 40 * 3034716 * 2
def baseEnd_3034716 : Nat := 519422652629951297797867

theorem tailTrace_3034716 : CollatzResearch.WordTrace tailWord_3034716 prefixEnd_3034716 519422652629951297797867 := by
  unfold tailWord_3034716
  simp only [CollatzResearch.WordTrace]
  refine ⟨55342592836874847537438001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73790123782499796716584001 55342592836874847537438001)
  ·
    refine ⟨41506944627656135653078501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55342592836874847537438001 41506944627656135653078501)
    ·
      refine ⟨7782552117685525434952219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41506944627656135653078501 7782552117685525434952219)
      ·
        refine ⟨11673828176528288152428329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782552117685525434952219 11673828176528288152428329)
        ·
          refine ⟨8755371132396216114321247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11673828176528288152428329 8755371132396216114321247)
          ·
            refine ⟨13133056698594324171481871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755371132396216114321247 13133056698594324171481871)
            ·
              refine ⟨19699585047891486257222807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133056698594324171481871 19699585047891486257222807)
              ·
                refine ⟨29549377571837229385834211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19699585047891486257222807 29549377571837229385834211)
                ·
                  refine ⟨44324066357755844078751317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29549377571837229385834211 44324066357755844078751317)
                  ·
                    refine ⟨519422652629951297797867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44324066357755844078751317 519422652629951297797867)
                    ·
                      rfl

theorem cell23_3034716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3034716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034716 prefixEnd_3034716 := by exact prefixLift 3034716
  have htrace : WordTrace (prefixWord ++ tailWord_3034716) baseStart_3034716 baseEnd_3034716 := by
    simpa [prefixWord, tailWord_3034716, baseEnd_3034716] using wordTrace_append hprefix tailTrace_3034716
  have hstable : (prefixWord ++ tailWord_3034716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034716).length < 2 ^ (prefixWord ++ tailWord_3034716).sum := by decide
  have hdescent : baseEnd_3034716 < baseStart_3034716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034717 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3034717 : Nat := 118140960795 + 3034717 * 2 ^ 59
def prefixEnd_3034717 : Nat := 4983230072969 + 3 ^ 40 * 3034717 * 2
def baseEnd_3034717 : Nat := 1558268471370508389481097

theorem tailTrace_3034717 : CollatzResearch.WordTrace tailWord_3034717 prefixEnd_3034717 1558268471370508389481097 := by
  unfold tailWord_3034717
  simp only [CollatzResearch.WordTrace]
  refine ⟨110685222146746072245662405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73790148097830714830441603 110685222146746072245662405)
  ·
    refine ⟨20753479152514888546061701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110685222146746072245662405 20753479152514888546061701)
    ·
      refine ⟨3891277341096541602386569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20753479152514888546061701 3891277341096541602386569)
      ·
        refine ⟨2918458005822406201789927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891277341096541602386569 2918458005822406201789927)
        ·
          refine ⟨4377687008733609302684891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918458005822406201789927 4377687008733609302684891)
          ·
            refine ⟨6566530513100413954027337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377687008733609302684891 6566530513100413954027337)
            ·
              refine ⟨4924897884825310465520503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566530513100413954027337 4924897884825310465520503)
              ·
                refine ⟨7387346827237965698280755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924897884825310465520503 7387346827237965698280755)
                ·
                  refine ⟨11081020240856948547421133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387346827237965698280755 11081020240856948547421133)
                  ·
                    refine ⟨4155382590321355705282925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11081020240856948547421133 4155382590321355705282925)
                    ·
                      refine ⟨1558268471370508389481097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155382590321355705282925 1558268471370508389481097)
                      ·
                        rfl

theorem cell23_3034717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3034717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034717 prefixEnd_3034717 := by exact prefixLift 3034717
  have htrace : WordTrace (prefixWord ++ tailWord_3034717) baseStart_3034717 baseEnd_3034717 := by
    simpa [prefixWord, tailWord_3034717, baseEnd_3034717] using wordTrace_append hprefix tailTrace_3034717
  have hstable : (prefixWord ++ tailWord_3034717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034717).length < 2 ^ (prefixWord ++ tailWord_3034717).sum := by decide
  have hdescent : baseEnd_3034717 < baseStart_3034717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034723 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 4, 2]
def baseStart_3034723 : Nat := 118140960795 + 3034723 * 2 ^ 59
def prefixEnd_3034723 : Nat := 4983230072969 + 3 ^ 40 * 3034723 * 2
def baseEnd_3034723 : Nat := 1558271552254435366006069

theorem tailTrace_3034723 : CollatzResearch.WordTrace tailWord_3034723 prefixEnd_3034723 1558271552254435366006069 := by
  unfold tailWord_3034723
  simp only [CollatzResearch.WordTrace]
  refine ⟨110685440984724335270380823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73790293989816223513587215 110685440984724335270380823)
  ·
    refine ⟨166028161477086502905571235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110685440984724335270380823 166028161477086502905571235)
    ·
      refine ⟨249042242215629754358356853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166028161477086502905571235 249042242215629754358356853)
      ·
        refine ⟨23347710207715289471095955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249042242215629754358356853 23347710207715289471095955)
        ·
          refine ⟨35021565311572934206643933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23347710207715289471095955 35021565311572934206643933)
          ·
            refine ⟨13133086991839850327491475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35021565311572934206643933 13133086991839850327491475)
            ·
              refine ⟨19699630487759775491237213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133086991839850327491475 19699630487759775491237213)
              ·
                refine ⟨7387361432909915809213955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19699630487759775491237213 7387361432909915809213955)
                ·
                  refine ⟨11081042149364873713820933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387361432909915809213955 11081042149364873713820933)
                  ·
                    refine ⟨2077695403005913821341425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11081042149364873713820933 2077695403005913821341425)
                    ·
                      refine ⟨1558271552254435366006069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077695403005913821341425 1558271552254435366006069)
                      ·
                        rfl

theorem cell23_3034723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_3034723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034723 prefixEnd_3034723 := by exact prefixLift 3034723
  have htrace : WordTrace (prefixWord ++ tailWord_3034723) baseStart_3034723 baseEnd_3034723 := by
    simpa [prefixWord, tailWord_3034723, baseEnd_3034723] using wordTrace_append hprefix tailTrace_3034723
  have hstable : (prefixWord ++ tailWord_3034723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034723).length < 2 ^ (prefixWord ++ tailWord_3034723).sum := by decide
  have hdescent : baseEnd_3034723 < baseStart_3034723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034729 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 9]
def baseStart_3034729 : Nat := 118140960795 + 3034729 * 2 ^ 59
def prefixEnd_3034729 : Nat := 4983230072969 + 3 ^ 40 * 3034729 * 2
def baseEnd_3034729 : Nat := 173141625904262482503449

theorem tailTrace_3034729 : CollatzResearch.WordTrace tailWord_3034729 prefixEnd_3034729 173141625904262482503449 := by
  unfold tailWord_3034729
  simp only [CollatzResearch.WordTrace]
  refine ⟨110685659822702598295099241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73790439881801732196732827 110685659822702598295099241)
  ·
    refine ⟨83014244867026948721324431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110685659822702598295099241 83014244867026948721324431)
    ·
      refine ⟨124521367300540423081986647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83014244867026948721324431 124521367300540423081986647)
      ·
        refine ⟨186782050950810634622979971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124521367300540423081986647 186782050950810634622979971)
        ·
          refine ⟨280173076426215951934469957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186782050950810634622979971 280173076426215951934469957)
          ·
            refine ⟨52532451829915490987713117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280173076426215951934469957 52532451829915490987713117)
            ·
              refine ⟨19699669436218309120392419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52532451829915490987713117 19699669436218309120392419)
              ·
                refine ⟨29549504154327463680588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19699669436218309120392419 29549504154327463680588629)
                ·
                  refine ⟨173141625904262482503449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29549504154327463680588629 173141625904262482503449)
                  ·
                    rfl

theorem cell23_3034729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_3034729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034729 prefixEnd_3034729 := by exact prefixLift 3034729
  have htrace : WordTrace (prefixWord ++ tailWord_3034729) baseStart_3034729 baseEnd_3034729 := by
    simpa [prefixWord, tailWord_3034729, baseEnd_3034729] using wordTrace_append hprefix tailTrace_3034729
  have hstable : (prefixWord ++ tailWord_3034729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034729).length < 2 ^ (prefixWord ++ tailWord_3034729).sum := by decide
  have hdescent : baseEnd_3034729 < baseStart_3034729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034776 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_3034776 : Nat := 118140960795 + 3034776 * 2 ^ 59
def prefixEnd_3034776 : Nat := 4983230072969 + 3 ^ 40 * 3034776 * 2
def baseEnd_3034776 : Nat := 519432922243041219547775

theorem tailTrace_3034776 : CollatzResearch.WordTrace tailWord_3034776 prefixEnd_3034776 519432922243041219547775 := by
  unfold tailWord_3034776
  simp only [CollatzResearch.WordTrace]
  refine ⟨55343687026766162661030091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73791582702354883548040121 55343687026766162661030091)
  ·
    refine ⟨83015530540149243991545137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55343687026766162661030091 83015530540149243991545137)
    ·
      refine ⟨62261647905111932993658853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83015530540149243991545137 62261647905111932993658853)
      ·
        refine ⟨11674058982208487436311035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62261647905111932993658853 11674058982208487436311035)
        ·
          refine ⟨17511088473312731154466553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674058982208487436311035 17511088473312731154466553)
          ·
            refine ⟨13133316354984548365849915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17511088473312731154466553 13133316354984548365849915)
            ·
              refine ⟨19699974532476822548774873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133316354984548365849915 19699974532476822548774873)
              ·
                refine ⟨14774980899357616911581155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19699974532476822548774873 14774980899357616911581155)
                ·
                  refine ⟨22162471349036425367371733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14774980899357616911581155 22162471349036425367371733)
                  ·
                    refine ⟨519432922243041219547775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22162471349036425367371733 519432922243041219547775)
                    ·
                      rfl

theorem cell23_3034776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_3034776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034776 prefixEnd_3034776 := by exact prefixLift 3034776
  have htrace : WordTrace (prefixWord ++ tailWord_3034776) baseStart_3034776 baseEnd_3034776 := by
    simpa [prefixWord, tailWord_3034776, baseEnd_3034776] using wordTrace_append hprefix tailTrace_3034776
  have hstable : (prefixWord ++ tailWord_3034776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034776).length < 2 ^ (prefixWord ++ tailWord_3034776).sum := by decide
  have hdescent : baseEnd_3034776 < baseStart_3034776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034779 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_3034779 : Nat := 118140960795 + 3034779 * 2 ^ 59
def prefixEnd_3034779 : Nat := 4983230072969 + 3 ^ 40 * 3034779 * 2
def baseEnd_3034779 : Nat := 1558300307171087146905811

theorem tailTrace_3034779 : CollatzResearch.WordTrace tailWord_3034779 prefixEnd_3034779 1558300307171087146905811 := by
  unfold tailWord_3034779
  simp only [CollatzResearch.WordTrace]
  refine ⟨110687483472521456834419391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73791655648347637889612927 110687483472521456834419391)
  ·
    refine ⟨166031225208782185251629087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110687483472521456834419391 166031225208782185251629087)
    ·
      refine ⟨249046837813173277877443631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166031225208782185251629087 249046837813173277877443631)
      ·
        refine ⟨373570256719759916816165447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249046837813173277877443631 373570256719759916816165447)
        ·
          refine ⟨560355385079639875224248171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373570256719759916816165447 560355385079639875224248171)
          ·
            refine ⟨840533077619459812836372257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560355385079639875224248171 840533077619459812836372257)
            ·
              refine ⟨630399808214594859627279193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840533077619459812836372257 630399808214594859627279193)
              ·
                refine ⟨472799856160946144720459395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630399808214594859627279193 472799856160946144720459395)
                ·
                  refine ⟨709199784241419217080689093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472799856160946144720459395 709199784241419217080689093)
                  ·
                    refine ⟨132974959545266103202629205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709199784241419217080689093 132974959545266103202629205)
                    ·
                      refine ⟨1558300307171087146905811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132974959545266103202629205 1558300307171087146905811)
                      ·
                        rfl

theorem cell23_3034779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_3034779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034779 prefixEnd_3034779 := by exact prefixLift 3034779
  have htrace : WordTrace (prefixWord ++ tailWord_3034779) baseStart_3034779 baseEnd_3034779 := by
    simpa [prefixWord, tailWord_3034779, baseEnd_3034779] using wordTrace_append hprefix tailTrace_3034779
  have hstable : (prefixWord ++ tailWord_3034779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034779).length < 2 ^ (prefixWord ++ tailWord_3034779).sum := by decide
  have hdescent : baseEnd_3034779 < baseStart_3034779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034796 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3034796 : Nat := 118140960795 + 3034796 * 2 ^ 59
def prefixEnd_3034796 : Nat := 4983230072969 + 3 ^ 40 * 3034796 * 2
def baseEnd_3034796 : Nat := 1558309036342213580393233

theorem tailTrace_3034796 : CollatzResearch.WordTrace tailWord_3034796 prefixEnd_3034796 1558309036342213580393233 := by
  unfold tailWord_3034796
  simp only [CollatzResearch.WordTrace]
  refine ⟨55344051756729934368894121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73792069008973245825192161 55344051756729934368894121)
  ·
    refine ⟨41508038817547450776670591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55344051756729934368894121 41508038817547450776670591)
    ·
      refine ⟨62262058226321176165005887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41508038817547450776670591 62262058226321176165005887)
      ·
        refine ⟨93393087339481764247508831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62262058226321176165005887 93393087339481764247508831)
        ·
          refine ⟨140089631009222646371263247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93393087339481764247508831 140089631009222646371263247)
          ·
            refine ⟨210134446513833969556894871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140089631009222646371263247 210134446513833969556894871)
            ·
              refine ⟨315201669770750954335342307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210134446513833969556894871 315201669770750954335342307)
              ·
                refine ⟨472802504656126431503013461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315201669770750954335342307 472802504656126431503013461)
                ·
                  refine ⟨5540654351438981619175939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 472802504656126431503013461 5540654351438981619175939)
                  ·
                    refine ⟨8310981527158472428763909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540654351438981619175939 8310981527158472428763909)
                    ·
                      refine ⟨1558309036342213580393233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8310981527158472428763909 1558309036342213580393233)
                      ·
                        rfl

theorem cell23_3034796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3034796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034796 prefixEnd_3034796 := by exact prefixLift 3034796
  have htrace : WordTrace (prefixWord ++ tailWord_3034796) baseStart_3034796 baseEnd_3034796 := by
    simpa [prefixWord, tailWord_3034796, baseEnd_3034796] using wordTrace_append hprefix tailTrace_3034796
  have hstable : (prefixWord ++ tailWord_3034796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034796).length < 2 ^ (prefixWord ++ tailWord_3034796).sum := by decide
  have hdescent : baseEnd_3034796 < baseStart_3034796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034813 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3034813 : Nat := 118140960795 + 3034813 * 2 ^ 59
def prefixEnd_3034813 : Nat := 4983230072969 + 3 ^ 40 * 3034813 * 2
def baseEnd_3034813 : Nat := 1558317765513340013880655

theorem tailTrace_3034813 : CollatzResearch.WordTrace tailWord_3034813 prefixEnd_3034813 1558317765513340013880655 := by
  unfold tailWord_3034813
  simp only [CollatzResearch.WordTrace]
  refine ⟨110688723554398280641157093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73792482369598853760771395 110688723554398280641157093)
  ·
    refine ⟨20754135666449677620216955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110688723554398280641157093 20754135666449677620216955)
    ·
      refine ⟨31131203499674516430325433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20754135666449677620216955 31131203499674516430325433)
      ·
        refine ⟨23348402624755887322744075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31131203499674516430325433 23348402624755887322744075)
        ·
          refine ⟨35022603937133830984116113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23348402624755887322744075 35022603937133830984116113)
          ·
            refine ⟨26266952952850373238087085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35022603937133830984116113 26266952952850373238087085)
            ·
              refine ⟨9850107357318889964282657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26266952952850373238087085 9850107357318889964282657)
              ·
                refine ⟨7387580517989167473211993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850107357318889964282657 7387580517989167473211993)
                ·
                  refine ⟨5540685388491875604908995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7387580517989167473211993 5540685388491875604908995)
                  ·
                    refine ⟨8311028082737813407363493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540685388491875604908995 8311028082737813407363493)
                    ·
                      refine ⟨1558317765513340013880655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8311028082737813407363493 1558317765513340013880655)
                      ·
                        rfl

theorem cell23_3034813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3034813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034813 prefixEnd_3034813 := by exact prefixLift 3034813
  have htrace : WordTrace (prefixWord ++ tailWord_3034813) baseStart_3034813 baseEnd_3034813 := by
    simpa [prefixWord, tailWord_3034813, baseEnd_3034813] using wordTrace_append hprefix tailTrace_3034813
  have hstable : (prefixWord ++ tailWord_3034813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034813).length < 2 ^ (prefixWord ++ tailWord_3034813).sum := by decide
  have hdescent : baseEnd_3034813 < baseStart_3034813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034870 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_3034870 : Nat := 118140960795 + 3034870 * 2 ^ 59
def prefixEnd_3034870 : Nat := 4983230072969 + 3 ^ 40 * 3034870 * 2
def baseEnd_3034870 : Nat := 173149670434516254540877

theorem tailTrace_3034870 : CollatzResearch.WordTrace tailWord_3034870 prefixEnd_3034870 173149670434516254540877 := by
  unfold tailWord_3034870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6918175157199486210998879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73793868343461186250654709 6918175157199486210998879)
  ·
    refine ⟨10377262735799229316498319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6918175157199486210998879 10377262735799229316498319)
    ·
      refine ⟨15565894103698843974747479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377262735799229316498319 15565894103698843974747479)
      ·
        refine ⟨23348841155548265962121219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15565894103698843974747479 23348841155548265962121219)
        ·
          refine ⟨35023261733322398943181829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23348841155548265962121219 35023261733322398943181829)
          ·
            refine ⟨6566861574997949801846593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35023261733322398943181829 6566861574997949801846593)
            ·
              refine ⟨4925146181248462351384945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566861574997949801846593 4925146181248462351384945)
              ·
                refine ⟨3693859635936346763538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925146181248462351384945 3693859635936346763538709)
                ·
                  refine ⟨173149670434516254540877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3693859635936346763538709 173149670434516254540877)
                  ·
                    rfl

theorem cell23_3034870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_3034870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034870 prefixEnd_3034870 := by exact prefixLift 3034870
  have htrace : WordTrace (prefixWord ++ tailWord_3034870) baseStart_3034870 baseEnd_3034870 := by
    simpa [prefixWord, tailWord_3034870, baseEnd_3034870] using wordTrace_append hprefix tailTrace_3034870
  have hstable : (prefixWord ++ tailWord_3034870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034870).length < 2 ^ (prefixWord ++ tailWord_3034870).sum := by decide
  have hdescent : baseEnd_3034870 < baseStart_3034870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034873 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 5, 2]
def baseStart_3034873 : Nat := 118140960795 + 3034873 * 2 ^ 59
def prefixEnd_3034873 : Nat := 4983230072969 + 3 ^ 40 * 3034873 * 2
def baseEnd_3034873 : Nat := 1558348574352609779130379

theorem tailTrace_3034873 : CollatzResearch.WordTrace tailWord_3034873 prefixEnd_3034873 1558348574352609779130379 := by
  unfold tailWord_3034873
  simp only [CollatzResearch.WordTrace]
  refine ⟨110690911934180910888341273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73793941289453940592227515 110690911934180910888341273)
  ·
    refine ⟨83018183950635683166255955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110690911934180910888341273 83018183950635683166255955)
    ·
      refine ⟨124527275925953524749383933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83018183950635683166255955 124527275925953524749383933)
      ·
        refine ⟨46697728472232571781018975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124527275925953524749383933 46697728472232571781018975)
        ·
          refine ⟨70046592708348857671528463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46697728472232571781018975 70046592708348857671528463)
          ·
            refine ⟨105069889062523286507292695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70046592708348857671528463 105069889062523286507292695)
            ·
              refine ⟨157604833593784929760939043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105069889062523286507292695 157604833593784929760939043)
              ·
                refine ⟨236407250390677394641408565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157604833593784929760939043 236407250390677394641408565)
                ·
                  refine ⟨22163179724126005747632053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236407250390677394641408565 22163179724126005747632053)
                  ·
                    refine ⟨2077798099136813038840505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22163179724126005747632053 2077798099136813038840505)
                    ·
                      refine ⟨1558348574352609779130379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077798099136813038840505 1558348574352609779130379)
                      ·
                        rfl

theorem cell23_3034873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_3034873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034873 prefixEnd_3034873 := by exact prefixLift 3034873
  have htrace : WordTrace (prefixWord ++ tailWord_3034873) baseStart_3034873 baseEnd_3034873 := by
    simpa [prefixWord, tailWord_3034873, baseEnd_3034873] using wordTrace_append hprefix tailTrace_3034873
  have hstable : (prefixWord ++ tailWord_3034873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034873).length < 2 ^ (prefixWord ++ tailWord_3034873).sum := by decide
  have hdescent : baseEnd_3034873 < baseStart_3034873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034913 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3034913 : Nat := 118140960795 + 3034913 * 2 ^ 59
def prefixEnd_3034913 : Nat := 4983230072969 + 3 ^ 40 * 3034913 * 2
def baseEnd_3034913 : Nat := 519456371192929874210065

theorem tailTrace_3034913 : CollatzResearch.WordTrace tailWord_3034913 prefixEnd_3034913 519456371192929874210065 := by
  unfold tailWord_3034913
  simp only [CollatzResearch.WordTrace]
  refine ⟨110692370854035997719797393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73794913902690665146531595 110692370854035997719797393)
  ·
    refine ⟨83019278140526998289848045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110692370854035997719797393 83019278140526998289848045)
    ·
      refine ⟨31132229302697624358693017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83019278140526998289848045 31132229302697624358693017)
      ·
        refine ⟨23349171977023218269019763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31132229302697624358693017 23349171977023218269019763)
        ·
          refine ⟨35023757965534827403529645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23349171977023218269019763 35023757965534827403529645)
          ·
            refine ⟨13133909237075560276323617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35023757965534827403529645 13133909237075560276323617)
            ·
              refine ⟨9850431927806670207242713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13133909237075560276323617 9850431927806670207242713)
              ·
                refine ⟨7387823945855002655432035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850431927806670207242713 7387823945855002655432035)
                ·
                  refine ⟨11081735918782503983148053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387823945855002655432035 11081735918782503983148053)
                  ·
                    refine ⟨519456371192929874210065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11081735918782503983148053 519456371192929874210065)
                    ·
                      rfl

theorem cell23_3034913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3034913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034913 prefixEnd_3034913 := by exact prefixLift 3034913
  have htrace : WordTrace (prefixWord ++ tailWord_3034913) baseStart_3034913 baseEnd_3034913 := by
    simpa [prefixWord, tailWord_3034913, baseEnd_3034913] using wordTrace_append hprefix tailTrace_3034913
  have hstable : (prefixWord ++ tailWord_3034913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034913).length < 2 ^ (prefixWord ++ tailWord_3034913).sum := by decide
  have hdescent : baseEnd_3034913 < baseStart_3034913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034914 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3034914 : Nat := 118140960795 + 3034914 * 2 ^ 59
def prefixEnd_3034914 : Nat := 4983230072969 + 3 ^ 40 * 3034914 * 2
def baseEnd_3034914 : Nat := 1558369627059444118717691

theorem tailTrace_3034914 : CollatzResearch.WordTrace tailWord_3034914 prefixEnd_3034914 1558369627059444118717691 := by
  unfold tailWord_3034914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673101831758093722645949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73794938218021583260389197 27673101831758093722645949)
  ·
    refine ⟨10377413186909285145992231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27673101831758093722645949 10377413186909285145992231)
    ·
      refine ⟨15566119780363927718988347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377413186909285145992231 15566119780363927718988347)
      ·
        refine ⟨23349179670545891578482521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15566119780363927718988347 23349179670545891578482521)
        ·
          refine ⟨17511884752909418683861891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23349179670545891578482521 17511884752909418683861891)
          ·
            refine ⟨26267827129364128025792837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17511884752909418683861891 26267827129364128025792837)
            ·
              refine ⟨4925217586755774004836157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26267827129364128025792837 4925217586755774004836157)
              ·
                refine ⟨1846956595033415251813559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4925217586755774004836157 1846956595033415251813559)
                ·
                  refine ⟨2770434892550122877720339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846956595033415251813559 2770434892550122877720339)
                  ·
                    refine ⟨4155652338825184316580509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770434892550122877720339 4155652338825184316580509)
                    ·
                      refine ⟨1558369627059444118717691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155652338825184316580509 1558369627059444118717691)
                      ·
                        rfl

theorem cell23_3034914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3034914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034914 prefixEnd_3034914 := by exact prefixLift 3034914
  have htrace : WordTrace (prefixWord ++ tailWord_3034914) baseStart_3034914 baseEnd_3034914 := by
    simpa [prefixWord, tailWord_3034914, baseEnd_3034914] using wordTrace_append hprefix tailTrace_3034914
  have hstable : (prefixWord ++ tailWord_3034914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034914).length < 2 ^ (prefixWord ++ tailWord_3034914).sum := by decide
  have hdescent : baseEnd_3034914 < baseStart_3034914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034917 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_3034917 : Nat := 118140960795 + 3034917 * 2 ^ 59
def prefixEnd_3034917 : Nat := 4983230072969 + 3 ^ 40 * 3034917 * 2
def baseEnd_3034917 : Nat := 519457055833802535660059

theorem tailTrace_3034917 : CollatzResearch.WordTrace tailWord_3034917 prefixEnd_3034917 519457055833802535660059 := by
  unfold tailWord_3034917
  simp only [CollatzResearch.WordTrace]
  refine ⟨110692516746021506402943005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73795011164014337601962003 110692516746021506402943005)
  ·
    refine ⟨41509693779758064901103627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110692516746021506402943005 41509693779758064901103627)
    ·
      refine ⟨62264540669637097351655441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41509693779758064901103627 62264540669637097351655441)
      ·
        refine ⟨46698405502227823013741581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62264540669637097351655441 46698405502227823013741581)
        ·
          refine ⟨17511902063335433630153093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46698405502227823013741581 17511902063335433630153093)
          ·
            refine ⟨3283481636875393805653705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17511902063335433630153093 3283481636875393805653705)
            ·
              refine ⟨2462611227656545354240279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283481636875393805653705 2462611227656545354240279)
              ·
                refine ⟨3693916841484818031360419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462611227656545354240279 3693916841484818031360419)
                ·
                  refine ⟨5540875262227227047040629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693916841484818031360419 5540875262227227047040629)
                  ·
                    refine ⟨519457055833802535660059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5540875262227227047040629 519457055833802535660059)
                    ·
                      rfl

theorem cell23_3034917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_3034917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034917 prefixEnd_3034917 := by exact prefixLift 3034917
  have htrace : WordTrace (prefixWord ++ tailWord_3034917) baseStart_3034917 baseEnd_3034917 := by
    simpa [prefixWord, tailWord_3034917, baseEnd_3034917] using wordTrace_append hprefix tailTrace_3034917
  have hstable : (prefixWord ++ tailWord_3034917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034917).length < 2 ^ (prefixWord ++ tailWord_3034917).sum := by decide
  have hdescent : baseEnd_3034917 < baseStart_3034917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034930 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3034930 : Nat := 118140960795 + 3034930 * 2 ^ 59
def prefixEnd_3034930 : Nat := 4983230072969 + 3 ^ 40 * 3034930 * 2
def baseEnd_3034930 : Nat := 519459280916638685372539

theorem tailTrace_3034930 : CollatzResearch.WordTrace tailWord_3034930 prefixEnd_3034930 519459280916638685372539 := by
  unfold tailWord_3034930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673247723743602405791561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73795327263316273082110829 27673247723743602405791561)
  ·
    refine ⟨20754935792807701804343671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27673247723743602405791561 20754935792807701804343671)
    ·
      refine ⟨31132403689211552706515507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20754935792807701804343671 31132403689211552706515507)
      ·
        refine ⟨46698605533817329059773261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31132403689211552706515507 46698605533817329059773261)
        ·
          refine ⟨17511977075181498397414973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46698605533817329059773261 17511977075181498397414973)
          ·
            refine ⟨6566991403193061899030615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17511977075181498397414973 6566991403193061899030615)
            ·
              refine ⟨9850487104789592848545923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566991403193061899030615 9850487104789592848545923)
              ·
                refine ⟨14775730657184389272818885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9850487104789592848545923 14775730657184389272818885)
                ·
                  refine ⟨2770449498222072988653541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14775730657184389272818885 2770449498222072988653541)
                  ·
                    refine ⟨519459280916638685372539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770449498222072988653541 519459280916638685372539)
                    ·
                      rfl

theorem cell23_3034930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3034930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034930 prefixEnd_3034930 := by exact prefixLift 3034930
  have htrace : WordTrace (prefixWord ++ tailWord_3034930) baseStart_3034930 baseEnd_3034930 := by
    simpa [prefixWord, tailWord_3034930, baseEnd_3034930] using wordTrace_append hprefix tailTrace_3034930
  have hstable : (prefixWord ++ tailWord_3034930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034930).length < 2 ^ (prefixWord ++ tailWord_3034930).sum := by decide
  have hdescent : baseEnd_3034930 < baseStart_3034930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034947 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 2, 4]
def baseStart_3034947 : Nat := 118140960795 + 3034947 * 2 ^ 59
def prefixEnd_3034947 : Nat := 4983230072969 + 3 ^ 40 * 3034947 * 2
def baseEnd_3034947 : Nat := 519462190640347496535013

theorem tailTrace_3034947 : CollatzResearch.WordTrace tailWord_3034947 prefixEnd_3034947 519462190640347496535013 := by
  unfold tailWord_3034947
  simp only [CollatzResearch.WordTrace]
  refine ⟨110693610935912821526535095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73795740623941881017690063 110693610935912821526535095)
  ·
    refine ⟨166040416403869232289802643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110693610935912821526535095 166040416403869232289802643)
    ·
      refine ⟨249060624605803848434703965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166040416403869232289802643 249060624605803848434703965)
      ·
        refine ⟨93397734227176443163013987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249060624605803848434703965 93397734227176443163013987)
        ·
          refine ⟨140096601340764664744520981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93397734227176443163013987 140096601340764664744520981)
          ·
            refine ⟨6567028187848343659899421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140096601340764664744520981 6567028187848343659899421)
            ·
              refine ⟨2462635570443128872462283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6567028187848343659899421 2462635570443128872462283)
              ·
                refine ⟨3693953355664693308693425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462635570443128872462283 3693953355664693308693425)
                ·
                  refine ⟨2770465016748519981520069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3693953355664693308693425 2770465016748519981520069)
                  ·
                    refine ⟨519462190640347496535013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770465016748519981520069 519462190640347496535013)
                    ·
                      rfl

theorem cell23_3034947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 2, 4].length) (baseStart_3034947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034947 prefixEnd_3034947 := by exact prefixLift 3034947
  have htrace : WordTrace (prefixWord ++ tailWord_3034947) baseStart_3034947 baseEnd_3034947 := by
    simpa [prefixWord, tailWord_3034947, baseEnd_3034947] using wordTrace_append hprefix tailTrace_3034947
  have hstable : (prefixWord ++ tailWord_3034947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034947).length < 2 ^ (prefixWord ++ tailWord_3034947).sum := by decide
  have hdescent : baseEnd_3034947 < baseStart_3034947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034970 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3034970 : Nat := 118140960795 + 3034970 * 2 ^ 59
def prefixEnd_3034970 : Nat := 4983230072969 + 3 ^ 40 * 3034970 * 2
def baseEnd_3034970 : Nat := 1558398381976095899617433

theorem tailTrace_3034970 : CollatzResearch.WordTrace tailWord_3034970 prefixEnd_3034970 1558398381976095899617433 := by
  unfold tailWord_3034970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673612453707374113655591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73796299876552997636414909 27673612453707374113655591)
  ·
    refine ⟨41510418680561061170483387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673612453707374113655591 41510418680561061170483387)
    ·
      refine ⟨62265628020841591755725081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510418680561061170483387 62265628020841591755725081)
      ·
        refine ⟨46699221015631193816793811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62265628020841591755725081 46699221015631193816793811)
        ·
          refine ⟨70048831523446790725190717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46699221015631193816793811 70048831523446790725190717)
          ·
            refine ⟨26268311821292546521946519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70048831523446790725190717 26268311821292546521946519)
            ·
              refine ⟨39402467731938819782919779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26268311821292546521946519 39402467731938819782919779)
              ·
                refine ⟨59103701597908229674379669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39402467731938819782919779 59103701597908229674379669)
                ·
                  refine ⟨2770486012401948265986547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59103701597908229674379669 2770486012401948265986547)
                  ·
                    refine ⟨4155729018602922398979821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770486012401948265986547 4155729018602922398979821)
                    ·
                      refine ⟨1558398381976095899617433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155729018602922398979821 1558398381976095899617433)
                      ·
                        rfl

theorem cell23_3034970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3034970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034970 prefixEnd_3034970 := by exact prefixLift 3034970
  have htrace : WordTrace (prefixWord ++ tailWord_3034970) baseStart_3034970 baseEnd_3034970 := by
    simpa [prefixWord, tailWord_3034970, baseEnd_3034970] using wordTrace_append hprefix tailTrace_3034970
  have hstable : (prefixWord ++ tailWord_3034970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034970).length < 2 ^ (prefixWord ++ tailWord_3034970).sum := by decide
  have hdescent : baseEnd_3034970 < baseStart_3034970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034983 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3034983 : Nat := 118140960795 + 3034983 * 2 ^ 59
def prefixEnd_3034983 : Nat := 4983230072969 + 3 ^ 40 * 3034983 * 2
def baseEnd_3034983 : Nat := 1558405057224604348754873

theorem tailTrace_3034983 : CollatzResearch.WordTrace tailWord_3034983 prefixEnd_3034983 1558405057224604348754873 := by
  unfold tailWord_3034983
  simp only [CollatzResearch.WordTrace]
  refine ⟨110694923963782399674845603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73796615975854933116563735 110694923963782399674845603)
  ·
    refine ⟨166042385945673599512268405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110694923963782399674845603 166042385945673599512268405)
    ·
      refine ⟨15566473682406899954275163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166042385945673599512268405 15566473682406899954275163)
      ·
        refine ⟨23349710523610349931412745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15566473682406899954275163 23349710523610349931412745)
        ·
          refine ⟨17512282892707762448559559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23349710523610349931412745 17512282892707762448559559)
          ·
            refine ⟨26268424339061643672839339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512282892707762448559559 26268424339061643672839339)
            ·
              refine ⟨39402636508592465509259009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26268424339061643672839339 39402636508592465509259009)
              ·
                refine ⟨29551977381444349131944257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39402636508592465509259009 29551977381444349131944257)
                ·
                  refine ⟨22163983036083261848958193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29551977381444349131944257 22163983036083261848958193)
                  ·
                    refine ⟨16622987277062446386718645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22163983036083261848958193 16622987277062446386718645)
                    ·
                      refine ⟨1558405057224604348754873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16622987277062446386718645 1558405057224604348754873)
                      ·
                        rfl

theorem cell23_3034983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3034983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034983 prefixEnd_3034983 := by exact prefixLift 3034983
  have htrace : WordTrace (prefixWord ++ tailWord_3034983) baseStart_3034983 baseEnd_3034983 := by
    simpa [prefixWord, tailWord_3034983, baseEnd_3034983] using wordTrace_append hprefix tailTrace_3034983
  have hstable : (prefixWord ++ tailWord_3034983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034983).length < 2 ^ (prefixWord ++ tailWord_3034983).sum := by decide
  have hdescent : baseEnd_3034983 < baseStart_3034983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034993 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_3034993 : Nat := 118140960795 + 3034993 * 2 ^ 59
def prefixEnd_3034993 : Nat := 4983230072969 + 3 ^ 40 * 3034993 * 2
def baseEnd_3034993 : Nat := 1558410192031149309629827

theorem tailTrace_3034993 : CollatzResearch.WordTrace tailWord_3034993 prefixEnd_3034993 1558410192031149309629827 := by
  unfold tailWord_3034993
  simp only [CollatzResearch.WordTrace]
  refine ⟨110695288693746171382709633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73796859129164114255139755 110695288693746171382709633)
  ·
    refine ⟨83021466520309628537032225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110695288693746171382709633 83021466520309628537032225)
    ·
      refine ⟨62266099890232221402774169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83021466520309628537032225 62266099890232221402774169)
      ·
        refine ⟨46699574917674166052080627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62266099890232221402774169 46699574917674166052080627)
        ·
          refine ⟨70049362376511249078120941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46699574917674166052080627 70049362376511249078120941)
          ·
            refine ⟨26268510891191718404295353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70049362376511249078120941 26268510891191718404295353)
            ·
              refine ⟨19701383168393788803221515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26268510891191718404295353 19701383168393788803221515)
              ·
                refine ⟨29552074752590683204832273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19701383168393788803221515 29552074752590683204832273)
                ·
                  refine ⟨22164056064443012403624205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29552074752590683204832273 22164056064443012403624205)
                  ·
                    refine ⟨8311521024166129651359077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22164056064443012403624205 8311521024166129651359077)
                    ·
                      refine ⟨1558410192031149309629827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8311521024166129651359077 1558410192031149309629827)
                      ·
                        rfl

theorem cell23_3034993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_3034993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034993 prefixEnd_3034993 := by exact prefixLift 3034993
  have htrace : WordTrace (prefixWord ++ tailWord_3034993) baseStart_3034993 baseEnd_3034993 := by
    simpa [prefixWord, tailWord_3034993, baseEnd_3034993] using wordTrace_append hprefix tailTrace_3034993
  have hstable : (prefixWord ++ tailWord_3034993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034993).length < 2 ^ (prefixWord ++ tailWord_3034993).sum := by decide
  have hdescent : baseEnd_3034993 < baseStart_3034993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034997 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3034997 : Nat := 118140960795 + 3034997 * 2 ^ 59
def prefixEnd_3034997 : Nat := 4983230072969 + 3 ^ 40 * 3034997 * 2
def baseEnd_3034997 : Nat := 1558412245953767293979809

theorem tailTrace_3034997 : CollatzResearch.WordTrace tailWord_3034997 prefixEnd_3034997 1558412245953767293979809 := by
  unfold tailWord_3034997
  simp only [CollatzResearch.WordTrace]
  refine ⟨110695434585731680065855245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73796956390487786710570163 110695434585731680065855245)
  ·
    refine ⟨41510787969649380024695717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110695434585731680065855245 41510787969649380024695717)
    ·
      refine ⟨7783272744309258754630447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41510787969649380024695717 7783272744309258754630447)
      ·
        refine ⟨11674909116463888131945671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7783272744309258754630447 11674909116463888131945671)
        ·
          refine ⟨17512363674695832197918507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674909116463888131945671 17512363674695832197918507)
          ·
            refine ⟨26268545512043748296877761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512363674695832197918507 26268545512043748296877761)
            ·
              refine ⟨19701409134032811222658321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26268545512043748296877761 19701409134032811222658321)
              ·
                refine ⟨14776056850524608416993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701409134032811222658321 14776056850524608416993741)
                ·
                  refine ⟨5541021318946728156372653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14776056850524608416993741 5541021318946728156372653)
                  ·
                    refine ⟨2077882994605023058639745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5541021318946728156372653 2077882994605023058639745)
                    ·
                      refine ⟨1558412245953767293979809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077882994605023058639745 1558412245953767293979809)
                      ·
                        rfl

theorem cell23_3034997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3034997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034997 prefixEnd_3034997 := by exact prefixLift 3034997
  have htrace : WordTrace (prefixWord ++ tailWord_3034997) baseStart_3034997 baseEnd_3034997 := by
    simpa [prefixWord, tailWord_3034997, baseEnd_3034997] using wordTrace_append hprefix tailTrace_3034997
  have hstable : (prefixWord ++ tailWord_3034997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034997).length < 2 ^ (prefixWord ++ tailWord_3034997).sum := by decide
  have hdescent : baseEnd_3034997 < baseStart_3034997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3034998 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_3034998 : Nat := 118140960795 + 3034998 * 2 ^ 59
def prefixEnd_3034998 : Nat := 4983230072969 + 3 ^ 40 * 3034998 * 2
def baseEnd_3034998 : Nat := 519470919811473930022435

theorem tailTrace_3034998 : CollatzResearch.WordTrace tailWord_3034998 prefixEnd_3034998 519470919811473930022435 := by
  unfold tailWord_3034998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6918466941170503577290103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73796980705818704824427765 6918466941170503577290103)
  ·
    refine ⟨10377700411755755365935155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6918466941170503577290103 10377700411755755365935155)
    ·
      refine ⟨15566550617633633048902733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377700411755755365935155 15566550617633633048902733)
      ·
        refine ⟨5837456481612612393338525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15566550617633633048902733 5837456481612612393338525)
        ·
          refine ⟨2189046180604729647501947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5837456481612612393338525 2189046180604729647501947)
          ·
            refine ⟨3283569270907094471252921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189046180604729647501947 3283569270907094471252921)
            ·
              refine ⟨2462676953180320853439691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283569270907094471252921 2462676953180320853439691)
              ·
                refine ⟨3694015429770481280159537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462676953180320853439691 3694015429770481280159537)
                ·
                  refine ⟨2770511572327860960119653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694015429770481280159537 2770511572327860960119653)
                  ·
                    refine ⟨519470919811473930022435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2770511572327860960119653 519470919811473930022435)
                    ·
                      rfl

theorem cell23_3034998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_3034998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3034998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3034998 prefixEnd_3034998 := by exact prefixLift 3034998
  have htrace : WordTrace (prefixWord ++ tailWord_3034998) baseStart_3034998 baseEnd_3034998 := by
    simpa [prefixWord, tailWord_3034998, baseEnd_3034998] using wordTrace_append hprefix tailTrace_3034998
  have hstable : (prefixWord ++ tailWord_3034998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3034998).length < 2 ^ (prefixWord ++ tailWord_3034998).sum := by decide
  have hdescent : baseEnd_3034998 < baseStart_3034998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3034998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035013 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_3035013 : Nat := 118140960795 + 3035013 * 2 ^ 59
def prefixEnd_3035013 : Nat := 4983230072969 + 3 ^ 40 * 3035013 * 2
def baseEnd_3035013 : Nat := 1558420461644239231379735

theorem tailTrace_3035013 : CollatzResearch.WordTrace tailWord_3035013 prefixEnd_3035013 1558420461644239231379735 := by
  unfold tailWord_3035013
  simp only [CollatzResearch.WordTrace]
  refine ⟨110696018153673714798437693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73797345435782476532291795 110696018153673714798437693)
  ·
    refine ⟨41511006807627643049414135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110696018153673714798437693 41511006807627643049414135)
    ·
      refine ⟨62266510211441464574121203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41511006807627643049414135 62266510211441464574121203)
      ·
        refine ⟨93399765317162196861181805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62266510211441464574121203 93399765317162196861181805)
        ·
          refine ⟨35024911993935823822943177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93399765317162196861181805 35024911993935823822943177)
          ·
            refine ⟨26268683995451867867207383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35024911993935823822943177 26268683995451867867207383)
            ·
              refine ⟨39403025993177801800811075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26268683995451867867207383 39403025993177801800811075)
              ·
                refine ⟨59104538989766702701216613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39403025993177801800811075 59104538989766702701216613)
                ·
                  refine ⟨11082101060581256756478115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59104538989766702701216613 11082101060581256756478115)
                  ·
                    refine ⟨16623151590871885134717173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11082101060581256756478115 16623151590871885134717173)
                    ·
                      refine ⟨1558420461644239231379735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16623151590871885134717173 1558420461644239231379735)
                      ·
                        rfl

theorem cell23_3035013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_3035013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035013 prefixEnd_3035013 := by exact prefixLift 3035013
  have htrace : WordTrace (prefixWord ++ tailWord_3035013) baseStart_3035013 baseEnd_3035013 := by
    simpa [prefixWord, tailWord_3035013, baseEnd_3035013] using wordTrace_append hprefix tailTrace_3035013
  have hstable : (prefixWord ++ tailWord_3035013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035013).length < 2 ^ (prefixWord ++ tailWord_3035013).sum := by decide
  have hdescent : baseEnd_3035013 < baseStart_3035013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035038 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3035038 : Nat := 118140960795 + 3035038 * 2 ^ 59
def prefixEnd_3035038 : Nat := 4983230072969 + 3 ^ 40 * 3035038 * 2
def baseEnd_3035038 : Nat := 1558433298660601633567121

theorem tailTrace_3035038 : CollatzResearch.WordTrace tailWord_3035038 prefixEnd_3035038 1558433298660601633567121 := by
  unfold tailWord_3035038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837116247322893008512221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73797953319055429378731845 13837116247322893008512221)
  ·
    refine ⟨5188918592746084878192083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13837116247322893008512221 5188918592746084878192083)
    ·
      refine ⟨7783377889119127317288125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5188918592746084878192083 7783377889119127317288125)
      ·
        refine ⟨2918766708419672743983047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7783377889119127317288125 2918766708419672743983047)
        ·
          refine ⟨4378150062629509115974571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918766708419672743983047 4378150062629509115974571)
          ·
            refine ⟨6567225093944263673961857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378150062629509115974571 6567225093944263673961857)
            ·
              refine ⟨4925418820458197755471393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567225093944263673961857 4925418820458197755471393)
              ·
                refine ⟨3694064115343648316603545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925418820458197755471393 3694064115343648316603545)
                ·
                  refine ⟨2770548086507736237452659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694064115343648316603545 2770548086507736237452659)
                  ·
                    refine ⟨4155822129761604356178989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770548086507736237452659 4155822129761604356178989)
                    ·
                      refine ⟨1558433298660601633567121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155822129761604356178989 1558433298660601633567121)
                      ·
                        rfl

theorem cell23_3035038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3035038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035038 prefixEnd_3035038 := by exact prefixLift 3035038
  have htrace : WordTrace (prefixWord ++ tailWord_3035038) baseStart_3035038 baseEnd_3035038 := by
    simpa [prefixWord, tailWord_3035038, baseEnd_3035038] using wordTrace_append hprefix tailTrace_3035038
  have hstable : (prefixWord ++ tailWord_3035038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035038).length < 2 ^ (prefixWord ++ tailWord_3035038).sum := by decide
  have hdescent : baseEnd_3035038 < baseStart_3035038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035044 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_3035044 : Nat := 118140960795 + 3035044 * 2 ^ 59
def prefixEnd_3035044 : Nat := 4983230072969 + 3 ^ 40 * 3035044 * 2
def baseEnd_3035044 : Nat := 1558436379544528610092093

theorem tailTrace_3035044 : CollatzResearch.WordTrace tailWord_3035044 prefixEnd_3035044 1558436379544528610092093 := by
  unfold tailWord_3035044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348574408280703546408093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73798099211040938061877457 55348574408280703546408093)
  ·
    refine ⟨20755715403105263829903035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55348574408280703546408093 20755715403105263829903035)
    ·
      refine ⟨31133573104657895744854553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20755715403105263829903035 31133573104657895744854553)
      ·
        refine ⟨23350179828493421808640915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31133573104657895744854553 23350179828493421808640915)
        ·
          refine ⟨35025269742740132712961373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23350179828493421808640915 35025269742740132712961373)
          ·
            refine ⟨13134476153527549767360515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35025269742740132712961373 13134476153527549767360515)
            ·
              refine ⟨19701714230291324651040773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134476153527549767360515 19701714230291324651040773)
              ·
                refine ⟨3694071418179623372070145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19701714230291324651040773 3694071418179623372070145)
                ·
                  refine ⟨2770553563634717529052609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694071418179623372070145 2770553563634717529052609)
                  ·
                    refine ⟨2077915172726038146789457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2770553563634717529052609 2077915172726038146789457)
                    ·
                      refine ⟨1558436379544528610092093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2077915172726038146789457 1558436379544528610092093)
                      ·
                        rfl

theorem cell23_3035044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_3035044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035044 prefixEnd_3035044 := by exact prefixLift 3035044
  have htrace : WordTrace (prefixWord ++ tailWord_3035044) baseStart_3035044 baseEnd_3035044 := by
    simpa [prefixWord, tailWord_3035044, baseEnd_3035044] using wordTrace_append hprefix tailTrace_3035044
  have hstable : (prefixWord ++ tailWord_3035044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035044).length < 2 ^ (prefixWord ++ tailWord_3035044).sum := by decide
  have hdescent : baseEnd_3035044 < baseStart_3035044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035063 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 1, 7]
def baseStart_3035063 : Nat := 118140960795 + 3035063 * 2 ^ 59
def prefixEnd_3035063 : Nat := 4983230072969 + 3 ^ 40 * 3035063 * 2
def baseEnd_3035063 : Nat := 519482045225654678584835

theorem tailTrace_3035063 : CollatzResearch.WordTrace tailWord_3035063 prefixEnd_3035063 519482045225654678584835 := by
  unfold tailWord_3035063
  simp only [CollatzResearch.WordTrace]
  refine ⟨110697841803492573337757843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73798561202328382225171895 110697841803492573337757843)
  ·
    refine ⟨166046762705238860006636765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110697841803492573337757843 166046762705238860006636765)
    ·
      refine ⟨62267536014464572502488787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166046762705238860006636765 62267536014464572502488787)
      ·
        refine ⟨93401304021696858753733181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62267536014464572502488787 93401304021696858753733181)
        ·
          refine ⟨35025489008136322032649943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93401304021696858753733181 35025489008136322032649943)
          ·
            refine ⟨52538233512204483048974915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35025489008136322032649943 52538233512204483048974915)
            ·
              refine ⟨78807350268306724573462373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52538233512204483048974915 78807350268306724573462373)
              ·
                refine ⟨14776378175307510857524195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78807350268306724573462373 14776378175307510857524195)
                ·
                  refine ⟨22164567262961266286286293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14776378175307510857524195 22164567262961266286286293)
                  ·
                    refine ⟨519482045225654678584835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22164567262961266286286293 519482045225654678584835)
                    ·
                      rfl

theorem cell23_3035063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_3035063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035063 prefixEnd_3035063 := by exact prefixLift 3035063
  have htrace : WordTrace (prefixWord ++ tailWord_3035063) baseStart_3035063 baseEnd_3035063 := by
    simpa [prefixWord, tailWord_3035063, baseEnd_3035063] using wordTrace_append hprefix tailTrace_3035063
  have hstable : (prefixWord ++ tailWord_3035063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035063).length < 2 ^ (prefixWord ++ tailWord_3035063).sum := by decide
  have hdescent : baseEnd_3035063 < baseStart_3035063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035080 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3035080 : Nat := 118140960795 + 3035080 * 2 ^ 59
def prefixEnd_3035080 : Nat := 4983230072969 + 3 ^ 40 * 3035080 * 2
def baseEnd_3035080 : Nat := 519484954949363489747309

theorem tailTrace_3035080 : CollatzResearch.WordTrace tailWord_3035080 prefixEnd_3035080 519484954949363489747309 := by
  unfold tailWord_3035080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55349230922215492620563347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73798974562953990160751129 55349230922215492620563347)
  ·
    refine ⟨83023846383323238930845021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55349230922215492620563347 83023846383323238930845021)
    ·
      refine ⟨31133942393746214599066883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83023846383323238930845021 31133942393746214599066883)
      ·
        refine ⟨46700913590619321898600325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31133942393746214599066883 46700913590619321898600325)
        ·
          refine ⟨8756421298241122855987561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46700913590619321898600325 8756421298241122855987561)
          ·
            refine ⟨6567315973680842141990671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8756421298241122855987561 6567315973680842141990671)
            ·
              refine ⟨9850973960521263212986007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567315973680842141990671 9850973960521263212986007)
              ·
                refine ⟨14776460940781894819479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9850973960521263212986007 14776460940781894819479011)
                ·
                  refine ⟨22164691411172842229218517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14776460940781894819479011 22164691411172842229218517)
                  ·
                    refine ⟨519484954949363489747309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22164691411172842229218517 519484954949363489747309)
                    ·
                      rfl

theorem cell23_3035080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3035080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035080 prefixEnd_3035080 := by exact prefixLift 3035080
  have htrace : WordTrace (prefixWord ++ tailWord_3035080) baseStart_3035080 baseEnd_3035080 := by
    simpa [prefixWord, tailWord_3035080, baseEnd_3035080] using wordTrace_append hprefix tailTrace_3035080
  have hstable : (prefixWord ++ tailWord_3035080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035080).length < 2 ^ (prefixWord ++ tailWord_3035080).sum := by decide
  have hdescent : baseEnd_3035080 < baseStart_3035080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035120 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_3035120 : Nat := 118140960795 + 3035120 * 2 ^ 59
def prefixEnd_3035120 : Nat := 4983230072969 + 3 ^ 40 * 3035120 * 2
def baseEnd_3035120 : Nat := 1558475404074270312741743

theorem tailTrace_3035120 : CollatzResearch.WordTrace tailWord_3035120 prefixEnd_3035120 1558475404074270312741743 := by
  unfold tailWord_3035120
  simp only [CollatzResearch.WordTrace]
  refine ⟨55349960382143036036291407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73799947176190714715055209 55349960382143036036291407)
  ·
    refine ⟨83024940573214554054437111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55349960382143036036291407 83024940573214554054437111)
    ·
      refine ⟨124537410859821831081655667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83024940573214554054437111 124537410859821831081655667)
      ·
        refine ⟨186806116289732746622483501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124537410859821831081655667 186806116289732746622483501)
        ·
          refine ⟨70052293608649779983431313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186806116289732746622483501 70052293608649779983431313)
          ·
            refine ⟨52539220206487334987573485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70052293608649779983431313 52539220206487334987573485)
            ·
              refine ⟨19702207577432750620340057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52539220206487334987573485 19702207577432750620340057)
              ·
                refine ⟨14776655683074562965255043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19702207577432750620340057 14776655683074562965255043)
                ·
                  refine ⟨22164983524611844447882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14776655683074562965255043 22164983524611844447882565)
                  ·
                    refine ⟨4155934410864720833977981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22164983524611844447882565 4155934410864720833977981)
                    ·
                      refine ⟨1558475404074270312741743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155934410864720833977981 1558475404074270312741743)
                      ·
                        rfl

theorem cell23_3035120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_3035120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035120 prefixEnd_3035120 := by exact prefixLift 3035120
  have htrace : WordTrace (prefixWord ++ tailWord_3035120) baseStart_3035120 baseEnd_3035120 := by
    simpa [prefixWord, tailWord_3035120, baseEnd_3035120] using wordTrace_append hprefix tailTrace_3035120
  have hstable : (prefixWord ++ tailWord_3035120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035120).length < 2 ^ (prefixWord ++ tailWord_3035120).sum := by decide
  have hdescent : baseEnd_3035120 < baseStart_3035120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035137 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3035137 : Nat := 118140960795 + 3035137 * 2 ^ 59
def prefixEnd_3035137 : Nat := 4983230072969 + 3 ^ 40 * 3035137 * 2
def baseEnd_3035137 : Nat := 1558484133245396746229165

theorem tailTrace_3035137 : CollatzResearch.WordTrace tailWord_3035137 prefixEnd_3035137 1558484133245396746229165 := by
  unfold tailWord_3035137
  simp only [CollatzResearch.WordTrace]
  refine ⟨110700540805224483975951665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73800360536816322650634443 110700540805224483975951665)
  ·
    refine ⟨83025405603918362981963749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110700540805224483975951665 83025405603918362981963749)
    ·
      refine ⟨15567263550734693059118203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83025405603918362981963749 15567263550734693059118203)
      ·
        refine ⟨23350895326102039588677305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567263550734693059118203 23350895326102039588677305)
        ·
          refine ⟨17513171494576529691507979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23350895326102039588677305 17513171494576529691507979)
          ·
            refine ⟨26269757241864794537261969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17513171494576529691507979 26269757241864794537261969)
            ·
              refine ⟨19702317931398595902946477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26269757241864794537261969 19702317931398595902946477)
              ·
                refine ⟨7388369224274473463604929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19702317931398595902946477 7388369224274473463604929)
                ·
                  refine ⟨5541276918205855097703697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7388369224274473463604929 5541276918205855097703697)
                  ·
                    refine ⟨4155957688654391323277773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5541276918205855097703697 4155957688654391323277773)
                    ·
                      refine ⟨1558484133245396746229165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4155957688654391323277773 1558484133245396746229165)
                      ·
                        rfl

theorem cell23_3035137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3035137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035137 prefixEnd_3035137 := by exact prefixLift 3035137
  have htrace : WordTrace (prefixWord ++ tailWord_3035137) baseStart_3035137 baseEnd_3035137 := by
    simpa [prefixWord, tailWord_3035137, baseEnd_3035137] using wordTrace_append hprefix tailTrace_3035137
  have hstable : (prefixWord ++ tailWord_3035137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035137).length < 2 ^ (prefixWord ++ tailWord_3035137).sum := by decide
  have hdescent : baseEnd_3035137 < baseStart_3035137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035187 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 1, 5]
def baseStart_3035187 : Nat := 118140960795 + 3035187 * 2 ^ 59
def prefixEnd_3035187 : Nat := 4983230072969 + 3 ^ 40 * 3035187 * 2
def baseEnd_3035187 : Nat := 519503269092707183534645

theorem tailTrace_3035187 : CollatzResearch.WordTrace tailWord_3035187 prefixEnd_3035187 519503269092707183534645 := by
  unfold tailWord_3035187
  simp only [CollatzResearch.WordTrace]
  refine ⟨110702364455043342515271815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73801576303362228343514543 110702364455043342515271815)
  ·
    refine ⟨166053546682565013772907723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110702364455043342515271815 166053546682565013772907723)
    ·
      refine ⟨249080320023847520659361585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166053546682565013772907723 249080320023847520659361585)
      ·
        refine ⟨186810240017885640494521189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249080320023847520659361585 186810240017885640494521189)
        ·
          refine ⟨35026920003353557592722723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186810240017885640494521189 35026920003353557592722723)
          ·
            refine ⟨52540380005030336389084085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35026920003353557592722723 52540380005030336389084085)
            ·
              refine ⟨4925660625471594036476633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52540380005030336389084085 4925660625471594036476633)
              ·
                refine ⟨3694245469103695527357475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925660625471594036476633 3694245469103695527357475)
                ·
                  refine ⟨5541368203655543291036213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694245469103695527357475 5541368203655543291036213)
                  ·
                    refine ⟨519503269092707183534645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5541368203655543291036213 519503269092707183534645)
                    ·
                      rfl

theorem cell23_3035187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 5].length) (baseStart_3035187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035187 prefixEnd_3035187 := by exact prefixLift 3035187
  have htrace : WordTrace (prefixWord ++ tailWord_3035187) baseStart_3035187 baseEnd_3035187 := by
    simpa [prefixWord, tailWord_3035187, baseEnd_3035187] using wordTrace_append hprefix tailTrace_3035187
  have hstable : (prefixWord ++ tailWord_3035187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035187).length < 2 ^ (prefixWord ++ tailWord_3035187).sum := by decide
  have hdescent : baseEnd_3035187 < baseStart_3035187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035200 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_3035200 : Nat := 118140960795 + 3035200 * 2 ^ 59
def prefixEnd_3035200 : Nat := 4983230072969 + 3 ^ 40 * 3035200 * 2
def baseEnd_3035200 : Nat := 519505494175543333247125

theorem tailTrace_3035200 : CollatzResearch.WordTrace tailWord_3035200 prefixEnd_3035200 519505494175543333247125 := by
  unfold tailWord_3035200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55351419301998122867747527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73801892402664163823663369 55351419301998122867747527)
  ·
    refine ⟨83027128952997184301621291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55351419301998122867747527 83027128952997184301621291)
    ·
      refine ⟨124540693429495776452431937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83027128952997184301621291 124540693429495776452431937)
      ·
        refine ⟨93405520072121832339323953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124540693429495776452431937 93405520072121832339323953)
        ·
          refine ⟨70054140054091374254492965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93405520072121832339323953 70054140054091374254492965)
          ·
            refine ⟨13135151260142132672717431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70054140054091374254492965 13135151260142132672717431)
            ·
              refine ⟨19702726890213199009076147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13135151260142132672717431 19702726890213199009076147)
              ·
                refine ⟨29554090335319798513614221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19702726890213199009076147 29554090335319798513614221)
                ·
                  refine ⟨11082783875744924442605333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29554090335319798513614221 11082783875744924442605333)
                  ·
                    refine ⟨519505494175543333247125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11082783875744924442605333 519505494175543333247125)
                    ·
                      rfl

theorem cell23_3035200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_3035200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035200 prefixEnd_3035200 := by exact prefixLift 3035200
  have htrace : WordTrace (prefixWord ++ tailWord_3035200) baseStart_3035200 baseEnd_3035200 := by
    simpa [prefixWord, tailWord_3035200, baseEnd_3035200] using wordTrace_append hprefix tailTrace_3035200
  have hstable : (prefixWord ++ tailWord_3035200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035200).length < 2 ^ (prefixWord ++ tailWord_3035200).sum := by decide
  have hdescent : baseEnd_3035200 < baseStart_3035200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035218 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3035218 : Nat := 118140960795 + 3035218 * 2 ^ 59
def prefixEnd_3035218 : Nat := 4983230072969 + 3 ^ 40 * 3035218 * 2
def baseEnd_3035218 : Nat := 1558525725178410929316293

theorem tailTrace_3035218 : CollatzResearch.WordTrace tailWord_3035218 prefixEnd_3035218 1558525725178410929316293 := by
  unfold tailWord_3035218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27675873779482758702412577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73802330078620689873100205 27675873779482758702412577)
  ·
    refine ⟨20756905334612069026809433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27675873779482758702412577 20756905334612069026809433)
    ·
      refine ⟨15567679000959051770107075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20756905334612069026809433 15567679000959051770107075)
      ·
        refine ⟨23351518501438577655160613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567679000959051770107075 23351518501438577655160613)
        ·
          refine ⟨4378409719019733310342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23351518501438577655160613 4378409719019733310342615)
          ·
            refine ⟨6567614578529599965513923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378409719019733310342615 6567614578529599965513923)
            ·
              refine ⟨9851421867794399948270885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567614578529599965513923 9851421867794399948270885)
              ·
                refine ⟨1847141600211449990300791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9851421867794399948270885 1847141600211449990300791)
                ·
                  refine ⟨2770712400317174985451187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847141600211449990300791 2770712400317174985451187)
                  ·
                    refine ⟨4156068600475762478176781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770712400317174985451187 4156068600475762478176781)
                    ·
                      refine ⟨1558525725178410929316293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4156068600475762478176781 1558525725178410929316293)
                      ·
                        rfl

theorem cell23_3035218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3035218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035218 prefixEnd_3035218 := by exact prefixLift 3035218
  have htrace : WordTrace (prefixWord ++ tailWord_3035218) baseStart_3035218 baseEnd_3035218 := by
    simpa [prefixWord, tailWord_3035218, baseEnd_3035218] using wordTrace_append hprefix tailTrace_3035218
  have hstable : (prefixWord ++ tailWord_3035218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035218).length < 2 ^ (prefixWord ++ tailWord_3035218).sum := by decide
  have hdescent : baseEnd_3035218 < baseStart_3035218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035237 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3035237 : Nat := 118140960795 + 3035237 * 2 ^ 59
def prefixEnd_3035237 : Nat := 4983230072969 + 3 ^ 40 * 3035237 * 2
def baseEnd_3035237 : Nat := 1558535481310846354978705

theorem tailTrace_3035237 : CollatzResearch.WordTrace tailWord_3035237 prefixEnd_3035237 1558535481310846354978705 := by
  unfold tailWord_3035237
  simp only [CollatzResearch.WordTrace]
  refine ⟨110704188104862201054591965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73802792069908134036394643 110704188104862201054591965)
  ·
    refine ⟨41514070539323325395471987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110704188104862201054591965 41514070539323325395471987)
    ·
      refine ⟨62271105808984988093207981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41514070539323325395471987 62271105808984988093207981)
      ·
        refine ⟨23351664678369370534952993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62271105808984988093207981 23351664678369370534952993)
        ·
          refine ⟨17513748508777027901214745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23351664678369370534952993 17513748508777027901214745)
          ·
            refine ⟨13135311381582770925911059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513748508777027901214745 13135311381582770925911059)
            ·
              refine ⟨19702967072374156388866589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13135311381582770925911059 19702967072374156388866589)
              ·
                refine ⟨7388612652140308645824971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19702967072374156388866589 7388612652140308645824971)
                ·
                  refine ⟨11082918978210462968737457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7388612652140308645824971 11082918978210462968737457)
                  ·
                    refine ⟨8312189233657847226553093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11082918978210462968737457 8312189233657847226553093)
                    ·
                      refine ⟨1558535481310846354978705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8312189233657847226553093 1558535481310846354978705)
                      ·
                        rfl

theorem cell23_3035237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3035237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035237 prefixEnd_3035237 := by exact prefixLift 3035237
  have htrace : WordTrace (prefixWord ++ tailWord_3035237) baseStart_3035237 baseEnd_3035237 := by
    simpa [prefixWord, tailWord_3035237, baseEnd_3035237] using wordTrace_append hprefix tailTrace_3035237
  have hstable : (prefixWord ++ tailWord_3035237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035237).length < 2 ^ (prefixWord ++ tailWord_3035237).sum := by decide
  have hdescent : baseEnd_3035237 < baseStart_3035237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035247 : List Nat := [1, 1, 2, 1, 3, 5, 3, 7]
def baseStart_3035247 : Nat := 118140960795 + 3035247 * 2 ^ 59
def prefixEnd_3035247 : Nat := 4983230072969 + 3 ^ 40 * 3035247 * 2
def baseEnd_3035247 : Nat := 57723726522866345031617

theorem tailTrace_3035247 : CollatzResearch.WordTrace tailWord_3035247 prefixEnd_3035247 57723726522866345031617 := by
  unfold tailWord_3035247
  simp only [CollatzResearch.WordTrace]
  refine ⟨110704552834825972762455995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73803035223217315174970663 110704552834825972762455995)
  ·
    refine ⟨166056829252238959143683993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110704552834825972762455995 166056829252238959143683993)
    ·
      refine ⟨124542621939179219357762995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166056829252238959143683993 124542621939179219357762995)
      ·
        refine ⟨186813932908768829036644493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124542621939179219357762995 186813932908768829036644493)
        ·
          refine ⟨70055224840788310888741685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186813932908768829036644493 70055224840788310888741685)
          ·
            refine ⟨6567677328823904145819533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70055224840788310888741685 6567677328823904145819533)
            ·
              refine ⟨2462878998308964054682325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6567677328823904145819533 2462878998308964054682325)
              ·
                refine ⟨57723726522866345031617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2462878998308964054682325 57723726522866345031617)
                ·
                  rfl

theorem cell23_3035247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 7].length) (baseStart_3035247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035247 prefixEnd_3035247 := by exact prefixLift 3035247
  have htrace : WordTrace (prefixWord ++ tailWord_3035247) baseStart_3035247 baseEnd_3035247 := by
    simpa [prefixWord, tailWord_3035247, baseEnd_3035247] using wordTrace_append hprefix tailTrace_3035247
  have hstable : (prefixWord ++ tailWord_3035247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035247).length < 2 ^ (prefixWord ++ tailWord_3035247).sum := by decide
  have hdescent : baseEnd_3035247 < baseStart_3035247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035254 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3035254 : Nat := 118140960795 + 3035254 * 2 ^ 59
def prefixEnd_3035254 : Nat := 4983230072969 + 3 ^ 40 * 3035254 * 2
def baseEnd_3035254 : Nat := 1558544210481972788466127

theorem tailTrace_3035254 : CollatzResearch.WordTrace tailWord_3035254 prefixEnd_3035254 1558544210481972788466127 := by
  unfold tailWord_3035254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919050509112538309872551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73803205430533741971973877 6919050509112538309872551)
  ·
    refine ⟨10378575763668807464808827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919050509112538309872551 10378575763668807464808827)
    ·
      refine ⟨15567863645503211197213241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378575763668807464808827 15567863645503211197213241)
      ·
        refine ⟨11675897734127408397909931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15567863645503211197213241 11675897734127408397909931)
        ·
          refine ⟨17513846601191112596864897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675897734127408397909931 17513846601191112596864897)
          ·
            refine ⟨13135384950893334447648673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513846601191112596864897 13135384950893334447648673)
            ·
              refine ⟨9851538713170000835736505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13135384950893334447648673 9851538713170000835736505)
              ·
                refine ⟨7388654034877500626802379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9851538713170000835736505 7388654034877500626802379)
                ·
                  refine ⟨11082981052316250940203569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7388654034877500626802379 11082981052316250940203569)
                  ·
                    refine ⟨8312235789237188205152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11082981052316250940203569 8312235789237188205152677)
                    ·
                      refine ⟨1558544210481972788466127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8312235789237188205152677 1558544210481972788466127)
                      ·
                        rfl

theorem cell23_3035254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3035254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035254 prefixEnd_3035254 := by exact prefixLift 3035254
  have htrace : WordTrace (prefixWord ++ tailWord_3035254) baseStart_3035254 baseEnd_3035254 := by
    simpa [prefixWord, tailWord_3035254, baseEnd_3035254] using wordTrace_append hprefix tailTrace_3035254
  have hstable : (prefixWord ++ tailWord_3035254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035254).length < 2 ^ (prefixWord ++ tailWord_3035254).sum := by decide
  have hdescent : baseEnd_3035254 < baseStart_3035254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035261 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_3035261 : Nat := 118140960795 + 3035261 * 2 ^ 59
def prefixEnd_3035261 : Nat := 4983230072969 + 3 ^ 40 * 3035261 * 2
def baseEnd_3035261 : Nat := 1558547804846554261078595

theorem tailTrace_3035261 : CollatzResearch.WordTrace tailWord_3035261 prefixEnd_3035261 1558547804846554261078595 := by
  unfold tailWord_3035261
  simp only [CollatzResearch.WordTrace]
  refine ⟨110705063456775253153465637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73803375637850168768977091 110705063456775253153465637)
  ·
    refine ⟨20757199398145359966274807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110705063456775253153465637 20757199398145359966274807)
    ·
      refine ⟨31135799097218039949412211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20757199398145359966274807 31135799097218039949412211)
      ·
        refine ⟨46703698645827059924118317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31135799097218039949412211 46703698645827059924118317)
        ·
          refine ⟨17513886992185147471544369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46703698645827059924118317 17513886992185147471544369)
          ·
            refine ⟨13135415244138860603658277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513886992185147471544369 13135415244138860603658277)
            ·
              refine ⟨2462890358276036363185927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13135415244138860603658277 2462890358276036363185927)
              ·
                refine ⟨3694335537414054544778891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462890358276036363185927 3694335537414054544778891)
                ·
                  refine ⟨5541503306121081817168337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694335537414054544778891 5541503306121081817168337)
                  ·
                    refine ⟨4156127479590811362876253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5541503306121081817168337 4156127479590811362876253)
                    ·
                      refine ⟨1558547804846554261078595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4156127479590811362876253 1558547804846554261078595)
                      ·
                        rfl

theorem cell23_3035261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_3035261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035261 prefixEnd_3035261 := by exact prefixLift 3035261
  have htrace : WordTrace (prefixWord ++ tailWord_3035261) baseStart_3035261 baseEnd_3035261 := by
    simpa [prefixWord, tailWord_3035261, baseEnd_3035261] using wordTrace_append hprefix tailTrace_3035261
  have hstable : (prefixWord ++ tailWord_3035261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035261).length < 2 ^ (prefixWord ++ tailWord_3035261).sum := by decide
  have hdescent : baseEnd_3035261 < baseStart_3035261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035301 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_3035301 : Nat := 118140960795 + 3035301 * 2 ^ 59
def prefixEnd_3035301 : Nat := 4983230072969 + 3 ^ 40 * 3035301 * 2
def baseEnd_3035301 : Nat := 1558568344072734104578411

theorem tailTrace_3035301 : CollatzResearch.WordTrace tailWord_3035301 prefixEnd_3035301 1558568344072734104578411 := by
  unfold tailWord_3035301
  simp only [CollatzResearch.WordTrace]
  refine ⟨110706522376630339984921757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73804348251086893323281171 110706522376630339984921757)
  ·
    refine ⟨41514945891236377494345659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110706522376630339984921757 41514945891236377494345659)
    ·
      refine ⟨62272418836854566241518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41514945891236377494345659 62272418836854566241518489)
      ·
        refine ⟨46704314127640924681138867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62272418836854566241518489 46704314127640924681138867)
        ·
          refine ⟨70056471191461387021708301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46704314127640924681138867 70056471191461387021708301)
          ·
            refine ⟨26271176696798020133140613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70056471191461387021708301 26271176696798020133140613)
            ·
              refine ⟨4925845630649628774963865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26271176696798020133140613 4925845630649628774963865)
              ·
                refine ⟨3694384222987221581222899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925845630649628774963865 3694384222987221581222899)
                ·
                  refine ⟨5541576334480832371834349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694384222987221581222899 5541576334480832371834349)
                  ·
                    refine ⟨2078091125430312139437881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5541576334480832371834349 2078091125430312139437881)
                    ·
                      refine ⟨1558568344072734104578411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078091125430312139437881 1558568344072734104578411)
                      ·
                        rfl

theorem cell23_3035301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_3035301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035301 prefixEnd_3035301 := by exact prefixLift 3035301
  have htrace : WordTrace (prefixWord ++ tailWord_3035301) baseStart_3035301 baseEnd_3035301 := by
    simpa [prefixWord, tailWord_3035301, baseEnd_3035301] using wordTrace_append hprefix tailTrace_3035301
  have hstable : (prefixWord ++ tailWord_3035301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035301).length < 2 ^ (prefixWord ++ tailWord_3035301).sum := by decide
  have hdescent : baseEnd_3035301 < baseStart_3035301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035314 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3035314 : Nat := 118140960795 + 3035314 * 2 ^ 59
def prefixEnd_3035314 : Nat := 4983230072969 + 3 ^ 40 * 3035314 * 2
def baseEnd_3035314 : Nat := 1558575019321242553715851

theorem tailTrace_3035314 : CollatzResearch.WordTrace tailWord_3035314 prefixEnd_3035314 1558575019321242553715851 := by
  unfold tailWord_3035314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676749131395810801286249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73804664350388828803429997 27676749131395810801286249)
  ·
    refine ⟨20757561848546858100964687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27676749131395810801286249 20757561848546858100964687)
    ·
      refine ⟨31136342772820287151447031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20757561848546858100964687 31136342772820287151447031)
      ·
        refine ⟨46704514159230430727170547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31136342772820287151447031 46704514159230430727170547)
        ·
          refine ⟨70056771238845646090755821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46704514159230430727170547 70056771238845646090755821)
          ·
            refine ⟨26271289214567117284033433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70056771238845646090755821 26271289214567117284033433)
            ·
              refine ⟨19703466910925337963025075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26271289214567117284033433 19703466910925337963025075)
              ·
                refine ⟨29555200366388006944537613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19703466910925337963025075 29555200366388006944537613)
                ·
                  refine ⟨11083200137395502604201605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29555200366388006944537613 11083200137395502604201605)
                  ·
                    refine ⟨2078100025761656738287801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11083200137395502604201605 2078100025761656738287801)
                    ·
                      refine ⟨1558575019321242553715851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078100025761656738287801 1558575019321242553715851)
                      ·
                        rfl

theorem cell23_3035314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3035314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035314 prefixEnd_3035314 := by exact prefixLift 3035314
  have htrace : WordTrace (prefixWord ++ tailWord_3035314) baseStart_3035314 baseEnd_3035314 := by
    simpa [prefixWord, tailWord_3035314, baseEnd_3035314] using wordTrace_append hprefix tailTrace_3035314
  have hstable : (prefixWord ++ tailWord_3035314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035314).length < 2 ^ (prefixWord ++ tailWord_3035314).sum := by decide
  have hdescent : baseEnd_3035314 < baseStart_3035314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035377 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_3035377 : Nat := 118140960795 + 3035377 * 2 ^ 59
def prefixEnd_3035377 : Nat := 4983230072969 + 3 ^ 40 * 3035377 * 2
def baseEnd_3035377 : Nat := 1558607368602475807228061

theorem tailTrace_3035377 : CollatzResearch.WordTrace tailWord_3035377 prefixEnd_3035377 1558607368602475807228061 := by
  unfold tailWord_3035377
  simp only [CollatzResearch.WordTrace]
  refine ⟨110709294324355004964688385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73806196216236669976458923 110709294324355004964688385)
  ·
    refine ⟨83031970743266253723516289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110709294324355004964688385 83031970743266253723516289)
    ·
      refine ⟨62273978057449690292637217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83031970743266253723516289 62273978057449690292637217)
      ·
        refine ⟨46705483543087267719477913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62273978057449690292637217 46705483543087267719477913)
        ·
          refine ⟨35029112657315450789608435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46705483543087267719477913 35029112657315450789608435)
          ·
            refine ⟨52543668985973176184412653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35029112657315450789608435 52543668985973176184412653)
            ·
              refine ⟨19703875869739941069154745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52543668985973176184412653 19703875869739941069154745)
              ·
                refine ⟨14777906902304955801866059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19703875869739941069154745 14777906902304955801866059)
                ·
                  refine ⟨22166860353457433702799089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14777906902304955801866059 22166860353457433702799089)
                  ·
                    refine ⟨16625145265093075277099317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22166860353457433702799089 16625145265093075277099317)
                    ·
                      refine ⟨1558607368602475807228061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16625145265093075277099317 1558607368602475807228061)
                      ·
                        rfl

theorem cell23_3035377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_3035377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035377 prefixEnd_3035377 := by exact prefixLift 3035377
  have htrace : WordTrace (prefixWord ++ tailWord_3035377) baseStart_3035377 baseEnd_3035377 := by
    simpa [prefixWord, tailWord_3035377, baseEnd_3035377] using wordTrace_append hprefix tailTrace_3035377
  have hstable : (prefixWord ++ tailWord_3035377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035377).length < 2 ^ (prefixWord ++ tailWord_3035377).sum := by decide
  have hdescent : baseEnd_3035377 < baseStart_3035377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035388 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 5]
def baseStart_3035388 : Nat := 118140960795 + 3035388 * 2 ^ 59
def prefixEnd_3035388 : Nat := 4983230072969 + 3 ^ 40 * 3035388 * 2
def baseEnd_3035388 : Nat := 173179224098852807132279

theorem tailTrace_3035388 : CollatzResearch.WordTrace tailWord_3035388 prefixEnd_3035388 173179224098852807132279 := by
  unfold tailWord_3035388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55354847763657576921669409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73806463684876769228892545 55354847763657576921669409)
  ·
    refine ⟨41516135822743182691252057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55354847763657576921669409 41516135822743182691252057)
    ·
      refine ⟨31137101867057387018439043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41516135822743182691252057 31137101867057387018439043)
      ·
        refine ⟨46705652800586080527658565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31137101867057387018439043 46705652800586080527658565)
        ·
          refine ⟨8757309900109890098935981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46705652800586080527658565 8757309900109890098935981)
          ·
            refine ⟨3283991212541208787100993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8757309900109890098935981 3283991212541208787100993)
            ·
              refine ⟨2462993409405906590325745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283991212541208787100993 2462993409405906590325745)
              ·
                refine ⟨1847245057054429942744309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462993409405906590325745 1847245057054429942744309)
                ·
                  refine ⟨173179224098852807132279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1847245057054429942744309 173179224098852807132279)
                  ·
                    rfl

theorem cell23_3035388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_3035388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035388 prefixEnd_3035388 := by exact prefixLift 3035388
  have htrace : WordTrace (prefixWord ++ tailWord_3035388) baseStart_3035388 baseEnd_3035388 := by
    simpa [prefixWord, tailWord_3035388, baseEnd_3035388] using wordTrace_append hprefix tailTrace_3035388
  have hstable : (prefixWord ++ tailWord_3035388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035388).length < 2 ^ (prefixWord ++ tailWord_3035388).sum := by decide
  have hdescent : baseEnd_3035388 < baseStart_3035388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035418 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_3035418 : Nat := 118140960795 + 3035418 * 2 ^ 59
def prefixEnd_3035418 : Nat := 4983230072969 + 3 ^ 40 * 3035418 * 2
def baseEnd_3035418 : Nat := 519542807103103382271791

theorem tailTrace_3035418 : CollatzResearch.WordTrace tailWord_3035418 prefixEnd_3035418 519542807103103382271791 := by
  unfold tailWord_3035418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27677697429301617241732727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73807193144804312644620605 27677697429301617241732727)
  ·
    refine ⟨41516546143952425862599091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27677697429301617241732727 41516546143952425862599091)
    ·
      refine ⟨62274819215928638793898637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41516546143952425862599091 62274819215928638793898637)
      ·
        refine ⟨23353057205973239547711989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62274819215928638793898637 23353057205973239547711989)
        ·
          refine ⟨2189349113059991207597999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23353057205973239547711989 2189349113059991207597999)
          ·
            refine ⟨3284023669589986811396999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189349113059991207597999 3284023669589986811396999)
            ·
              refine ⟨4926035504384980217095499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284023669589986811396999 4926035504384980217095499)
              ·
                refine ⟨7389053256577470325643249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926035504384980217095499 7389053256577470325643249)
                ·
                  refine ⟨5541789942433102744232437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389053256577470325643249 5541789942433102744232437)
                  ·
                    refine ⟨519542807103103382271791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5541789942433102744232437 519542807103103382271791)
                    ·
                      rfl

theorem cell23_3035418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_3035418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035418 prefixEnd_3035418 := by exact prefixLift 3035418
  have htrace : WordTrace (prefixWord ++ tailWord_3035418) baseStart_3035418 baseEnd_3035418 := by
    simpa [prefixWord, tailWord_3035418, baseEnd_3035418] using wordTrace_append hprefix tailTrace_3035418
  have hstable : (prefixWord ++ tailWord_3035418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035418).length < 2 ^ (prefixWord ++ tailWord_3035418).sum := by decide
  have hdescent : baseEnd_3035418 < baseStart_3035418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035421 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3035421 : Nat := 118140960795 + 3035421 * 2 ^ 59
def prefixEnd_3035421 : Nat := 4983230072969 + 3 ^ 40 * 3035421 * 2
def baseEnd_3035421 : Nat := 1558629961751273635077859

theorem tailTrace_3035421 : CollatzResearch.WordTrace tailWord_3035421 prefixEnd_3035421 1558629961751273635077859 := by
  unfold tailWord_3035421
  simp only [CollatzResearch.WordTrace]
  refine ⟨110710899136195600479290117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73807266090797066986193411 110710899136195600479290117)
  ·
    refine ⟨20758293588036675089866897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110710899136195600479290117 20758293588036675089866897)
    ·
      refine ⟨15568720191027506317400173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20758293588036675089866897 15568720191027506317400173)
      ·
        refine ⟨5838270071635314869025065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15568720191027506317400173 5838270071635314869025065)
        ·
          refine ⟨4378702553726486151768799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5838270071635314869025065 4378702553726486151768799)
          ·
            refine ⟨6568053830589729227653199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378702553726486151768799 6568053830589729227653199)
            ·
              refine ⟨9852080745884593841479799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568053830589729227653199 9852080745884593841479799)
              ·
                refine ⟨14778121118826890762219699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9852080745884593841479799 14778121118826890762219699)
                ·
                  refine ⟨22167181678240336143329549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14778121118826890762219699 22167181678240336143329549)
                  ·
                    refine ⟨8312693129340126053748581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22167181678240336143329549 8312693129340126053748581)
                    ·
                      refine ⟨1558629961751273635077859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8312693129340126053748581 1558629961751273635077859)
                      ·
                        rfl

theorem cell23_3035421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3035421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035421 prefixEnd_3035421 := by exact prefixLift 3035421
  have htrace : WordTrace (prefixWord ++ tailWord_3035421) baseStart_3035421 baseEnd_3035421 := by
    simpa [prefixWord, tailWord_3035421, baseEnd_3035421] using wordTrace_append hprefix tailTrace_3035421
  have hstable : (prefixWord ++ tailWord_3035421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035421).length < 2 ^ (prefixWord ++ tailWord_3035421).sum := by decide
  have hdescent : baseEnd_3035421 < baseStart_3035421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035427 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 8]
def baseStart_3035427 : Nat := 118140960795 + 3035427 * 2 ^ 59
def prefixEnd_3035427 : Nat := 4983230072969 + 3 ^ 40 * 3035427 * 2
def baseEnd_3035427 : Nat := 173181449181688956844759

theorem tailTrace_3035427 : CollatzResearch.WordTrace tailWord_3035427 prefixEnd_3035427 173181449181688956844759 := by
  unfold tailWord_3035427
  simp only [CollatzResearch.WordTrace]
  refine ⟨110711117974173863504008535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73807411982782575669339023 110711117974173863504008535)
  ·
    refine ⟨166066676961260795256012803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110711117974173863504008535 166066676961260795256012803)
    ·
      refine ⟨249100015441891192884019205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166066676961260795256012803 249100015441891192884019205)
      ·
        refine ⟨46706252895354598665753601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249100015441891192884019205 46706252895354598665753601)
        ·
          refine ⟨35029689671515948999315201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46706252895354598665753601 35029689671515948999315201)
          ·
            refine ⟨26272267253636961749486401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35029689671515948999315201 26272267253636961749486401)
            ·
              refine ⟨19704200440227721312114801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26272267253636961749486401 19704200440227721312114801)
              ·
                refine ⟨14778150330170790984086101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19704200440227721312114801 14778150330170790984086101)
                ·
                  refine ⟨173181449181688956844759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14778150330170790984086101 173181449181688956844759)
                  ·
                    rfl

theorem cell23_3035427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 8].length) (baseStart_3035427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035427 prefixEnd_3035427 := by exact prefixLift 3035427
  have htrace : WordTrace (prefixWord ++ tailWord_3035427) baseStart_3035427 baseEnd_3035427 := by
    simpa [prefixWord, tailWord_3035427, baseEnd_3035427] using wordTrace_append hprefix tailTrace_3035427
  have hstable : (prefixWord ++ tailWord_3035427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035427).length < 2 ^ (prefixWord ++ tailWord_3035427).sum := by decide
  have hdescent : baseEnd_3035427 < baseStart_3035427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035474 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3035474 : Nat := 118140960795 + 3035474 * 2 ^ 59
def prefixEnd_3035474 : Nat := 4983230072969 + 3 ^ 40 * 3035474 * 2
def baseEnd_3035474 : Nat := 519552392075320642571705

theorem tailTrace_3035474 : CollatzResearch.WordTrace tailWord_3035474 prefixEnd_3035474 519552392075320642571705 := by
  unfold tailWord_3035474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678208051250897632742369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73808554803335727020646317 27678208051250897632742369)
  ·
    refine ⟨20758656038438173224556777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27678208051250897632742369 20758656038438173224556777)
    ·
      refine ⟨15568992028828629918417583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20758656038438173224556777 15568992028828629918417583)
      ·
        refine ⟨23353488043242944877626375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568992028828629918417583 23353488043242944877626375)
        ·
          refine ⟨35030232064864417316439563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23353488043242944877626375 35030232064864417316439563)
          ·
            refine ⟨52545348097296625974659345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35030232064864417316439563 52545348097296625974659345)
            ·
              refine ⟨39409011072972469480994509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52545348097296625974659345 39409011072972469480994509)
              ·
                refine ⟨14778379152364676055372941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39409011072972469480994509 14778379152364676055372941)
                ·
                  refine ⟨5541892182136753520764853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14778379152364676055372941 5541892182136753520764853)
                  ·
                    refine ⟨519552392075320642571705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5541892182136753520764853 519552392075320642571705)
                    ·
                      rfl

theorem cell23_3035474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3035474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035474 prefixEnd_3035474 := by exact prefixLift 3035474
  have htrace : WordTrace (prefixWord ++ tailWord_3035474) baseStart_3035474 baseEnd_3035474 := by
    simpa [prefixWord, tailWord_3035474, baseEnd_3035474] using wordTrace_append hprefix tailTrace_3035474
  have hstable : (prefixWord ++ tailWord_3035474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035474).length < 2 ^ (prefixWord ++ tailWord_3035474).sum := by decide
  have hdescent : baseEnd_3035474 < baseStart_3035474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035481 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 2, 3, 2]
def baseStart_3035481 : Nat := 118140960795 + 3035481 * 2 ^ 59
def prefixEnd_3035481 : Nat := 4983230072969 + 3 ^ 40 * 3035481 * 2
def baseEnd_3035481 : Nat := 1558660770590543400327583

theorem tailTrace_3035481 : CollatzResearch.WordTrace tailWord_3035481 prefixEnd_3035481 1558660770590543400327583 := by
  unfold tailWord_3035481
  simp only [CollatzResearch.WordTrace]
  refine ⟨110713087515978230726474297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73808725010652153817649531 110713087515978230726474297)
  ·
    refine ⟨83034815636983673044855723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110713087515978230726474297 83034815636983673044855723)
    ·
      refine ⟨124552223455475509567283585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83034815636983673044855723 124552223455475509567283585)
      ·
        refine ⟨93414167591606632175462689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124552223455475509567283585 93414167591606632175462689)
        ·
          refine ⟨70060625693704974131597017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93414167591606632175462689 70060625693704974131597017)
          ·
            refine ⟨52545469270278730598697763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70060625693704974131597017 52545469270278730598697763)
            ·
              refine ⟨78818203905418095898046645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52545469270278730598697763 78818203905418095898046645)
              ·
                refine ⟨7389206616132946490441873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78818203905418095898046645 7389206616132946490441873)
                ·
                  refine ⟨5541904962099709867831405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389206616132946490441873 5541904962099709867831405)
                  ·
                    refine ⟨2078214360787391200436777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5541904962099709867831405 2078214360787391200436777)
                    ·
                      refine ⟨1558660770590543400327583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078214360787391200436777 1558660770590543400327583)
                      ·
                        rfl

theorem cell23_3035481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_3035481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035481 prefixEnd_3035481 := by exact prefixLift 3035481
  have htrace : WordTrace (prefixWord ++ tailWord_3035481) baseStart_3035481 baseEnd_3035481 := by
    simpa [prefixWord, tailWord_3035481, baseEnd_3035481] using wordTrace_append hprefix tailTrace_3035481
  have hstable : (prefixWord ++ tailWord_3035481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035481).length < 2 ^ (prefixWord ++ tailWord_3035481).sum := by decide
  have hdescent : baseEnd_3035481 < baseStart_3035481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035498 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3035498 : Nat := 118140960795 + 3035498 * 2 ^ 59
def prefixEnd_3035498 : Nat := 4983230072969 + 3 ^ 40 * 3035498 * 2
def baseEnd_3035498 : Nat := 1558669499761669833815005

theorem tailTrace_3035498 : CollatzResearch.WordTrace tailWord_3035498 prefixEnd_3035498 1558669499761669833815005 := by
  unfold tailWord_3035498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678426889229160657460787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73809138371277761753228765 27678426889229160657460787)
  ·
    refine ⟨41517640333843740986191181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27678426889229160657460787 41517640333843740986191181)
    ·
      refine ⟨15569115125191402869821693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41517640333843740986191181 15569115125191402869821693)
      ·
        refine ⟨5838418171946776076183135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15569115125191402869821693 5838418171946776076183135)
        ·
          refine ⟨8757627257920164114274703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838418171946776076183135 8757627257920164114274703)
          ·
            refine ⟨13136440886880246171412055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8757627257920164114274703 13136440886880246171412055)
            ·
              refine ⟨19704661330320369257118083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13136440886880246171412055 19704661330320369257118083)
              ·
                refine ⟨29556991995480553885677125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19704661330320369257118083 29556991995480553885677125)
                ·
                  refine ⟨5541935999152603853564461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29556991995480553885677125 5541935999152603853564461)
                  ·
                    refine ⟨2078225999682226445086673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5541935999152603853564461 2078225999682226445086673)
                    ·
                      refine ⟨1558669499761669833815005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078225999682226445086673 1558669499761669833815005)
                      ·
                        rfl

theorem cell23_3035498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3035498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035498 prefixEnd_3035498 := by exact prefixLift 3035498
  have htrace : WordTrace (prefixWord ++ tailWord_3035498) baseStart_3035498 baseEnd_3035498 := by
    simpa [prefixWord, tailWord_3035498, baseEnd_3035498] using wordTrace_append hprefix tailTrace_3035498
  have hstable : (prefixWord ++ tailWord_3035498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035498).length < 2 ^ (prefixWord ++ tailWord_3035498).sum := by decide
  have hdescent : baseEnd_3035498 < baseStart_3035498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035524 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3035524 : Nat := 118140960795 + 3035524 * 2 ^ 59
def prefixEnd_3035524 : Nat := 4983230072969 + 3 ^ 40 * 3035524 * 2
def baseEnd_3035524 : Nat := 1558682850258686732089885

theorem tailTrace_3035524 : CollatzResearch.WordTrace tailWord_3035524 prefixEnd_3035524 1558682850258686732089885 := by
  unfold tailWord_3035524
  simp only [CollatzResearch.WordTrace]
  refine ⟨55357327927411224535144813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73809770569881632713526417 55357327927411224535144813)
  ·
    refine ⟨20758997972779209200679305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55357327927411224535144813 20758997972779209200679305)
    ·
      refine ⟨15569248479584406900509479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20758997972779209200679305 15569248479584406900509479)
      ·
        refine ⟨23353872719376610350764219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15569248479584406900509479 23353872719376610350764219)
        ·
          refine ⟨35030809079064915526146329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23353872719376610350764219 35030809079064915526146329)
          ·
            refine ⟨26273106809298686644609747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35030809079064915526146329 26273106809298686644609747)
            ·
              refine ⟨39409660213948029966914621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26273106809298686644609747 39409660213948029966914621)
              ·
                refine ⟨14778622580230511237592983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39409660213948029966914621 14778622580230511237592983)
                ·
                  refine ⟨22167933870345766856389475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14778622580230511237592983 22167933870345766856389475)
                  ·
                    refine ⟨33251900805518650284584213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22167933870345766856389475 33251900805518650284584213)
                    ·
                      refine ⟨1558682850258686732089885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33251900805518650284584213 1558682850258686732089885)
                      ·
                        rfl

theorem cell23_3035524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3035524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035524 prefixEnd_3035524 := by exact prefixLift 3035524
  have htrace : WordTrace (prefixWord ++ tailWord_3035524) baseStart_3035524 baseEnd_3035524 := by
    simpa [prefixWord, tailWord_3035524, baseEnd_3035524] using wordTrace_append hprefix tailTrace_3035524
  have hstable : (prefixWord ++ tailWord_3035524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035524).length < 2 ^ (prefixWord ++ tailWord_3035524).sum := by decide
  have hdescent : baseEnd_3035524 < baseStart_3035524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035528 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_3035528 : Nat := 118140960795 + 3035528 * 2 ^ 59
def prefixEnd_3035528 : Nat := 4983230072969 + 3 ^ 40 * 3035528 * 2
def baseEnd_3035528 : Nat := 1558684904181304716439867

theorem tailTrace_3035528 : CollatzResearch.WordTrace tailWord_3035528 prefixEnd_3035528 1558684904181304716439867 := by
  unfold tailWord_3035528
  simp only [CollatzResearch.WordTrace]
  refine ⟨55357400873403978876717619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73809867831205305168956825 55357400873403978876717619)
  ·
    refine ⟨83036101310105968315076429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55357400873403978876717619 83036101310105968315076429)
    ·
      refine ⟨31138537991289738118153661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83036101310105968315076429 31138537991289738118153661)
      ·
        refine ⟨11676951746733651794307623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31138537991289738118153661 11676951746733651794307623)
        ·
          refine ⟨17515427620100477691461435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11676951746733651794307623 17515427620100477691461435)
          ·
            refine ⟨26273141430150716537192153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17515427620100477691461435 26273141430150716537192153)
            ·
              refine ⟨19704856072613037402894115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26273141430150716537192153 19704856072613037402894115)
              ·
                refine ⟨29557284108919556104341173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19704856072613037402894115 29557284108919556104341173)
                ·
                  refine ⟨2770995385211208384781985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29557284108919556104341173 2770995385211208384781985)
                  ·
                    refine ⟨2078246538908406288586489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2770995385211208384781985 2078246538908406288586489)
                    ·
                      refine ⟨1558684904181304716439867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078246538908406288586489 1558684904181304716439867)
                      ·
                        rfl

theorem cell23_3035528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_3035528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035528 prefixEnd_3035528 := by exact prefixLift 3035528
  have htrace : WordTrace (prefixWord ++ tailWord_3035528) baseStart_3035528 baseEnd_3035528 := by
    simpa [prefixWord, tailWord_3035528, baseEnd_3035528] using wordTrace_append hprefix tailTrace_3035528
  have hstable : (prefixWord ++ tailWord_3035528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035528).length < 2 ^ (prefixWord ++ tailWord_3035528).sum := by decide
  have hdescent : baseEnd_3035528 < baseStart_3035528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035531 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3]
def baseStart_3035531 : Nat := 118140960795 + 3035531 * 2 ^ 59
def prefixEnd_3035531 : Nat := 4983230072969 + 3 ^ 40 * 3035531 * 2
def baseEnd_3035531 : Nat := 1558686444623268204702353

theorem tailTrace_3035531 : CollatzResearch.WordTrace tailWord_3035531 prefixEnd_3035531 1558686444623268204702353 := by
  unfold tailWord_3035531
  simp only [CollatzResearch.WordTrace]
  refine ⟨110714911165797089265794447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73809940777198059510529631 110714911165797089265794447)
  ·
    refine ⟨166072366748695633898691671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110714911165797089265794447 166072366748695633898691671)
    ·
      refine ⟨249108550123043450848037507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166072366748695633898691671 249108550123043450848037507)
      ·
        refine ⟨373662825184565176272056261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249108550123043450848037507 373662825184565176272056261)
        ·
          refine ⟨70061779722105970551010549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373662825184565176272056261 70061779722105970551010549)
          ·
            refine ⟨6568291848947434739157239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70061779722105970551010549 6568291848947434739157239)
            ·
              refine ⟨9852437773421152108735859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568291848947434739157239 9852437773421152108735859)
              ·
                refine ⟨14778656660131728163103789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9852437773421152108735859 14778656660131728163103789)
                ·
                  refine ⟨5541996247549398061163921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14778656660131728163103789 5541996247549398061163921)
                  ·
                    refine ⟨4156497185662048545872941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5541996247549398061163921 4156497185662048545872941)
                    ·
                      refine ⟨1558686444623268204702353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4156497185662048545872941 1558686444623268204702353)
                      ·
                        rfl

theorem cell23_3035531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].length) (baseStart_3035531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035531 prefixEnd_3035531 := by exact prefixLift 3035531
  have htrace : WordTrace (prefixWord ++ tailWord_3035531) baseStart_3035531 baseEnd_3035531 := by
    simpa [prefixWord, tailWord_3035531, baseEnd_3035531] using wordTrace_append hprefix tailTrace_3035531
  have hstable : (prefixWord ++ tailWord_3035531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035531).length < 2 ^ (prefixWord ++ tailWord_3035531).sum := by decide
  have hdescent : baseEnd_3035531 < baseStart_3035531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035545 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 1, 2, 2]
def baseStart_3035545 : Nat := 118140960795 + 3035545 * 2 ^ 59
def prefixEnd_3035545 : Nat := 4983230072969 + 3 ^ 40 * 3035545 * 2
def baseEnd_3035545 : Nat := 1558693633352431149927289

theorem tailTrace_3035545 : CollatzResearch.WordTrace tailWord_3035545 prefixEnd_3035545 1558693633352431149927289 := by
  unfold tailWord_3035545
  simp only [CollatzResearch.WordTrace]
  refine ⟨110715421787746369656804089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73810281191830913104536059 110715421787746369656804089)
  ·
    refine ⟨83036566340809777242603067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110715421787746369656804089 83036566340809777242603067)
    ·
      refine ⟨124554849511214665863904601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83036566340809777242603067 124554849511214665863904601)
      ·
        refine ⟨93416137133410999397928451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124554849511214665863904601 93416137133410999397928451)
        ·
          refine ⟨140124205700116499096892677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93416137133410999397928451 140124205700116499096892677)
          ·
            refine ⟨26273288568771843580667377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140124205700116499096892677 26273288568771843580667377)
            ·
              refine ⟨19704966426578882685500533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26273288568771843580667377 19704966426578882685500533)
              ·
                refine ⟨1847340602491770251765675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19704966426578882685500533 1847340602491770251765675)
                ·
                  refine ⟨2771010903737655377648513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847340602491770251765675 2771010903737655377648513)
                  ·
                    refine ⟨2078258177803241533236385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771010903737655377648513 2078258177803241533236385)
                    ·
                      refine ⟨1558693633352431149927289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078258177803241533236385 1558693633352431149927289)
                      ·
                        rfl

theorem cell23_3035545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_3035545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035545 prefixEnd_3035545 := by exact prefixLift 3035545
  have htrace : WordTrace (prefixWord ++ tailWord_3035545) baseStart_3035545 baseEnd_3035545 := by
    simpa [prefixWord, tailWord_3035545, baseEnd_3035545] using wordTrace_append hprefix tailTrace_3035545
  have hstable : (prefixWord ++ tailWord_3035545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035545).length < 2 ^ (prefixWord ++ tailWord_3035545).sum := by decide
  have hdescent : baseEnd_3035545 < baseStart_3035545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035561 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_3035561 : Nat := 118140960795 + 3035561 * 2 ^ 59
def prefixEnd_3035561 : Nat := 4983230072969 + 3 ^ 40 * 3035561 * 2
def baseEnd_3035561 : Nat := 1558701849042903087327215

theorem tailTrace_3035561 : CollatzResearch.WordTrace tailWord_3035561 prefixEnd_3035561 1558701849042903087327215 := by
  unfold tailWord_3035561
  simp only [CollatzResearch.WordTrace]
  refine ⟨110716005355688404389386537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73810670237125602926257691 110716005355688404389386537)
  ·
    refine ⟨83037004016766303292039903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110716005355688404389386537 83037004016766303292039903)
    ·
      refine ⟨124555506025149454938059855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83037004016766303292039903 124555506025149454938059855)
      ·
        refine ⟨186833259037724182407089783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124555506025149454938059855 186833259037724182407089783)
        ·
          refine ⟨280249888556586273610634675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186833259037724182407089783 280249888556586273610634675)
          ·
            refine ⟨420374832834879410415952013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280249888556586273610634675 420374832834879410415952013)
            ·
              refine ⟨157640562313079778905982005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420374832834879410415952013 157640562313079778905982005)
              ·
                refine ⟨14778802716851229272435813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157640562313079778905982005 14778802716851229272435813)
                ·
                  refine ⟨2771025509409605488581715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14778802716851229272435813 2771025509409605488581715)
                  ·
                    refine ⟨4156538264114408232872573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2771025509409605488581715 4156538264114408232872573)
                    ·
                      refine ⟨1558701849042903087327215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4156538264114408232872573 1558701849042903087327215)
                      ·
                        rfl

theorem cell23_3035561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_3035561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035561 prefixEnd_3035561 := by exact prefixLift 3035561
  have htrace : WordTrace (prefixWord ++ tailWord_3035561) baseStart_3035561 baseEnd_3035561 := by
    simpa [prefixWord, tailWord_3035561, baseEnd_3035561] using wordTrace_append hprefix tailTrace_3035561
  have hstable : (prefixWord ++ tailWord_3035561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035561).length < 2 ^ (prefixWord ++ tailWord_3035561).sum := by decide
  have hdescent : baseEnd_3035561 < baseStart_3035561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035584 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_3035584 : Nat := 118140960795 + 3035584 * 2 ^ 59
def prefixEnd_3035584 : Nat := 4983230072969 + 3 ^ 40 * 3035584 * 2
def baseEnd_3035584 : Nat := 1558713659097956497339609

theorem tailTrace_3035584 : CollatzResearch.WordTrace tailWord_3035584 prefixEnd_3035584 1558713659097956497339609 := by
  unfold tailWord_3035584
  simp only [CollatzResearch.WordTrace]
  refine ⟨55358422117302539658736903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73811229489736719544982537 55358422117302539658736903)
  ·
    refine ⟨83037633175953809488105355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55358422117302539658736903 83037633175953809488105355)
    ·
      refine ⟨124556449763930714232158033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83037633175953809488105355 124556449763930714232158033)
      ·
        refine ⟨93417337322948035674118525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124556449763930714232158033 93417337322948035674118525)
        ·
          refine ⟨35031501496105513377794447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93417337322948035674118525 35031501496105513377794447)
          ·
            refine ⟨52547252244158270066691671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35031501496105513377794447 52547252244158270066691671)
            ·
              refine ⟨78820878366237405100037507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52547252244158270066691671 78820878366237405100037507)
              ·
                refine ⟨118231317549356107650056261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78820878366237405100037507 118231317549356107650056261)
                ·
                  refine ⟨22168372040504270184385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118231317549356107650056261 22168372040504270184385549)
                  ·
                    refine ⟨8313139515189101319144581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22168372040504270184385549 8313139515189101319144581)
                    ·
                      refine ⟨1558713659097956497339609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8313139515189101319144581 1558713659097956497339609)
                      ·
                        rfl

theorem cell23_3035584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_3035584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035584 prefixEnd_3035584 := by exact prefixLift 3035584
  have htrace : WordTrace (prefixWord ++ tailWord_3035584) baseStart_3035584 baseEnd_3035584 := by
    simpa [prefixWord, tailWord_3035584, baseEnd_3035584] using wordTrace_append hprefix tailTrace_3035584
  have hstable : (prefixWord ++ tailWord_3035584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035584).length < 2 ^ (prefixWord ++ tailWord_3035584).sum := by decide
  have hdescent : baseEnd_3035584 < baseStart_3035584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035594 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3035594 : Nat := 118140960795 + 3035594 * 2 ^ 59
def prefixEnd_3035594 : Nat := 4983230072969 + 3 ^ 40 * 3035594 * 2
def baseEnd_3035594 : Nat := 519572931301500486071521

theorem tailTrace_3035594 : CollatzResearch.WordTrace tailWord_3035594 prefixEnd_3035594 519572931301500486071521 := by
  unfold tailWord_3035594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27679302241142212756334459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73811472643045900683558557 27679302241142212756334459)
  ·
    refine ⟨41518953361713319134501689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27679302241142212756334459 41518953361713319134501689)
    ·
      refine ⟨31139215021284989350876267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41518953361713319134501689 31139215021284989350876267)
      ·
        refine ⟨46708822531927484026314401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31139215021284989350876267 46708822531927484026314401)
        ·
          refine ⟨35031616898945613019735801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46708822531927484026314401 35031616898945613019735801)
          ·
            refine ⟨26273712674209209764801851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35031616898945613019735801 26273712674209209764801851)
            ·
              refine ⟨39410569011313814647202777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26273712674209209764801851 39410569011313814647202777)
              ·
                refine ⟨29557926758485360985402083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39410569011313814647202777 29557926758485360985402083)
                ·
                  refine ⟨44336890137728041478103125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29557926758485360985402083 44336890137728041478103125)
                  ·
                    refine ⟨519572931301500486071521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44336890137728041478103125 519572931301500486071521)
                    ·
                      rfl

theorem cell23_3035594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3035594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035594 prefixEnd_3035594 := by exact prefixLift 3035594
  have htrace : WordTrace (prefixWord ++ tailWord_3035594) baseStart_3035594 baseEnd_3035594 := by
    simpa [prefixWord, tailWord_3035594, baseEnd_3035594] using wordTrace_append hprefix tailTrace_3035594
  have hstable : (prefixWord ++ tailWord_3035594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035594).length < 2 ^ (prefixWord ++ tailWord_3035594).sum := by decide
  have hdescent : baseEnd_3035594 < baseStart_3035594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035605 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3035605 : Nat := 118140960795 + 3035605 * 2 ^ 59
def prefixEnd_3035605 : Nat := 4983230072969 + 3 ^ 40 * 3035605 * 2
def baseEnd_3035605 : Nat := 1558724442191700915177013

theorem tailTrace_3035605 : CollatzResearch.WordTrace tailWord_3035605 prefixEnd_3035605 1558724442191700915177013 := by
  unfold tailWord_3035605
  simp only [CollatzResearch.WordTrace]
  refine ⟨110717610167528999903988269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73811740111685999935992179 110717610167528999903988269)
  ·
    refine ⟨41519103812823374963995601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110717610167528999903988269 41519103812823374963995601)
    ·
      refine ⟨31139327859617531222996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41519103812823374963995601 31139327859617531222996701)
      ·
        refine ⟨11677247947356574208623763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31139327859617531222996701 11677247947356574208623763)
        ·
          refine ⟨17515871921034861312935645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677247947356574208623763 17515871921034861312935645)
          ·
            refine ⟨6568451970388072992350867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17515871921034861312935645 6568451970388072992350867)
            ·
              refine ⟨9852677955582109488526301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568451970388072992350867 9852677955582109488526301)
              ·
                refine ⟨3694754233343291058197363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9852677955582109488526301 3694754233343291058197363)
                ·
                  refine ⟨5542131350014936587296045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694754233343291058197363 5542131350014936587296045)
                  ·
                    refine ⟨2078299256255601220236017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5542131350014936587296045 2078299256255601220236017)
                    ·
                      refine ⟨1558724442191700915177013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078299256255601220236017 1558724442191700915177013)
                      ·
                        rfl

theorem cell23_3035605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3035605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035605 prefixEnd_3035605 := by exact prefixLift 3035605
  have htrace : WordTrace (prefixWord ++ tailWord_3035605) baseStart_3035605 baseEnd_3035605 := by
    simpa [prefixWord, tailWord_3035605, baseEnd_3035605] using wordTrace_append hprefix tailTrace_3035605
  have hstable : (prefixWord ++ tailWord_3035605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035605).length < 2 ^ (prefixWord ++ tailWord_3035605).sum := by decide
  have hdescent : baseEnd_3035605 < baseStart_3035605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_3035664 : Nat := 118140960795 + 3035664 * 2 ^ 59
def prefixEnd_3035664 : Nat := 4983230072969 + 3 ^ 40 * 3035664 * 2
def baseEnd_3035664 : Nat := 1558754737550316184339241

theorem tailTrace_3035664 : CollatzResearch.WordTrace tailWord_3035664 prefixEnd_3035664 1558754737550316184339241 := by
  unfold tailWord_3035664
  simp only [CollatzResearch.WordTrace]
  refine ⟨55359881037157626490193023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73813174716210168653590697 55359881037157626490193023)
  ·
    refine ⟨83039821555736439735289535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55359881037157626490193023 83039821555736439735289535)
    ·
      refine ⟨124559732333604659602934303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83039821555736439735289535 124559732333604659602934303)
      ·
        refine ⟨186839598500406989404401455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124559732333604659602934303 186839598500406989404401455)
        ·
          refine ⟨280259397750610484106602183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186839598500406989404401455 280259397750610484106602183)
          ·
            refine ⟨420389096625915726159903275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280259397750610484106602183 420389096625915726159903275)
            ·
              refine ⟨630583644938873589239854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420389096625915726159903275 630583644938873589239854913)
              ·
                refine ⟨472937733704155191929891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630583644938873589239854913 472937733704155191929891185)
                ·
                  refine ⟨354703300278116393947418389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472937733704155191929891185 354703300278116393947418389)
                  ·
                    refine ⟨16626717200536705966285237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 354703300278116393947418389 16626717200536705966285237)
                    ·
                      refine ⟨1558754737550316184339241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16626717200536705966285237 1558754737550316184339241)
                      ·
                        rfl

theorem cell23_3035664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_3035664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035664 prefixEnd_3035664 := by exact prefixLift 3035664
  have htrace : WordTrace (prefixWord ++ tailWord_3035664) baseStart_3035664 baseEnd_3035664 := by
    simpa [prefixWord, tailWord_3035664, baseEnd_3035664] using wordTrace_append hprefix tailTrace_3035664
  have hstable : (prefixWord ++ tailWord_3035664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035664).length < 2 ^ (prefixWord ++ tailWord_3035664).sum := by decide
  have hdescent : baseEnd_3035664 < baseStart_3035664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035681 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3035681 : Nat := 118140960795 + 3035681 * 2 ^ 59
def prefixEnd_3035681 : Nat := 4983230072969 + 3 ^ 40 * 3035681 * 2
def baseEnd_3035681 : Nat := 1558763466721442617826663

theorem tailTrace_3035681 : CollatzResearch.WordTrace tailWord_3035681 prefixEnd_3035681 1558763466721442617826663 := by
  unfold tailWord_3035681
  simp only [CollatzResearch.WordTrace]
  refine ⟨110720382115253664883754897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73813588076835776589169931 110720382115253664883754897)
  ·
    refine ⟨83040286586440248662816173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110720382115253664883754897 83040286586440248662816173)
    ·
      refine ⟨31140107469915093248556065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83040286586440248662816173 31140107469915093248556065)
      ·
        refine ⟨23355080602436319936417049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31140107469915093248556065 23355080602436319936417049)
        ·
          refine ⟨17516310451827239952312787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23355080602436319936417049 17516310451827239952312787)
          ·
            refine ⟨26274465677740859928469181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17516310451827239952312787 26274465677740859928469181)
            ·
              refine ⟨9852924629152822473175943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26274465677740859928469181 9852924629152822473175943)
              ·
                refine ⟨14779386943729233709763915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9852924629152822473175943 14779386943729233709763915)
                ·
                  refine ⟨22169080415593850564645873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14779386943729233709763915 22169080415593850564645873)
                  ·
                    refine ⟨16626810311695387923484405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22169080415593850564645873 16626810311695387923484405)
                    ·
                      refine ⟨1558763466721442617826663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16626810311695387923484405 1558763466721442617826663)
                      ·
                        rfl

theorem cell23_3035681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3035681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035681 prefixEnd_3035681 := by exact prefixLift 3035681
  have htrace : WordTrace (prefixWord ++ tailWord_3035681) baseStart_3035681 baseEnd_3035681 := by
    simpa [prefixWord, tailWord_3035681, baseEnd_3035681] using wordTrace_append hprefix tailTrace_3035681
  have hstable : (prefixWord ++ tailWord_3035681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035681).length < 2 ^ (prefixWord ++ tailWord_3035681).sum := by decide
  have hdescent : baseEnd_3035681 < baseStart_3035681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035708 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3035708 : Nat := 118140960795 + 3035708 * 2 ^ 59
def prefixEnd_3035708 : Nat := 4983230072969 + 3 ^ 40 * 3035708 * 2
def baseEnd_3035708 : Nat := 1558777330699114012189039

theorem tailTrace_3035708 : CollatzResearch.WordTrace tailWord_3035708 prefixEnd_3035708 1558777330699114012189039 := by
  unfold tailWord_3035708
  simp only [CollatzResearch.WordTrace]
  refine ⟨55360683443077924247493889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73814244590770565663325185 55360683443077924247493889)
  ·
    refine ⟨41520512582308443185620417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55360683443077924247493889 41520512582308443185620417)
    ·
      refine ⟨31140384436731332389215313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41520512582308443185620417 31140384436731332389215313)
      ·
        refine ⟨23355288327548499291911485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31140384436731332389215313 23355288327548499291911485)
        ·
          refine ⟨8758233122830687234466807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23355288327548499291911485 8758233122830687234466807)
          ·
            refine ⟨13137349684246030851700211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758233122830687234466807 13137349684246030851700211)
            ·
              refine ⟨19706024526369046277550317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137349684246030851700211 19706024526369046277550317)
              ·
                refine ⟨7389759197388392354081369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19706024526369046277550317 7389759197388392354081369)
                ·
                  refine ⟨5542319398041294265561027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389759197388392354081369 5542319398041294265561027)
                  ·
                    refine ⟨8313479097061941398341541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542319398041294265561027 8313479097061941398341541)
                    ·
                      refine ⟨1558777330699114012189039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8313479097061941398341541 1558777330699114012189039)
                      ·
                        rfl

theorem cell23_3035708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3035708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035708 prefixEnd_3035708 := by exact prefixLift 3035708
  have htrace : WordTrace (prefixWord ++ tailWord_3035708) baseStart_3035708 baseEnd_3035708 := by
    simpa [prefixWord, tailWord_3035708, baseEnd_3035708] using wordTrace_append hprefix tailTrace_3035708
  have hstable : (prefixWord ++ tailWord_3035708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035708).length < 2 ^ (prefixWord ++ tailWord_3035708).sum := by decide
  have hdescent : baseEnd_3035708 < baseStart_3035708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035725 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3035725 : Nat := 118140960795 + 3035725 * 2 ^ 59
def prefixEnd_3035725 : Nat := 4983230072969 + 3 ^ 40 * 3035725 * 2
def baseEnd_3035725 : Nat := 1558786059870240445676461

theorem tailTrace_3035725 : CollatzResearch.WordTrace tailWord_3035725 prefixEnd_3035725 1558786059870240445676461 := by
  unfold tailWord_3035725
  simp only [CollatzResearch.WordTrace]
  refine ⟨110721986927094260398356629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73814657951396173598904419 110721986927094260398356629)
  ·
    refine ⟨5190093137207543456172967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110721986927094260398356629 5190093137207543456172967)
    ·
      refine ⟨7785139705811315184259451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190093137207543456172967 7785139705811315184259451)
      ·
        refine ⟨11677709558716972776389177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785139705811315184259451 11677709558716972776389177)
        ·
          refine ⟨8758282169037729582291883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677709558716972776389177 8758282169037729582291883)
          ·
            refine ⟨13137423253556594373437825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758282169037729582291883 13137423253556594373437825)
            ·
              refine ⟨9853067440167445780078369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137423253556594373437825 9853067440167445780078369)
              ·
                refine ⟨7389800580125584335058777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9853067440167445780078369 7389800580125584335058777)
                ·
                  refine ⟨5542350435094188251294083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389800580125584335058777 5542350435094188251294083)
                  ·
                    refine ⟨8313525652641282376941125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542350435094188251294083 8313525652641282376941125)
                    ·
                      refine ⟨1558786059870240445676461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8313525652641282376941125 1558786059870240445676461)
                      ·
                        rfl

theorem cell23_3035725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3035725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035725 prefixEnd_3035725 := by exact prefixLift 3035725
  have htrace : WordTrace (prefixWord ++ tailWord_3035725) baseStart_3035725 baseEnd_3035725 := by
    simpa [prefixWord, tailWord_3035725, baseEnd_3035725] using wordTrace_append hprefix tailTrace_3035725
  have hstable : (prefixWord ++ tailWord_3035725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035725).length < 2 ^ (prefixWord ++ tailWord_3035725).sum := by decide
  have hdescent : baseEnd_3035725 < baseStart_3035725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035735 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 1, 4]
def baseStart_3035735 : Nat := 118140960795 + 3035735 * 2 ^ 59
def prefixEnd_3035735 : Nat := 4983230072969 + 3 ^ 40 * 3035735 * 2
def baseEnd_3035735 : Nat := 519597064892261802183805

theorem tailTrace_3035735 : CollatzResearch.WordTrace tailWord_3035735 prefixEnd_3035735 519597064892261802183805 := by
  unfold tailWord_3035735
  simp only [CollatzResearch.WordTrace]
  refine ⟨110722351657058032106220659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73814901104705354737480439 110722351657058032106220659)
  ·
    refine ⟨166083527485587048159330989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110722351657058032106220659 166083527485587048159330989)
    ·
      refine ⟨62281322807095143059749121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166083527485587048159330989 62281322807095143059749121)
      ·
        refine ⟨46710992105321357294811841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62281322807095143059749121 46710992105321357294811841)
        ·
          refine ⟨35033244078991017971108881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46710992105321357294811841 35033244078991017971108881)
          ·
            refine ⟨26274933059243263478331661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35033244078991017971108881 26274933059243263478331661)
            ·
              refine ⟨9853099897216223804374373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26274933059243263478331661 9853099897216223804374373)
              ·
                refine ⟨1847456230728041963320195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9853099897216223804374373 1847456230728041963320195)
                ·
                  refine ⟨2771184346092062944980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847456230728041963320195 2771184346092062944980293)
                  ·
                    refine ⟨519597064892261802183805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771184346092062944980293 519597064892261802183805)
                    ·
                      rfl

theorem cell23_3035735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_3035735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035735 prefixEnd_3035735 := by exact prefixLift 3035735
  have htrace : WordTrace (prefixWord ++ tailWord_3035735) baseStart_3035735 baseEnd_3035735 := by
    simpa [prefixWord, tailWord_3035735, baseEnd_3035735] using wordTrace_append hprefix tailTrace_3035735
  have hstable : (prefixWord ++ tailWord_3035735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035735).length < 2 ^ (prefixWord ++ tailWord_3035735).sum := by decide
  have hdescent : baseEnd_3035735 < baseStart_3035735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035762 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3035762 : Nat := 118140960795 + 3035762 * 2 ^ 59
def prefixEnd_3035762 : Nat := 4983230072969 + 3 ^ 40 * 3035762 * 2
def baseEnd_3035762 : Nat := 1558805058654456800913791

theorem tailTrace_3035762 : CollatzResearch.WordTrace tailWord_3035762 prefixEnd_3035762 1558805058654456800913791 := by
  unfold tailWord_3035762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680834106990053929363385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73815557618640143811635693 27680834106990053929363385)
  ·
    refine ⟨20760625580242540447022539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27680834106990053929363385 20760625580242540447022539)
    ·
      refine ⟨31140938370363810670533809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20760625580242540447022539 31140938370363810670533809)
      ·
        refine ⟨23355703777772858002900357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31140938370363810670533809 23355703777772858002900357)
        ·
          refine ⟨4379194458332410875543817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23355703777772858002900357 4379194458332410875543817)
          ·
            refine ⟨3284395843749308156657863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379194458332410875543817 3284395843749308156657863)
            ·
              refine ⟨4926593765623962234986795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284395843749308156657863 4926593765623962234986795)
              ·
                refine ⟨7389890648435943352480193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926593765623962234986795 7389890648435943352480193)
                ·
                  refine ⟨5542417986326957514360145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389890648435943352480193 5542417986326957514360145)
                  ·
                    refine ⟨4156813489745218135770109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542417986326957514360145 4156813489745218135770109)
                    ·
                      refine ⟨1558805058654456800913791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4156813489745218135770109 1558805058654456800913791)
                      ·
                        rfl

theorem cell23_3035762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3035762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035762 prefixEnd_3035762 := by exact prefixLift 3035762
  have htrace : WordTrace (prefixWord ++ tailWord_3035762) baseStart_3035762 baseEnd_3035762 := by
    simpa [prefixWord, tailWord_3035762, baseEnd_3035762] using wordTrace_append hprefix tailTrace_3035762
  have hstable : (prefixWord ++ tailWord_3035762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035762).length < 2 ^ (prefixWord ++ tailWord_3035762).sum := by decide
  have hdescent : baseEnd_3035762 < baseStart_3035762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035768 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_3035768 : Nat := 118140960795 + 3035768 * 2 ^ 59
def prefixEnd_3035768 : Nat := 4983230072969 + 3 ^ 40 * 3035768 * 2
def baseEnd_3035768 : Nat := 1558808139538383777438763

theorem tailTrace_3035768 : CollatzResearch.WordTrace tailWord_3035768 prefixEnd_3035768 1558808139538383777438763 := by
  unfold tailWord_3035768
  simp only [CollatzResearch.WordTrace]
  refine ⟨55361777632969239371085979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73815703510625652494781305 55361777632969239371085979)
  ·
    refine ⟨83042666449453859056628969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55361777632969239371085979 83042666449453859056628969)
    ·
      refine ⟨62281999837090394292471727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83042666449453859056628969 62281999837090394292471727)
      ·
        refine ⟨93422999755635591438707591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62281999837090394292471727 93422999755635591438707591)
        ·
          refine ⟨140134499633453387158061387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93422999755635591438707591 140134499633453387158061387)
          ·
            refine ⟨210201749450180080737092081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140134499633453387158061387 210201749450180080737092081)
            ·
              refine ⟨157651312087635060552819061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210201749450180080737092081 157651312087635060552819061)
              ·
                refine ⟨14779810508215786926826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157651312087635060552819061 14779810508215786926826787)
                ·
                  refine ⟨22169715762323680390240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14779810508215786926826787 22169715762323680390240181)
                  ·
                    refine ⟨2078410852717845036585017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22169715762323680390240181 2078410852717845036585017)
                    ·
                      refine ⟨1558808139538383777438763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078410852717845036585017 1558808139538383777438763)
                      ·
                        rfl

theorem cell23_3035768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_3035768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035768 prefixEnd_3035768 := by exact prefixLift 3035768
  have htrace : WordTrace (prefixWord ++ tailWord_3035768) baseStart_3035768 baseEnd_3035768 := by
    simpa [prefixWord, tailWord_3035768, baseEnd_3035768] using wordTrace_append hprefix tailTrace_3035768
  have hstable : (prefixWord ++ tailWord_3035768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035768).length < 2 ^ (prefixWord ++ tailWord_3035768).sum := by decide
  have hdescent : baseEnd_3035768 < baseStart_3035768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_3035905 : Nat := 118140960795 + 3035905 * 2 ^ 59
def prefixEnd_3035905 : Nat := 4983230072969 + 3 ^ 40 * 3035905 * 2
def baseEnd_3035905 : Nat := 1558878486388049741425633

theorem tailTrace_3035905 : CollatzResearch.WordTrace tailWord_3035905 prefixEnd_3035905 1558878486388049741425633 := by
  unfold tailWord_3035905
  simp only [CollatzResearch.WordTrace]
  refine ⟨110728552066442151139909169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73819034710961434093272779 110728552066442151139909169)
  ·
    refine ⟨83046414049831613354931877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110728552066442151139909169 83046414049831613354931877)
    ·
      refine ⟨15571202634343427504049727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83046414049831613354931877 15571202634343427504049727)
      ·
        refine ⟨23356803951515141256074591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15571202634343427504049727 23356803951515141256074591)
        ·
          refine ⟨35035205927272711884111887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23356803951515141256074591 35035205927272711884111887)
          ·
            refine ⟨52552808890909067826167831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35035205927272711884111887 52552808890909067826167831)
            ·
              refine ⟨78829213336363601739251747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52552808890909067826167831 78829213336363601739251747)
              ·
                refine ⟨118243820004545402608877621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78829213336363601739251747 118243820004545402608877621)
                ·
                  refine ⟨11085358125426131494582277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118243820004545402608877621 11085358125426131494582277)
                  ·
                    refine ⟨2078504648517399655234177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11085358125426131494582277 2078504648517399655234177)
                    ·
                      refine ⟨1558878486388049741425633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078504648517399655234177 1558878486388049741425633)
                      ·
                        rfl

theorem cell23_3035905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_3035905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035905 prefixEnd_3035905 := by exact prefixLift 3035905
  have htrace : WordTrace (prefixWord ++ tailWord_3035905) baseStart_3035905 baseEnd_3035905 := by
    simpa [prefixWord, tailWord_3035905, baseEnd_3035905] using wordTrace_append hprefix tailTrace_3035905
  have hstable : (prefixWord ++ tailWord_3035905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035905).length < 2 ^ (prefixWord ++ tailWord_3035905).sum := by decide
  have hdescent : baseEnd_3035905 < baseStart_3035905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035955 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3]
def baseStart_3035955 : Nat := 118140960795 + 3035955 * 2 ^ 59
def prefixEnd_3035955 : Nat := 4983230072969 + 3 ^ 40 * 3035955 * 2
def baseEnd_3035955 : Nat := 1558904160420774545800403

theorem tailTrace_3035955 : CollatzResearch.WordTrace tailWord_3035955 prefixEnd_3035955 1558904160420774545800403 := by
  unfold tailWord_3035955
  simp only [CollatzResearch.WordTrace]
  refine ⟨110730375716261009679229319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73820250477507339786152879 110730375716261009679229319)
  ·
    refine ⟨166095563574391514518843979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110730375716261009679229319 166095563574391514518843979)
    ·
      refine ⟨249143345361587271778265969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166095563574391514518843979 249143345361587271778265969)
      ·
        refine ⟨186857509021190453833699477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249143345361587271778265969 186857509021190453833699477)
        ·
          refine ⟨8758945735368302523454663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186857509021190453833699477 8758945735368302523454663)
          ·
            refine ⟨13138418603052453785181995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758945735368302523454663 13138418603052453785181995)
            ·
              refine ⟨19707627904578680677772993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13138418603052453785181995 19707627904578680677772993)
              ·
                refine ⟨14780720928434010508329745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19707627904578680677772993 14780720928434010508329745)
                ·
                  refine ⟨11085540696325507881247309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14780720928434010508329745 11085540696325507881247309)
                  ·
                    refine ⟨4157077761122065455467741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11085540696325507881247309 4157077761122065455467741)
                    ·
                      refine ⟨1558904160420774545800403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4157077761122065455467741 1558904160420774545800403)
                      ·
                        rfl

theorem cell23_3035955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_3035955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035955 prefixEnd_3035955 := by exact prefixLift 3035955
  have htrace : WordTrace (prefixWord ++ tailWord_3035955) baseStart_3035955 baseEnd_3035955 := by
    simpa [prefixWord, tailWord_3035955, baseEnd_3035955] using wordTrace_append hprefix tailTrace_3035955
  have hstable : (prefixWord ++ tailWord_3035955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035955).length < 2 ^ (prefixWord ++ tailWord_3035955).sum := by decide
  have hdescent : baseEnd_3035955 < baseStart_3035955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035956 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3035956 : Nat := 118140960795 + 3035956 * 2 ^ 59
def prefixEnd_3035956 : Nat := 4983230072969 + 3 ^ 40 * 3035956 * 2
def baseEnd_3035956 : Nat := 1558904673901429041887899

theorem tailTrace_3035956 : CollatzResearch.WordTrace tailWord_3035956 prefixEnd_3035956 1558904673901429041887899 := by
  unfold tailWord_3035956
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365206094628693425007861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73820274792838257900010481 55365206094628693425007861)
  ·
    refine ⟨5190488071371440008594487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55365206094628693425007861 5190488071371440008594487)
    ·
      refine ⟨7785732107057160012891731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190488071371440008594487 7785732107057160012891731)
      ·
        refine ⟨11678598160585740019337597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785732107057160012891731 11678598160585740019337597)
        ·
          refine ⟨4379474310219652507251599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678598160585740019337597 4379474310219652507251599)
          ·
            refine ⟨6569211465329478760877399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379474310219652507251599 6569211465329478760877399)
            ·
              refine ⟨9853817197994218141316099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6569211465329478760877399 9853817197994218141316099)
              ·
                refine ⟨14780725796991327211974149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9853817197994218141316099 14780725796991327211974149)
                ·
                  refine ⟨2771386086935873852245153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14780725796991327211974149 2771386086935873852245153)
                  ·
                    refine ⟨2078539565201905389183865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771386086935873852245153 2078539565201905389183865)
                    ·
                      refine ⟨1558904673901429041887899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078539565201905389183865 1558904673901429041887899)
                      ·
                        rfl

theorem cell23_3035956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3035956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035956 prefixEnd_3035956 := by exact prefixLift 3035956
  have htrace : WordTrace (prefixWord ++ tailWord_3035956) baseStart_3035956 baseEnd_3035956 := by
    simpa [prefixWord, tailWord_3035956, baseEnd_3035956] using wordTrace_append hprefix tailTrace_3035956
  have hstable : (prefixWord ++ tailWord_3035956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035956).length < 2 ^ (prefixWord ++ tailWord_3035956).sum := by decide
  have hdescent : baseEnd_3035956 < baseStart_3035956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3035968 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3035968 : Nat := 118140960795 + 3035968 * 2 ^ 59
def prefixEnd_3035968 : Nat := 4983230072969 + 3 ^ 40 * 3035968 * 2
def baseEnd_3035968 : Nat := 1558910835669282994937843

theorem tailTrace_3035968 : CollatzResearch.WordTrace tailWord_3035968 prefixEnd_3035968 1558910835669282994937843 := by
  unfold tailWord_3035968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365424932606956449726279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73820566576809275266301705 55365424932606956449726279)
  ·
    refine ⟨83048137398910434674589419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55365424932606956449726279 83048137398910434674589419)
    ·
      refine ⟨124572206098365652011884129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83048137398910434674589419 124572206098365652011884129)
      ·
        refine ⟨93429154573774239008913097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124572206098365652011884129 93429154573774239008913097)
        ·
          refine ⟨70071865930330679256684823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93429154573774239008913097 70071865930330679256684823)
          ·
            refine ⟨105107798895496018885027235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70071865930330679256684823 105107798895496018885027235)
            ·
              refine ⟨157661698343244028327540853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105107798895496018885027235 157661698343244028327540853)
              ·
                refine ⟨14780784219679127655706955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157661698343244028327540853 14780784219679127655706955)
                ·
                  refine ⟨22171176329518691483560433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780784219679127655706955 22171176329518691483560433)
                  ·
                    refine ⟨16628382247139018612670325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22171176329518691483560433 16628382247139018612670325)
                    ·
                      refine ⟨1558910835669282994937843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16628382247139018612670325 1558910835669282994937843)
                      ·
                        rfl

theorem cell23_3035968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3035968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3035968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3035968 prefixEnd_3035968 := by exact prefixLift 3035968
  have htrace : WordTrace (prefixWord ++ tailWord_3035968) baseStart_3035968 baseEnd_3035968 := by
    simpa [prefixWord, tailWord_3035968, baseEnd_3035968] using wordTrace_append hprefix tailTrace_3035968
  have hstable : (prefixWord ++ tailWord_3035968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3035968).length < 2 ^ (prefixWord ++ tailWord_3035968).sum := by decide
  have hdescent : baseEnd_3035968 < baseStart_3035968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3035968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036005 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_3036005 : Nat := 118140960795 + 3036005 * 2 ^ 59
def prefixEnd_3036005 : Nat := 4983230072969 + 3 ^ 40 * 3036005 * 2
def baseEnd_3036005 : Nat := 519643278151166450058391

theorem tailTrace_3036005 : CollatzResearch.WordTrace tailWord_3036005 prefixEnd_3036005 519643278151166450058391 := by
  unfold tailWord_3036005
  simp only [CollatzResearch.WordTrace]
  refine ⟨110732199366079868218549469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73821466244053245479032979 110732199366079868218549469)
  ·
    refine ⟨41524574762279950581956051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110732199366079868218549469 41524574762279950581956051)
    ·
      refine ⟨62286862143419925872934077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41524574762279950581956051 62286862143419925872934077)
      ·
        refine ⟨23357573303782472202350279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62286862143419925872934077 23357573303782472202350279)
        ·
          refine ⟨35036359955673708303525419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23357573303782472202350279 35036359955673708303525419)
          ·
            refine ⟨52554539933510562455288129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35036359955673708303525419 52554539933510562455288129)
            ·
              refine ⟨39415904950132921841466097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52554539933510562455288129 39415904950132921841466097)
              ·
                refine ⟨29561928712599691381099573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39415904950132921841466097 29561928712599691381099573)
                ·
                  refine ⟨2771430816806221066978085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29561928712599691381099573 2771430816806221066978085)
                  ·
                    refine ⟨519643278151166450058391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2771430816806221066978085 519643278151166450058391)
                    ·
                      rfl

theorem cell23_3036005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_3036005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036005 prefixEnd_3036005 := by exact prefixLift 3036005
  have htrace : WordTrace (prefixWord ++ tailWord_3036005) baseStart_3036005 baseEnd_3036005 := by
    simpa [prefixWord, tailWord_3036005, baseEnd_3036005] using wordTrace_append hprefix tailTrace_3036005
  have hstable : (prefixWord ++ tailWord_3036005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036005).length < 2 ^ (prefixWord ++ tailWord_3036005).sum := by decide
  have hdescent : baseEnd_3036005 < baseStart_3036005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036035 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 6]
def baseStart_3036035 : Nat := 118140960795 + 3036035 * 2 ^ 59
def prefixEnd_3036035 : Nat := 4983230072969 + 3 ^ 40 * 3036035 * 2
def baseEnd_3036035 : Nat := 173216137652570470311115

theorem tailTrace_3036035 : CollatzResearch.WordTrace tailWord_3036035 prefixEnd_3036035 173216137652570470311115 := by
  unfold tailWord_3036035
  simp only [CollatzResearch.WordTrace]
  refine ⟨110733293555971183342141559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73822195703980788894761039 110733293555971183342141559)
  ·
    refine ⟨166099940333956775013212339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110733293555971183342141559 166099940333956775013212339)
    ·
      refine ⟨249149910500935162519818509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166099940333956775013212339 249149910500935162519818509)
      ·
        refine ⟨93431216437850685944931941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249149910500935162519818509 93431216437850685944931941)
        ·
          refine ⟨17518353082097003614674739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93431216437850685944931941 17518353082097003614674739)
          ·
            refine ⟨26277529623145505422012109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17518353082097003614674739 26277529623145505422012109)
            ·
              refine ⟨9854073608679564533254541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26277529623145505422012109 9854073608679564533254541)
              ·
                refine ⟨3695277603254836699970453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9854073608679564533254541 3695277603254836699970453)
                ·
                  refine ⟨173216137652570470311115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3695277603254836699970453 173216137652570470311115)
                  ·
                    rfl

theorem cell23_3036035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 6].length) (baseStart_3036035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036035 prefixEnd_3036035 := by exact prefixLift 3036035
  have htrace : WordTrace (prefixWord ++ tailWord_3036035) baseStart_3036035 baseEnd_3036035 := by
    simpa [prefixWord, tailWord_3036035, baseEnd_3036035] using wordTrace_append hprefix tailTrace_3036035
  have hstable : (prefixWord ++ tailWord_3036035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036035).length < 2 ^ (prefixWord ++ tailWord_3036035).sum := by decide
  have hdescent : baseEnd_3036035 < baseStart_3036035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036116 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3036116 : Nat := 118140960795 + 3036116 * 2 ^ 59
def prefixEnd_3036116 : Nat := 4983230072969 + 3 ^ 40 * 3036116 * 2
def baseEnd_3036116 : Nat := 519662276935382805295721

theorem tailTrace_3036116 : CollatzResearch.WordTrace tailWord_3036116 prefixEnd_3036116 519662276935382805295721 := by
  unfold tailWord_3036116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55368123934338867087920101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73824165245785156117226801 55368123934338867087920101)
  ·
    refine ⟨10381523237688537578985019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55368123934338867087920101 10381523237688537578985019)
    ·
      refine ⟨15572284856532806368477529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10381523237688537578985019 15572284856532806368477529)
      ·
        refine ⟨11679213642399604776358147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15572284856532806368477529 11679213642399604776358147)
        ·
          refine ⟨17518820463599407164537221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11679213642399604776358147 17518820463599407164537221)
          ·
            refine ⟨3284778836924888843350729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17518820463599407164537221 3284778836924888843350729)
            ·
              refine ⟨2463584127693666632513047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284778836924888843350729 2463584127693666632513047)
              ·
                refine ⟨3695376191540499948769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463584127693666632513047 3695376191540499948769571)
                ·
                  refine ⟨5543064287310749923154357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695376191540499948769571 5543064287310749923154357)
                  ·
                    refine ⟨519662276935382805295721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5543064287310749923154357 519662276935382805295721)
                    ·
                      rfl

theorem cell23_3036116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3036116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036116 prefixEnd_3036116 := by exact prefixLift 3036116
  have htrace : WordTrace (prefixWord ++ tailWord_3036116) baseStart_3036116 baseEnd_3036116 := by
    simpa [prefixWord, tailWord_3036116, baseEnd_3036116] using wordTrace_append hprefix tailTrace_3036116
  have hstable : (prefixWord ++ tailWord_3036116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036116).length < 2 ^ (prefixWord ++ tailWord_3036116).sum := by decide
  have hdescent : baseEnd_3036116 < baseStart_3036116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036146 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3036146 : Nat := 118140960795 + 3036146 * 2 ^ 59
def prefixEnd_3036146 : Nat := 4983230072969 + 3 ^ 40 * 3036146 * 2
def baseEnd_3036146 : Nat := 519667411741927766170675

theorem tailTrace_3036146 : CollatzResearch.WordTrace tailWord_3036146 prefixEnd_3036146 519667411741927766170675 := by
  unfold tailWord_3036146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27684335514642262324858073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73824894705712699532954861 27684335514642262324858073)
  ·
    refine ⟨20763251635981696743643555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27684335514642262324858073 20763251635981696743643555)
    ·
      refine ⟨31144877453972545115465333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20763251635981696743643555 31144877453972545115465333)
      ·
        refine ⟨2919832261309926104574875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31144877453972545115465333 2919832261309926104574875)
        ·
          refine ⟨4379748391964889156862313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919832261309926104574875 4379748391964889156862313)
          ·
            refine ⟨3284811293973666867646735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379748391964889156862313 3284811293973666867646735)
            ·
              refine ⟨4927216940960500301470103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284811293973666867646735 4927216940960500301470103)
              ·
                refine ⟨7390825411440750452205155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927216940960500301470103 7390825411440750452205155)
                ·
                  refine ⟨11086238117161125678307733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390825411440750452205155 11086238117161125678307733)
                  ·
                    refine ⟨519667411741927766170675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11086238117161125678307733 519667411741927766170675)
                    ·
                      rfl

theorem cell23_3036146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3036146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036146 prefixEnd_3036146 := by exact prefixLift 3036146
  have htrace : WordTrace (prefixWord ++ tailWord_3036146) baseStart_3036146 baseEnd_3036146 := by
    simpa [prefixWord, tailWord_3036146, baseEnd_3036146] using wordTrace_append hprefix tailTrace_3036146
  have hstable : (prefixWord ++ tailWord_3036146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036146).length < 2 ^ (prefixWord ++ tailWord_3036146).sum := by decide
  have hdescent : baseEnd_3036146 < baseStart_3036146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036165 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_3036165 : Nat := 118140960795 + 3036165 * 2 ^ 59
def prefixEnd_3036165 : Nat := 4983230072969 + 3 ^ 40 * 3036165 * 2
def baseEnd_3036165 : Nat := 1559011991358218724174437

theorem tailTrace_3036165 : CollatzResearch.WordTrace tailWord_3036165 prefixEnd_3036165 1559011991358218724174437 := by
  unfold tailWord_3036165
  simp only [CollatzResearch.WordTrace]
  refine ⟨110738035045500215544373949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73825356697000143696249299 110738035045500215544373949)
  ·
    refine ⟨41526763142062580829140231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110738035045500215544373949 41526763142062580829140231)
    ·
      refine ⟨62290144713093871243710347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41526763142062580829140231 62290144713093871243710347)
      ·
        refine ⟨93435217069640806865565521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62290144713093871243710347 93435217069640806865565521)
        ·
          refine ⟨70076412802230605149174141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93435217069640806865565521 70076412802230605149174141)
          ·
            refine ⟨26278654800836476930940303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70076412802230605149174141 26278654800836476930940303)
            ·
              refine ⟨39417982201254715396410455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26278654800836476930940303 39417982201254715396410455)
              ·
                refine ⟨59126973301882073094615683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39417982201254715396410455 59126973301882073094615683)
                ·
                  refine ⟨88690459952823109641923525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59126973301882073094615683 88690459952823109641923525)
                  ·
                    refine ⟨16629461241154333057860661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88690459952823109641923525 16629461241154333057860661)
                    ·
                      refine ⟨1559011991358218724174437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16629461241154333057860661 1559011991358218724174437)
                      ·
                        rfl

theorem cell23_3036165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_3036165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036165 prefixEnd_3036165 := by exact prefixLift 3036165
  have htrace : WordTrace (prefixWord ++ tailWord_3036165) baseStart_3036165 baseEnd_3036165 := by
    simpa [prefixWord, tailWord_3036165, baseEnd_3036165] using wordTrace_append hprefix tailTrace_3036165
  have hstable : (prefixWord ++ tailWord_3036165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036165).length < 2 ^ (prefixWord ++ tailWord_3036165).sum := by decide
  have hdescent : baseEnd_3036165 < baseStart_3036165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036170 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3036170 : Nat := 118140960795 + 3036170 * 2 ^ 59
def prefixEnd_3036170 : Nat := 4983230072969 + 3 ^ 40 * 3036170 * 2
def baseEnd_3036170 : Nat := 1559014558761491204611915

theorem tailTrace_3036170 : CollatzResearch.WordTrace tailWord_3036170 prefixEnd_3036170 1559014558761491204611915 := by
  unfold tailWord_3036170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27684554352620525349576491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73825478273654734265537309 27684554352620525349576491)
  ·
    refine ⟨41526831528930788024364737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27684554352620525349576491 41526831528930788024364737)
    ·
      refine ⟨31145123646698091018273553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41526831528930788024364737 31145123646698091018273553)
      ·
        refine ⟨23358842735023568263705165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31145123646698091018273553 23358842735023568263705165)
        ·
          refine ⟨8759566025633838098889437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23358842735023568263705165 8759566025633838098889437)
          ·
            refine ⟨3284837259612689287083539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8759566025633838098889437 3284837259612689287083539)
            ·
              refine ⟨4927255889419033930625309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284837259612689287083539 4927255889419033930625309)
              ·
                refine ⟨1847720958532137723984491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4927255889419033930625309 1847720958532137723984491)
                ·
                  refine ⟨2771581437798206585976737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847720958532137723984491 2771581437798206585976737)
                  ·
                    refine ⟨2078686078348654939482553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771581437798206585976737 2078686078348654939482553)
                    ·
                      refine ⟨1559014558761491204611915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078686078348654939482553 1559014558761491204611915)
                      ·
                        rfl

theorem cell23_3036170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3036170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036170 prefixEnd_3036170 := by exact prefixLift 3036170
  have htrace : WordTrace (prefixWord ++ tailWord_3036170) baseStart_3036170 baseEnd_3036170 := by
    simpa [prefixWord, tailWord_3036170, baseEnd_3036170] using wordTrace_append hprefix tailTrace_3036170
  have hstable : (prefixWord ++ tailWord_3036170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036170).length < 2 ^ (prefixWord ++ tailWord_3036170).sum := by decide
  have hdescent : baseEnd_3036170 < baseStart_3036170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036175 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_3036175 : Nat := 118140960795 + 3036175 * 2 ^ 59
def prefixEnd_3036175 : Nat := 4983230072969 + 3 ^ 40 * 3036175 * 2
def baseEnd_3036175 : Nat := 1559017126164763685049391

theorem tailTrace_3036175 : CollatzResearch.WordTrace tailWord_3036175 prefixEnd_3036175 1559017126164763685049391 := by
  unfold tailWord_3036175
  simp only [CollatzResearch.WordTrace]
  refine ⟨110738399775463987252237979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73825599850309324834825319 110738399775463987252237979)
  ·
    refine ⟨166107599663195980878356969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110738399775463987252237979 166107599663195980878356969)
    ·
      refine ⟨124580699747396985658767727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166107599663195980878356969 124580699747396985658767727)
      ·
        refine ⟨186871049621095478488151591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124580699747396985658767727 186871049621095478488151591)
        ·
          refine ⟨280306574431643217732227387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186871049621095478488151591 280306574431643217732227387)
          ·
            refine ⟨420459861647464826598341081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280306574431643217732227387 420459861647464826598341081)
            ·
              refine ⟨315344896235598619948755811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420459861647464826598341081 315344896235598619948755811)
              ·
                refine ⟨473017344353397929923133717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315344896235598619948755811 473017344353397929923133717)
                ·
                  refine ⟨22172688016565527965146893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 473017344353397929923133717 22172688016565527965146893)
                  ·
                    refine ⟨8314758006212072986930085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22172688016565527965146893 8314758006212072986930085)
                    ·
                      refine ⟨1559017126164763685049391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8314758006212072986930085 1559017126164763685049391)
                      ·
                        rfl

theorem cell23_3036175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_3036175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036175 prefixEnd_3036175 := by exact prefixLift 3036175
  have htrace : WordTrace (prefixWord ++ tailWord_3036175) baseStart_3036175 baseEnd_3036175 := by
    simpa [prefixWord, tailWord_3036175, baseEnd_3036175] using wordTrace_append hprefix tailTrace_3036175
  have hstable : (prefixWord ++ tailWord_3036175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036175).length < 2 ^ (prefixWord ++ tailWord_3036175).sum := by decide
  have hdescent : baseEnd_3036175 < baseStart_3036175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036185 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_3036185 : Nat := 118140960795 + 3036185 * 2 ^ 59
def prefixEnd_3036185 : Nat := 4983230072969 + 3 ^ 40 * 3036185 * 2
def baseEnd_3036185 : Nat := 519674086990436215308115

theorem tailTrace_3036185 : CollatzResearch.WordTrace tailWord_3036185 prefixEnd_3036185 519674086990436215308115 := by
  unfold tailWord_3036185
  simp only [CollatzResearch.WordTrace]
  refine ⟨110738764505427758960102009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73825843003618505973401339 110738764505427758960102009)
  ·
    refine ⟨83054073379070819220076507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110738764505427758960102009 83054073379070819220076507)
    ·
      refine ⟨124581110068606228830114761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83054073379070819220076507 124581110068606228830114761)
      ·
        refine ⟨93435832551454671622586071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124581110068606228830114761 93435832551454671622586071)
        ·
          refine ⟨140153748827182007433879107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93435832551454671622586071 140153748827182007433879107)
          ·
            refine ⟨210230623240773011150818661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140153748827182007433879107 210230623240773011150818661)
            ·
              refine ⟨39418241857644939590778499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210230623240773011150818661 39418241857644939590778499)
              ·
                refine ⟨59127362786467409386167749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39418241857644939590778499 59127362786467409386167749)
                ·
                  refine ⟨11086380522462639259906453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59127362786467409386167749 11086380522462639259906453)
                  ·
                    refine ⟨519674086990436215308115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11086380522462639259906453 519674086990436215308115)
                    ·
                      rfl

theorem cell23_3036185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_3036185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036185 prefixEnd_3036185 := by exact prefixLift 3036185
  have htrace : WordTrace (prefixWord ++ tailWord_3036185) baseStart_3036185 baseEnd_3036185 := by
    simpa [prefixWord, tailWord_3036185, baseEnd_3036185] using wordTrace_append hprefix tailTrace_3036185
  have hstable : (prefixWord ++ tailWord_3036185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036185).length < 2 ^ (prefixWord ++ tailWord_3036185).sum := by decide
  have hdescent : baseEnd_3036185 < baseStart_3036185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036209 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_3036209 : Nat := 118140960795 + 3036209 * 2 ^ 59
def prefixEnd_3036209 : Nat := 4983230072969 + 3 ^ 40 * 3036209 * 2
def baseEnd_3036209 : Nat := 1559034584507016552024235

theorem tailTrace_3036209 : CollatzResearch.WordTrace tailWord_3036209 prefixEnd_3036209 1559034584507016552024235 := by
  unfold tailWord_3036209
  simp only [CollatzResearch.WordTrace]
  refine ⟨110739639857340811058975681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73826426571560540705983787 110739639857340811058975681)
  ·
    refine ⟨83054729893005608294231761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110739639857340811058975681 83054729893005608294231761)
    ·
      refine ⟨62291047419754206220673821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83054729893005608294231761 62291047419754206220673821)
      ·
        refine ⟨23359142782407827332752683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62291047419754206220673821 23359142782407827332752683)
        ·
          refine ⟨35038714173611740999129025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23359142782407827332752683 35038714173611740999129025)
          ·
            refine ⟨26279035630208805749346769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35038714173611740999129025 26279035630208805749346769)
            ·
              refine ⟨19709276722656604312010077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26279035630208805749346769 19709276722656604312010077)
              ·
                refine ⟨7390978770996226617003779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19709276722656604312010077 7390978770996226617003779)
                ·
                  refine ⟨11086468156494339925505669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390978770996226617003779 11086468156494339925505669)
                  ·
                    refine ⟨2078712779342688736032313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11086468156494339925505669 2078712779342688736032313)
                    ·
                      refine ⟨1559034584507016552024235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078712779342688736032313 1559034584507016552024235)
                      ·
                        rfl

theorem cell23_3036209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_3036209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036209 prefixEnd_3036209 := by exact prefixLift 3036209
  have htrace : WordTrace (prefixWord ++ tailWord_3036209) baseStart_3036209 baseEnd_3036209 := by
    simpa [prefixWord, tailWord_3036209, baseEnd_3036209] using wordTrace_append hprefix tailTrace_3036209
  have hstable : (prefixWord ++ tailWord_3036209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036209).length < 2 ^ (prefixWord ++ tailWord_3036209).sum := by decide
  have hdescent : baseEnd_3036209 < baseStart_3036209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036215 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 9]
def baseStart_3036215 : Nat := 118140960795 + 3036215 * 2 ^ 59
def prefixEnd_3036215 : Nat := 4983230072969 + 3 ^ 40 * 3036215 * 2
def baseEnd_3036215 : Nat := 173226407265660392061023

theorem tailTrace_3036215 : CollatzResearch.WordTrace tailWord_3036215 prefixEnd_3036215 173226407265660392061023 := by
  unfold tailWord_3036215
  simp only [CollatzResearch.WordTrace]
  refine ⟨110739858695319074083694099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73826572463546049389129399 110739858695319074083694099)
  ·
    refine ⟨166109788042978611125541149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110739858695319074083694099 166109788042978611125541149)
    ·
      refine ⟨62291170516116979172077931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166109788042978611125541149 62291170516116979172077931)
      ·
        refine ⟨93436755774175468758116897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62291170516116979172077931 93436755774175468758116897)
        ·
          refine ⟨70077566830631601568587673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93436755774175468758116897 70077566830631601568587673)
          ·
            refine ⟨52558175122973701176440755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70077566830631601568587673 52558175122973701176440755)
            ·
              refine ⟨78837262684460551764661133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52558175122973701176440755 78837262684460551764661133)
              ·
                refine ⟨29563973506672706911747925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78837262684460551764661133 29563973506672706911747925)
                ·
                  refine ⟨173226407265660392061023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29563973506672706911747925 173226407265660392061023)
                  ·
                    rfl

theorem cell23_3036215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 9].length) (baseStart_3036215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036215 prefixEnd_3036215 := by exact prefixLift 3036215
  have htrace : WordTrace (prefixWord ++ tailWord_3036215) baseStart_3036215 baseEnd_3036215 := by
    simpa [prefixWord, tailWord_3036215, baseEnd_3036215] using wordTrace_append hprefix tailTrace_3036215
  have hstable : (prefixWord ++ tailWord_3036215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036215).length < 2 ^ (prefixWord ++ tailWord_3036215).sum := by decide
  have hdescent : baseEnd_3036215 < baseStart_3036215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036235 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_3036235 : Nat := 118140960795 + 3036235 * 2 ^ 59
def prefixEnd_3036235 : Nat := 4983230072969 + 3 ^ 40 * 3036235 * 2
def baseEnd_3036235 : Nat := 1559047935004033450299115

theorem tailTrace_3036235 : CollatzResearch.WordTrace tailWord_3036235 prefixEnd_3036235 1559047935004033450299115 := by
  unfold tailWord_3036235
  simp only [CollatzResearch.WordTrace]
  refine ⟨110740588155246617499422159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73827058770164411666281439 110740588155246617499422159)
  ·
    refine ⟨166110882232869926249133239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110740588155246617499422159 166110882232869926249133239)
    ·
      refine ⟨249166323349304889373699859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166110882232869926249133239 249166323349304889373699859)
      ·
        refine ⟨373749485023957334060549789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249166323349304889373699859 373749485023957334060549789)
        ·
          refine ⟨140156056883984000272706171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373749485023957334060549789 140156056883984000272706171)
          ·
            refine ⟨210234085325976000409059257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140156056883984000272706171 210234085325976000409059257)
            ·
              refine ⟨157675563994482000306794443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210234085325976000409059257 157675563994482000306794443)
              ·
                refine ⟨236513345991723000460191665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157675563994482000306794443 236513345991723000460191665)
                ·
                  refine ⟨177385009493792250345143749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236513345991723000460191665 177385009493792250345143749)
                  ·
                    refine ⟨33259689280086046939714453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177385009493792250345143749 33259689280086046939714453)
                    ·
                      refine ⟨1559047935004033450299115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33259689280086046939714453 1559047935004033450299115)
                      ·
                        rfl

theorem cell23_3036235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_3036235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036235 prefixEnd_3036235 := by exact prefixLift 3036235
  have htrace : WordTrace (prefixWord ++ tailWord_3036235) baseStart_3036235 baseEnd_3036235 := by
    simpa [prefixWord, tailWord_3036235, baseEnd_3036235] using wordTrace_append hprefix tailTrace_3036235
  have hstable : (prefixWord ++ tailWord_3036235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036235).length < 2 ^ (prefixWord ++ tailWord_3036235).sum := by decide
  have hdescent : baseEnd_3036235 < baseStart_3036235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036316 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3036316 : Nat := 118140960795 + 3036316 * 2 ^ 59
def prefixEnd_3036316 : Nat := 4983230072969 + 3 ^ 40 * 3036316 * 2
def baseEnd_3036316 : Nat := 1559089526937047633386243

theorem tailTrace_3036316 : CollatzResearch.WordTrace tailWord_3036316 prefixEnd_3036316 1559089526937047633386243 := by
  unfold tailWord_3036316
  simp only [CollatzResearch.WordTrace]
  refine ⟨55371771233976584166560401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73829028311968778888747201 55371771233976584166560401)
  ·
    refine ⟨41528828425482438124920301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55371771233976584166560401 41528828425482438124920301)
    ·
      refine ⟨15573310659555914296845113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41528828425482438124920301 15573310659555914296845113)
      ·
        refine ⟨11679982994666935722633835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15573310659555914296845113 11679982994666935722633835)
        ·
          refine ⟨17519974492000403583950753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11679982994666935722633835 17519974492000403583950753)
          ·
            refine ⟨13139980869000302687963065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17519974492000403583950753 13139980869000302687963065)
            ·
              refine ⟨9854985651750227015972299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139980869000302687963065 9854985651750227015972299)
              ·
                refine ⟨14782478477625340523958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9854985651750227015972299 14782478477625340523958449)
                ·
                  refine ⟨11086858858219005392968837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14782478477625340523958449 11086858858219005392968837)
                  ·
                    refine ⟨2078786035916063511181657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11086858858219005392968837 2078786035916063511181657)
                    ·
                      refine ⟨1559089526937047633386243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078786035916063511181657 1559089526937047633386243)
                      ·
                        rfl

theorem cell23_3036316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3036316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036316 prefixEnd_3036316 := by exact prefixLift 3036316
  have htrace : WordTrace (prefixWord ++ tailWord_3036316) baseStart_3036316 baseEnd_3036316 := by
    simpa [prefixWord, tailWord_3036316, baseEnd_3036316] using wordTrace_append hprefix tailTrace_3036316
  have hstable : (prefixWord ++ tailWord_3036316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036316).length < 2 ^ (prefixWord ++ tailWord_3036316).sum := by decide
  have hdescent : baseEnd_3036316 < baseStart_3036316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036353 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3036353 : Nat := 118140960795 + 3036353 * 2 ^ 59
def prefixEnd_3036353 : Nat := 4983230072969 + 3 ^ 40 * 3036353 * 2
def baseEnd_3036353 : Nat := 1559108525721263988623573

theorem tailTrace_3036353 : CollatzResearch.WordTrace tailWord_3036353 prefixEnd_3036353 1559108525721263988623573 := by
  unfold tailWord_3036353
  simp only [CollatzResearch.WordTrace]
  refine ⟨110744891968819123652217713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73829927979212749101478475 110744891968819123652217713)
  ·
    refine ⟨83058668976614342739163285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110744891968819123652217713 83058668976614342739163285)
    ·
      refine ⟨3893375108278797315898279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83058668976614342739163285 3893375108278797315898279)
      ·
        refine ⟨5840062662418195973847419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893375108278797315898279 5840062662418195973847419)
        ·
          refine ⟨8760093993627293960771129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840062662418195973847419 8760093993627293960771129)
          ·
            refine ⟨6570070495220470470578347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8760093993627293960771129 6570070495220470470578347)
            ·
              refine ⟨9855105742830705705867521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570070495220470470578347 9855105742830705705867521)
              ·
                refine ⟨7391329307123029279400641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855105742830705705867521 7391329307123029279400641)
                ·
                  refine ⟨5543496980342271959550481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391329307123029279400641 5543496980342271959550481)
                  ·
                    refine ⟨4157622735256703969662861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543496980342271959550481 4157622735256703969662861)
                    ·
                      refine ⟨1559108525721263988623573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4157622735256703969662861 1559108525721263988623573)
                      ·
                        rfl

theorem cell23_3036353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3036353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036353 prefixEnd_3036353 := by exact prefixLift 3036353
  have htrace : WordTrace (prefixWord ++ tailWord_3036353) baseStart_3036353 baseEnd_3036353 := by
    simpa [prefixWord, tailWord_3036353, baseEnd_3036353] using wordTrace_append hprefix tailTrace_3036353
  have hstable : (prefixWord ++ tailWord_3036353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036353).length < 2 ^ (prefixWord ++ tailWord_3036353).sum := by decide
  have hdescent : baseEnd_3036353 < baseStart_3036353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036373 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 6]
def baseStart_3036373 : Nat := 118140960795 + 3036373 * 2 ^ 59
def prefixEnd_3036373 : Nat := 4983230072969 + 3 ^ 40 * 3036373 * 2
def baseEnd_3036373 : Nat := 173235421703817101152609

theorem tailTrace_3036373 : CollatzResearch.WordTrace tailWord_3036373 prefixEnd_3036373 173235421703817101152609 := by
  unfold tailWord_3036373
  simp only [CollatzResearch.WordTrace]
  refine ⟨110745621428746667067945773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73830414285831111378630515 110745621428746667067945773)
  ·
    refine ⟨41529608035780000150479665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110745621428746667067945773 41529608035780000150479665)
    ·
      refine ⟨31147206026835000112859749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41529608035780000150479665 31147206026835000112859749)
      ·
        refine ⟨5840101130031562521161203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31147206026835000112859749 5840101130031562521161203)
        ·
          refine ⟨8760151695047343781741805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840101130031562521161203 8760151695047343781741805)
          ·
            refine ⟨3285056885642753918153177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8760151695047343781741805 3285056885642753918153177)
            ·
              refine ⟨2463792664232065438614883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285056885642753918153177 2463792664232065438614883)
              ·
                refine ⟨3695688996348098157922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463792664232065438614883 3695688996348098157922325)
                ·
                  refine ⟨173235421703817101152609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3695688996348098157922325 173235421703817101152609)
                  ·
                    rfl

theorem cell23_3036373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_3036373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036373 prefixEnd_3036373 := by exact prefixLift 3036373
  have htrace : WordTrace (prefixWord ++ tailWord_3036373) baseStart_3036373 baseEnd_3036373 := by
    simpa [prefixWord, tailWord_3036373, baseEnd_3036373] using wordTrace_append hprefix tailTrace_3036373
  have hstable : (prefixWord ++ tailWord_3036373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036373).length < 2 ^ (prefixWord ++ tailWord_3036373).sum := by decide
  have hdescent : baseEnd_3036373 < baseStart_3036373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036412 : List Nat := [2, 2, 2, 1, 16]
def baseStart_3036412 : Nat := 118140960795 + 3036412 * 2 ^ 59
def prefixEnd_3036412 : Nat := 4983230072969 + 3 ^ 40 * 3036412 * 2
def baseEnd_3036412 : Nat := 2138736380082138899569

theorem tailTrace_3036412 : CollatzResearch.WordTrace tailWord_3036412 prefixEnd_3036412 2138736380082138899569 := by
  unfold tailWord_3036412
  simp only [CollatzResearch.WordTrace]
  refine ⟨55373521937802688364307745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73831362583736917819076993 55373521937802688364307745)
  ·
    refine ⟨41530141453352016273230809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55373521937802688364307745 41530141453352016273230809)
    ·
      refine ⟨31147606090014012204923107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41530141453352016273230809 31147606090014012204923107)
      ·
        refine ⟨46721409135021018307384661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31147606090014012204923107 46721409135021018307384661)
        ·
          refine ⟨2138736380082138899569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 46721409135021018307384661 2138736380082138899569)
          ·
            rfl

theorem cell23_3036412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 16].length) (baseStart_3036412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036412 prefixEnd_3036412 := by exact prefixLift 3036412
  have htrace : WordTrace (prefixWord ++ tailWord_3036412) baseStart_3036412 baseEnd_3036412 := by
    simpa [prefixWord, tailWord_3036412, baseEnd_3036412] using wordTrace_append hprefix tailTrace_3036412
  have hstable : (prefixWord ++ tailWord_3036412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036412).length < 2 ^ (prefixWord ++ tailWord_3036412).sum := by decide
  have hdescent : baseEnd_3036412 < baseStart_3036412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036417 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_3036417 : Nat := 118140960795 + 3036417 * 2 ^ 59
def prefixEnd_3036417 : Nat := 4983230072969 + 3 ^ 40 * 3036417 * 2
def baseEnd_3036417 : Nat := 1559141388483151738223279

theorem tailTrace_3036417 : CollatzResearch.WordTrace tailWord_3036417 prefixEnd_3036417 1559141388483151738223279 := by
  unfold tailWord_3036417
  simp only [CollatzResearch.WordTrace]
  refine ⟨110747226240587262582547505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73831484160391508388365003 110747226240587262582547505)
  ·
    refine ⟨83060419680440446936910629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110747226240587262582547505 83060419680440446936910629)
    ·
      refine ⟨15573828690082583800670743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83060419680440446936910629 15573828690082583800670743)
      ·
        refine ⟨23360743035123875701006115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573828690082583800670743 23360743035123875701006115)
        ·
          refine ⟨35041114552685813551509173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360743035123875701006115 35041114552685813551509173)
          ·
            refine ⟨3285104489314295020453985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35041114552685813551509173 3285104489314295020453985)
            ·
              refine ⟨2463828366985721265340489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285104489314295020453985 2463828366985721265340489)
              ·
                refine ⟨1847871275239290949005367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463828366985721265340489 1847871275239290949005367)
                ·
                  refine ⟨2771806912858936423508051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847871275239290949005367 2771806912858936423508051)
                  ·
                    refine ⟨4157710369288404635262077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2771806912858936423508051 4157710369288404635262077)
                    ·
                      refine ⟨1559141388483151738223279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4157710369288404635262077 1559141388483151738223279)
                      ·
                        rfl

theorem cell23_3036417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_3036417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036417 prefixEnd_3036417 := by exact prefixLift 3036417
  have htrace : WordTrace (prefixWord ++ tailWord_3036417) baseStart_3036417 baseEnd_3036417 := by
    simpa [prefixWord, tailWord_3036417, baseEnd_3036417] using wordTrace_append hprefix tailTrace_3036417
  have hstable : (prefixWord ++ tailWord_3036417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036417).length < 2 ^ (prefixWord ++ tailWord_3036417).sum := by decide
  have hdescent : baseEnd_3036417 < baseStart_3036417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036489 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_3036489 : Nat := 118140960795 + 3036489 * 2 ^ 59
def prefixEnd_3036489 : Nat := 4983230072969 + 3 ^ 40 * 3036489 * 2
def baseEnd_3036489 : Nat := 519726119696758485507649

theorem tailTrace_3036489 : CollatzResearch.WordTrace tailWord_3036489 prefixEnd_3036489 519726119696758485507649 := by
  unfold tailWord_3036489
  simp only [CollatzResearch.WordTrace]
  refine ⟨110749852296326418879168521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73833234864217612586112347 110749852296326418879168521)
  ·
    refine ⟨83062389222244814159376391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110749852296326418879168521 83062389222244814159376391)
    ·
      refine ⟨124593583833367221239064587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83062389222244814159376391 124593583833367221239064587)
      ·
        refine ⟨186890375750050831858596881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124593583833367221239064587 186890375750050831858596881)
        ·
          refine ⟨140167781812538123893947661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186890375750050831858596881 140167781812538123893947661)
          ·
            refine ⟨52562918179701796460230373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140167781812538123893947661 52562918179701796460230373)
            ·
              refine ⟨9855547158694086836293195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52562918179701796460230373 9855547158694086836293195)
              ·
                refine ⟨14783320738041130254439793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855547158694086836293195 14783320738041130254439793)
                ·
                  refine ⟨11087490553530847690829845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14783320738041130254439793 11087490553530847690829845)
                  ·
                    refine ⟨519726119696758485507649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11087490553530847690829845 519726119696758485507649)
                    ·
                      rfl

theorem cell23_3036489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_3036489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036489 prefixEnd_3036489 := by exact prefixLift 3036489
  have htrace : WordTrace (prefixWord ++ tailWord_3036489) baseStart_3036489 baseEnd_3036489 := by
    simpa [prefixWord, tailWord_3036489, baseEnd_3036489] using wordTrace_append hprefix tailTrace_3036489
  have hstable : (prefixWord ++ tailWord_3036489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036489).length < 2 ^ (prefixWord ++ tailWord_3036489).sum := by decide
  have hdescent : baseEnd_3036489 < baseStart_3036489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036499 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_3036499 : Nat := 118140960795 + 3036499 * 2 ^ 59
def prefixEnd_3036499 : Nat := 4983230072969 + 3 ^ 40 * 3036499 * 2
def baseEnd_3036499 : Nat := 1559183493896820417397901

theorem tailTrace_3036499 : CollatzResearch.WordTrace tailWord_3036499 prefixEnd_3036499 1559183493896820417397901 := by
  unfold tailWord_3036499
  simp only [CollatzResearch.WordTrace]
  refine ⟨110750217026290190587032551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73833478017526793724688367 110750217026290190587032551)
  ·
    refine ⟨166125325539435285880548827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110750217026290190587032551 166125325539435285880548827)
    ·
      refine ⟨249187988309152928820823241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166125325539435285880548827 249187988309152928820823241)
      ·
        refine ⟨186890991231864696615617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249187988309152928820823241 186890991231864696615617431)
        ·
          refine ⟨280336486847797044923426147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186890991231864696615617431 280336486847797044923426147)
          ·
            refine ⟨420504730271695567385139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280336486847797044923426147 420504730271695567385139221)
            ·
              refine ⟨19711159231485729721178401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 420504730271695567385139221 19711159231485729721178401)
              ·
                refine ⟨14783369423614297290883801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19711159231485729721178401 14783369423614297290883801)
                ·
                  refine ⟨11087527067710722968162851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14783369423614297290883801 11087527067710722968162851)
                  ·
                    refine ⟨16631290601566084452244277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11087527067710722968162851 16631290601566084452244277)
                    ·
                      refine ⟨1559183493896820417397901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16631290601566084452244277 1559183493896820417397901)
                      ·
                        rfl

theorem cell23_3036499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_3036499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036499 prefixEnd_3036499 := by exact prefixLift 3036499
  have htrace : WordTrace (prefixWord ++ tailWord_3036499) baseStart_3036499 baseEnd_3036499 := by
    simpa [prefixWord, tailWord_3036499, baseEnd_3036499] using wordTrace_append hprefix tailTrace_3036499
  have hstable : (prefixWord ++ tailWord_3036499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036499).length < 2 ^ (prefixWord ++ tailWord_3036499).sum := by decide
  have hdescent : baseEnd_3036499 < baseStart_3036499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036500 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_3036500 : Nat := 118140960795 + 3036500 * 2 ^ 59
def prefixEnd_3036500 : Nat := 4983230072969 + 3 ^ 40 * 3036500 * 2
def baseEnd_3036500 : Nat := 1559184007377474913485397

theorem tailTrace_3036500 : CollatzResearch.WordTrace tailWord_3036500 prefixEnd_3036500 1559184007377474913485397 := by
  unfold tailWord_3036500
  simp only [CollatzResearch.WordTrace]
  refine ⟨55375126749643283878909477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73833502332857711838545969 55375126749643283878909477)
  ·
    refine ⟨10382836265558115727295527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55375126749643283878909477 10382836265558115727295527)
    ·
      refine ⟨15574254398337173590943291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10382836265558115727295527 15574254398337173590943291)
      ·
        refine ⟨23361381597505760386414937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15574254398337173590943291 23361381597505760386414937)
        ·
          refine ⟨17521036198129320289811203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23361381597505760386414937 17521036198129320289811203)
          ·
            refine ⟨26281554297193980434716805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17521036198129320289811203 26281554297193980434716805)
            ·
              refine ⟨4927791430723871331509401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26281554297193980434716805 4927791430723871331509401)
              ·
                refine ⟨3695843573042903498632051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927791430723871331509401 3695843573042903498632051)
                ·
                  refine ⟨5543765359564355247948077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695843573042903498632051 5543765359564355247948077)
                  ·
                    refine ⟨2078912009836633217980529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5543765359564355247948077 2078912009836633217980529)
                    ·
                      refine ⟨1559184007377474913485397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078912009836633217980529 1559184007377474913485397)
                      ·
                        rfl

theorem cell23_3036500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_3036500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036500 prefixEnd_3036500 := by exact prefixLift 3036500
  have htrace : WordTrace (prefixWord ++ tailWord_3036500) baseStart_3036500 baseEnd_3036500 := by
    simpa [prefixWord, tailWord_3036500, baseEnd_3036500] using wordTrace_append hprefix tailTrace_3036500
  have hstable : (prefixWord ++ tailWord_3036500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036500).length < 2 ^ (prefixWord ++ tailWord_3036500).sum := by decide
  have hdescent : baseEnd_3036500 < baseStart_3036500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036516 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_3036516 : Nat := 118140960795 + 3036516 * 2 ^ 59
def prefixEnd_3036516 : Nat := 4983230072969 + 3 ^ 40 * 3036516 * 2
def baseEnd_3036516 : Nat := 1559192223067946850885323

theorem tailTrace_3036516 : CollatzResearch.WordTrace tailWord_3036516 prefixEnd_3036516 1559192223067946850885323 := by
  unfold tailWord_3036516
  simp only [CollatzResearch.WordTrace]
  refine ⟨55375418533614301245200701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73833891378152401660267601 55375418533614301245200701)
  ·
    refine ⟨20765781950105362966950263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55375418533614301245200701 20765781950105362966950263)
    ·
      refine ⟨31148672925158044450425395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20765781950105362966950263 31148672925158044450425395)
      ·
        refine ⟨46723009387737066675638093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31148672925158044450425395 46723009387737066675638093)
        ·
          refine ⟨17521128520401400003364285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46723009387737066675638093 17521128520401400003364285)
          ·
            refine ⟨6570423195150525001261607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17521128520401400003364285 6570423195150525001261607)
            ·
              refine ⟨9855634792725787501892411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570423195150525001261607 9855634792725787501892411)
              ·
                refine ⟨14783452189088681252838617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855634792725787501892411 14783452189088681252838617)
                ·
                  refine ⟨11087589141816510939628963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14783452189088681252838617 11087589141816510939628963)
                  ·
                    refine ⟨16631383712724766409443445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11087589141816510939628963 16631383712724766409443445)
                    ·
                      refine ⟨1559192223067946850885323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16631383712724766409443445 1559192223067946850885323)
                      ·
                        rfl

theorem cell23_3036516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_3036516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036516 prefixEnd_3036516 := by exact prefixLift 3036516
  have htrace : WordTrace (prefixWord ++ tailWord_3036516) baseStart_3036516 baseEnd_3036516 := by
    simpa [prefixWord, tailWord_3036516, baseEnd_3036516] using wordTrace_append hprefix tailTrace_3036516
  have hstable : (prefixWord ++ tailWord_3036516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036516).length < 2 ^ (prefixWord ++ tailWord_3036516).sum := by decide
  have hdescent : baseEnd_3036516 < baseStart_3036516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036530 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3036530 : Nat := 118140960795 + 3036530 * 2 ^ 59
def prefixEnd_3036530 : Nat := 4983230072969 + 3 ^ 40 * 3036530 * 2
def baseEnd_3036530 : Nat := 1559199411797109796110259

theorem tailTrace_3036530 : CollatzResearch.WordTrace tailWord_3036530 prefixEnd_3036530 1559199411797109796110259 := by
  unfold tailWord_3036530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687836922294470720352761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73834231792785255254274029 27687836922294470720352761)
  ·
    refine ⟨20765877691720853040264571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27687836922294470720352761 20765877691720853040264571)
    ·
      refine ⟨31148816537581279560396857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20765877691720853040264571 31148816537581279560396857)
      ·
        refine ⟨23361612403185959670297643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31148816537581279560396857 23361612403185959670297643)
        ·
          refine ⟨35042418604778939505446465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23361612403185959670297643 35042418604778939505446465)
          ·
            refine ⟨26281813953584204629084849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35042418604778939505446465 26281813953584204629084849)
            ·
              refine ⟨19711360465188153471813637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26281813953584204629084849 19711360465188153471813637)
              ·
                refine ⟨3695880087222778775965057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19711360465188153471813637 3695880087222778775965057)
                ·
                  refine ⟨2771910065417084081973793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3695880087222778775965057 2771910065417084081973793)
                  ·
                    refine ⟨2078932549062813061480345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771910065417084081973793 2078932549062813061480345)
                    ·
                      refine ⟨1559199411797109796110259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078932549062813061480345 1559199411797109796110259)
                      ·
                        rfl

theorem cell23_3036530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3036530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036530 prefixEnd_3036530 := by exact prefixLift 3036530
  have htrace : WordTrace (prefixWord ++ tailWord_3036530) baseStart_3036530 baseEnd_3036530 := by
    simpa [prefixWord, tailWord_3036530, baseEnd_3036530] using wordTrace_append hprefix tailTrace_3036530
  have hstable : (prefixWord ++ tailWord_3036530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036530).length < 2 ^ (prefixWord ++ tailWord_3036530).sum := by decide
  have hdescent : baseEnd_3036530 < baseStart_3036530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036547 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 2, 2, 2]
def baseStart_3036547 : Nat := 118140960795 + 3036547 * 2 ^ 59
def prefixEnd_3036547 : Nat := 4983230072969 + 3 ^ 40 * 3036547 * 2
def baseEnd_3036547 : Nat := 1559208140968236229597681

theorem tailTrace_3036547 : CollatzResearch.WordTrace tailWord_3036547 prefixEnd_3036547 1559208140968236229597681 := by
  unfold tailWord_3036547
  simp only [CollatzResearch.WordTrace]
  refine ⟨110751967730116294784779895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73834645153410863189853263 110751967730116294784779895)
  ·
    refine ⟨166127951595174442177169843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110751967730116294784779895 166127951595174442177169843)
    ·
      refine ⟨249191927392761663265754765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166127951595174442177169843 249191927392761663265754765)
      ·
        refine ⟨93446972772285623724658037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249191927392761663265754765 93446972772285623724658037)
        ·
          refine ⟨8760653697401777224186691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93446972772285623724658037 8760653697401777224186691)
          ·
            refine ⟨13140980546102665836280037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760653697401777224186691 13140980546102665836280037)
            ·
              refine ⟨2463933852394249844302507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13140980546102665836280037 2463933852394249844302507)
              ·
                refine ⟨3695900778591374766453761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463933852394249844302507 3695900778591374766453761)
                ·
                  refine ⟨2771925583943531074840321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3695900778591374766453761 2771925583943531074840321)
                  ·
                    refine ⟨2078944187957648306130241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771925583943531074840321 2078944187957648306130241)
                    ·
                      refine ⟨1559208140968236229597681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2078944187957648306130241 1559208140968236229597681)
                      ·
                        rfl

theorem cell23_3036547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_3036547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036547 prefixEnd_3036547 := by exact prefixLift 3036547
  have htrace : WordTrace (prefixWord ++ tailWord_3036547) baseStart_3036547 baseEnd_3036547 := by
    simpa [prefixWord, tailWord_3036547, baseEnd_3036547] using wordTrace_append hprefix tailTrace_3036547
  have hstable : (prefixWord ++ tailWord_3036547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036547).length < 2 ^ (prefixWord ++ tailWord_3036547).sum := by decide
  have hdescent : baseEnd_3036547 < baseStart_3036547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036549 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_3036549 : Nat := 118140960795 + 3036549 * 2 ^ 59
def prefixEnd_3036549 : Nat := 4983230072969 + 3 ^ 40 * 3036549 * 2
def baseEnd_3036549 : Nat := 519736389309848407257557

theorem tailTrace_3036549 : CollatzResearch.WordTrace tailWord_3036549 prefixEnd_3036549 519736389309848407257557 := by
  unfold tailWord_3036549
  simp only [CollatzResearch.WordTrace]
  refine ⟨110752040676109049126352701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73834693784072699417568467 110752040676109049126352701)
  ·
    refine ⟨41532015253540893422382263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110752040676109049126352701 41532015253540893422382263)
    ·
      refine ⟨62298022880311340133573395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41532015253540893422382263 62298022880311340133573395)
      ·
        refine ⟨93447034320467010200360093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62298022880311340133573395 93447034320467010200360093)
        ·
          refine ⟨35042637870175128825135035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93447034320467010200360093 35042637870175128825135035)
          ·
            refine ⟨52563956805262693237702553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35042637870175128825135035 52563956805262693237702553)
            ·
              refine ⟨39422967603947019928276915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52563956805262693237702553 39422967603947019928276915)
              ·
                refine ⟨59134451405920529892415373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39422967603947019928276915 59134451405920529892415373)
                ·
                  refine ⟨22175419277220198709655765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59134451405920529892415373 22175419277220198709655765)
                  ·
                    refine ⟨519736389309848407257557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22175419277220198709655765 519736389309848407257557)
                    ·
                      rfl

theorem cell23_3036549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_3036549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036549 prefixEnd_3036549 := by exact prefixLift 3036549
  have htrace : WordTrace (prefixWord ++ tailWord_3036549) baseStart_3036549 baseEnd_3036549 := by
    simpa [prefixWord, tailWord_3036549, baseEnd_3036549] using wordTrace_append hprefix tailTrace_3036549
  have hstable : (prefixWord ++ tailWord_3036549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036549).length < 2 ^ (prefixWord ++ tailWord_3036549).sum := by decide
  have hdescent : baseEnd_3036549 < baseStart_3036549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036620 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3036620 : Nat := 118140960795 + 3036620 * 2 ^ 59
def prefixEnd_3036620 : Nat := 4983230072969 + 3 ^ 40 * 3036620 * 2
def baseEnd_3036620 : Nat := 1559245625056014443984845

theorem tailTrace_3036620 : CollatzResearch.WordTrace tailWord_3036620 prefixEnd_3036620 1559245625056014443984845 := by
  unfold tailWord_3036620
  simp only [CollatzResearch.WordTrace]
  refine ⟨55377315129425914126093657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73836420172567885501458209 55377315129425914126093657)
  ·
    refine ⟨41532986347069435594570243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55377315129425914126093657 41532986347069435594570243)
    ·
      refine ⟨62299479520604153391855365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41532986347069435594570243 62299479520604153391855365)
      ·
        refine ⟨11681152410113278760972881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62299479520604153391855365 11681152410113278760972881)
        ·
          refine ⟨8760864307584959070729661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681152410113278760972881 8760864307584959070729661)
          ·
            refine ⟨3285324115344359651523623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8760864307584959070729661 3285324115344359651523623)
            ·
              refine ⟨4927986173016539477285435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285324115344359651523623 4927986173016539477285435)
              ·
                refine ⟨7391979259524809215928153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927986173016539477285435 7391979259524809215928153)
                ·
                  refine ⟨5543984444643606911946115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391979259524809215928153 5543984444643606911946115)
                  ·
                    refine ⟨8315976666965410367919173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5543984444643606911946115 8315976666965410367919173)
                    ·
                      refine ⟨1559245625056014443984845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8315976666965410367919173 1559245625056014443984845)
                      ·
                        rfl

theorem cell23_3036620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3036620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036620 prefixEnd_3036620 := by exact prefixLift 3036620
  have htrace : WordTrace (prefixWord ++ tailWord_3036620) baseStart_3036620 baseEnd_3036620 := by
    simpa [prefixWord, tailWord_3036620, baseEnd_3036620] using wordTrace_append hprefix tailTrace_3036620
  have hstable : (prefixWord ++ tailWord_3036620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036620).length < 2 ^ (prefixWord ++ tailWord_3036620).sum := by decide
  have hdescent : baseEnd_3036620 < baseStart_3036620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036623 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_3036623 : Nat := 118140960795 + 3036623 * 2 ^ 59
def prefixEnd_3036623 : Nat := 4983230072969 + 3 ^ 40 * 3036623 * 2
def baseEnd_3036623 : Nat := 1559247165497977932247331

theorem tailTrace_3036623 : CollatzResearch.WordTrace tailWord_3036623 prefixEnd_3036623 1559247165497977932247331 := by
  unfold tailWord_3036623
  simp only [CollatzResearch.WordTrace]
  refine ⟨110754739677840959764546523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73836493118560639843031015 110754739677840959764546523)
  ·
    refine ⟨166132109516761439646819785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110754739677840959764546523 166132109516761439646819785)
    ·
      refine ⟨124599082137571079735114839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166132109516761439646819785 124599082137571079735114839)
      ·
        refine ⟨186898623206356619602672259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124599082137571079735114839 186898623206356619602672259)
        ·
          refine ⟨280347934809534929404008389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186898623206356619602672259 280347934809534929404008389)
          ·
            refine ⟨52565237776787799263251573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280347934809534929404008389 52565237776787799263251573)
            ·
              refine ⟨4927991041573856180929835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52565237776787799263251573 4927991041573856180929835)
              ·
                refine ⟨7391986562360784271394753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927991041573856180929835 7391986562360784271394753)
                ·
                  refine ⟨5543989921770588203546065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391986562360784271394753 5543989921770588203546065)
                  ·
                    refine ⟨4157992441327941152659549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543989921770588203546065 4157992441327941152659549)
                    ·
                      refine ⟨1559247165497977932247331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4157992441327941152659549 1559247165497977932247331)
                      ·
                        rfl

theorem cell23_3036623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_3036623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036623 prefixEnd_3036623 := by exact prefixLift 3036623
  have htrace : WordTrace (prefixWord ++ tailWord_3036623) baseStart_3036623 baseEnd_3036623 := by
    simpa [prefixWord, tailWord_3036623, baseEnd_3036623] using wordTrace_append hprefix tailTrace_3036623
  have hstable : (prefixWord ++ tailWord_3036623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036623).length < 2 ^ (prefixWord ++ tailWord_3036623).sum := by decide
  have hdescent : baseEnd_3036623 < baseStart_3036623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036643 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 6]
def baseStart_3036643 : Nat := 118140960795 + 3036643 * 2 ^ 59
def prefixEnd_3036643 : Nat := 4983230072969 + 3 ^ 40 * 3036643 * 2
def baseEnd_3036643 : Nat := 173250826123451983777471

theorem tailTrace_3036643 : CollatzResearch.WordTrace tailWord_3036643 prefixEnd_3036643 173250826123451983777471 := by
  unfold tailWord_3036643
  simp only [CollatzResearch.WordTrace]
  refine ⟨110755469137768503180274583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73836979425179002120183055 110755469137768503180274583)
  ·
    refine ⟨166133203706652754770411875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110755469137768503180274583 166133203706652754770411875)
    ·
      refine ⟨249199805559979132155617813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166133203706652754770411875 249199805559979132155617813)
      ·
        refine ⟨11681240885624021819794585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249199805559979132155617813 11681240885624021819794585)
        ·
          refine ⟨8760930664218016364845939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681240885624021819794585 8760930664218016364845939)
          ·
            refine ⟨13141395996327024547268909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760930664218016364845939 13141395996327024547268909)
            ·
              refine ⟨4928023498622634205225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13141395996327024547268909 4928023498622634205225841)
              ·
                refine ⟨3696017623966975653919381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928023498622634205225841 3696017623966975653919381)
                ·
                  refine ⟨173250826123451983777471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3696017623966975653919381 173250826123451983777471)
                  ·
                    rfl

theorem cell23_3036643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 6].length) (baseStart_3036643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036643 prefixEnd_3036643 := by exact prefixLift 3036643
  have htrace : WordTrace (prefixWord ++ tailWord_3036643) baseStart_3036643 baseEnd_3036643 := by
    simpa [prefixWord, tailWord_3036643, baseEnd_3036643] using wordTrace_append hprefix tailTrace_3036643
  have hstable : (prefixWord ++ tailWord_3036643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036643).length < 2 ^ (prefixWord ++ tailWord_3036643).sum := by decide
  have hdescent : baseEnd_3036643 < baseStart_3036643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036663 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_3036663 : Nat := 118140960795 + 3036663 * 2 ^ 59
def prefixEnd_3036663 : Nat := 4983230072969 + 3 ^ 40 * 3036663 * 2
def baseEnd_3036663 : Nat := 1559267704724157775747147

theorem tailTrace_3036663 : CollatzResearch.WordTrace tailWord_3036663 prefixEnd_3036663 1559267704724157775747147 := by
  unfold tailWord_3036663
  simp only [CollatzResearch.WordTrace]
  refine ⟨110756198597696046596002643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73837465731797364397335095 110756198597696046596002643)
  ·
    refine ⟨166134297896544069894003965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110756198597696046596002643 166134297896544069894003965)
    ·
      refine ⟨62300361711204026210251487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166134297896544069894003965 62300361711204026210251487)
      ·
        refine ⟨93450542566806039315377231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62300361711204026210251487 93450542566806039315377231)
        ·
          refine ⟨140175813850209058973065847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93450542566806039315377231 140175813850209058973065847)
          ·
            refine ⟨210263720775313588459598771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140175813850209058973065847 210263720775313588459598771)
            ·
              refine ⟨315395581162970382689398157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210263720775313588459598771 315395581162970382689398157)
              ·
                refine ⟨118273342936113893508524309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315395581162970382689398157 118273342936113893508524309)
                ·
                  refine ⟨5544062950130338758212077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118273342936113893508524309 5544062950130338758212077)
                  ·
                    refine ⟨2079023606298877034329529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5544062950130338758212077 2079023606298877034329529)
                    ·
                      refine ⟨1559267704724157775747147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079023606298877034329529 1559267704724157775747147)
                      ·
                        rfl

theorem cell23_3036663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_3036663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036663 prefixEnd_3036663 := by exact prefixLift 3036663
  have htrace : WordTrace (prefixWord ++ tailWord_3036663) baseStart_3036663 baseEnd_3036663 := by
    simpa [prefixWord, tailWord_3036663, baseEnd_3036663] using wordTrace_append hprefix tailTrace_3036663
  have hstable : (prefixWord ++ tailWord_3036663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036663).length < 2 ^ (prefixWord ++ tailWord_3036663).sum := by decide
  have hdescent : baseEnd_3036663 < baseStart_3036663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036703 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 4, 4]
def baseStart_3036703 : Nat := 118140960795 + 3036703 * 2 ^ 59
def prefixEnd_3036703 : Nat := 4983230072969 + 3 ^ 40 * 3036703 * 2
def baseEnd_3036703 : Nat := 519762747983445873082321

theorem tailTrace_3036703 : CollatzResearch.WordTrace tailWord_3036703 prefixEnd_3036703 519762747983445873082321 := by
  unfold tailWord_3036703
  simp only [CollatzResearch.WordTrace]
  refine ⟨110757657517551133427458763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73838438345034088951639175 110757657517551133427458763)
  ·
    refine ⟨166136486276326700141188145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110757657517551133427458763 166136486276326700141188145)
    ·
      refine ⟨124602364707245025105891109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166136486276326700141188145 124602364707245025105891109)
      ·
        refine ⟨23362943382608442207354583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124602364707245025105891109 23362943382608442207354583)
        ·
          refine ⟨35044415073912663311031875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23362943382608442207354583 35044415073912663311031875)
          ·
            refine ⟨52566622610868994966547813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35044415073912663311031875 52566622610868994966547813)
            ·
              refine ⟨9856241739537936556227715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52566622610868994966547813 9856241739537936556227715)
              ·
                refine ⟨14784362609306904834341573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856241739537936556227715 14784362609306904834341573)
                ·
                  refine ⟨2772067989245044656439045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14784362609306904834341573 2772067989245044656439045)
                  ·
                    refine ⟨519762747983445873082321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772067989245044656439045 519762747983445873082321)
                    ·
                      rfl

theorem cell23_3036703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_3036703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036703 prefixEnd_3036703 := by exact prefixLift 3036703
  have htrace : WordTrace (prefixWord ++ tailWord_3036703) baseStart_3036703 baseEnd_3036703 := by
    simpa [prefixWord, tailWord_3036703, baseEnd_3036703] using wordTrace_append hprefix tailTrace_3036703
  have hstable : (prefixWord ++ tailWord_3036703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036703).length < 2 ^ (prefixWord ++ tailWord_3036703).sum := by decide
  have hdescent : baseEnd_3036703 < baseStart_3036703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036800 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2]
def baseStart_3036800 : Nat := 118140960795 + 3036800 * 2 ^ 59
def prefixEnd_3036800 : Nat := 4983230072969 + 3 ^ 40 * 3036800 * 2
def baseEnd_3036800 : Nat := 1559338051573823739734017

theorem tailTrace_3036800 : CollatzResearch.WordTrace tailWord_3036800 prefixEnd_3036800 1559338051573823739734017 := by
  unfold tailWord_3036800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55380597699099859496869927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73840796932133145995826569 55380597699099859496869927)
  ·
    refine ⟨83070896548649789245304891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55380597699099859496869927 83070896548649789245304891)
    ·
      refine ⟨124606344822974683867957337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83070896548649789245304891 124606344822974683867957337)
      ·
        refine ⟨93454758617231012900968003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124606344822974683867957337 93454758617231012900968003)
        ·
          refine ⟨140182137925846519351452005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93454758617231012900968003 140182137925846519351452005)
          ·
            refine ⟨26284150861096222378397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140182137925846519351452005 26284150861096222378397251)
            ·
              refine ⟨39426226291644333567595877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26284150861096222378397251 39426226291644333567595877)
              ·
                refine ⟨7392417429683312543924227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39426226291644333567595877 7392417429683312543924227)
                ·
                  refine ⟨11088626144524968815886341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392417429683312543924227 11088626144524968815886341)
                  ·
                    refine ⟨2079117402098431652978689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11088626144524968815886341 2079117402098431652978689)
                    ·
                      refine ⟨1559338051573823739734017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079117402098431652978689 1559338051573823739734017)
                      ·
                        rfl

theorem cell23_3036800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_3036800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036800 prefixEnd_3036800 := by exact prefixLift 3036800
  have htrace : WordTrace (prefixWord ++ tailWord_3036800) baseStart_3036800 baseEnd_3036800 := by
    simpa [prefixWord, tailWord_3036800, baseEnd_3036800] using wordTrace_append hprefix tailTrace_3036800
  have hstable : (prefixWord ++ tailWord_3036800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036800).length < 2 ^ (prefixWord ++ tailWord_3036800).sum := by decide
  have hdescent : baseEnd_3036800 < baseStart_3036800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036804 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_3036804 : Nat := 118140960795 + 3036804 * 2 ^ 59
def prefixEnd_3036804 : Nat := 4983230072969 + 3 ^ 40 * 3036804 * 2
def baseEnd_3036804 : Nat := 1559340105496441724083999

theorem tailTrace_3036804 : CollatzResearch.WordTrace tailWord_3036804 prefixEnd_3036804 1559340105496441724083999 := by
  unfold tailWord_3036804
  simp only [CollatzResearch.WordTrace]
  refine ⟨55380670645092613838442733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73840894193456818451256977 55380670645092613838442733)
  ·
    refine ⟨20767751491909730189416025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55380670645092613838442733 20767751491909730189416025)
    ·
      refine ⟨15575813618932297642062019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20767751491909730189416025 15575813618932297642062019)
      ·
        refine ⟨23363720428398446463093029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15575813618932297642062019 23363720428398446463093029)
        ·
          refine ⟨4380697580324708711829943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23363720428398446463093029 4380697580324708711829943)
          ·
            refine ⟨6571046370487063067744915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380697580324708711829943 6571046370487063067744915)
            ·
              refine ⟨9856569555730594601617373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571046370487063067744915 9856569555730594601617373)
              ·
                refine ⟨3696213583398972975606515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9856569555730594601617373 3696213583398972975606515)
                ·
                  refine ⟨5544320375098459463409773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696213583398972975606515 5544320375098459463409773)
                  ·
                    refine ⟨2079120140661922298778665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5544320375098459463409773 2079120140661922298778665)
                    ·
                      refine ⟨1559340105496441724083999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079120140661922298778665 1559340105496441724083999)
                      ·
                        rfl

theorem cell23_3036804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_3036804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036804 prefixEnd_3036804 := by exact prefixLift 3036804
  have htrace : WordTrace (prefixWord ++ tailWord_3036804) baseStart_3036804 baseEnd_3036804 := by
    simpa [prefixWord, tailWord_3036804, baseEnd_3036804] using wordTrace_append hprefix tailTrace_3036804
  have hstable : (prefixWord ++ tailWord_3036804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036804).length < 2 ^ (prefixWord ++ tailWord_3036804).sum := by decide
  have hdescent : baseEnd_3036804 < baseStart_3036804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036817 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_3036817 : Nat := 118140960795 + 3036817 * 2 ^ 59
def prefixEnd_3036817 : Nat := 4983230072969 + 3 ^ 40 * 3036817 * 2
def baseEnd_3036817 : Nat := 1559346780744950173221439

theorem tailTrace_3036817 : CollatzResearch.WordTrace tailWord_3036817 prefixEnd_3036817 1559346780744950173221439 := by
  unfold tailWord_3036817
  simp only [CollatzResearch.WordTrace]
  refine ⟨110761815439138130897108705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73841210292758753931405803 110761815439138130897108705)
  ·
    refine ⟨83071361579353598172831529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110761815439138130897108705 83071361579353598172831529)
    ·
      refine ⟨62303521184515198629623647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83071361579353598172831529 62303521184515198629623647)
      ·
        refine ⟨93455281776772797944435471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62303521184515198629623647 93455281776772797944435471)
        ·
          refine ⟨140182922665159196916653207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93455281776772797944435471 140182922665159196916653207)
          ·
            refine ⟨210274383997738795374979811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140182922665159196916653207 210274383997738795374979811)
            ·
              refine ⟨315411575996608193062469717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210274383997738795374979811 315411575996608193062469717)
              ·
                refine ⟨3696229406210252262450817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 315411575996608193062469717 3696229406210252262450817)
                ·
                  refine ⟨2772172054657689196838113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696229406210252262450817 2772172054657689196838113)
                  ·
                    refine ⟨2079129040993266897628585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2772172054657689196838113 2079129040993266897628585)
                    ·
                      refine ⟨1559346780744950173221439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079129040993266897628585 1559346780744950173221439)
                      ·
                        rfl

theorem cell23_3036817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_3036817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036817 prefixEnd_3036817 := by exact prefixLift 3036817
  have htrace : WordTrace (prefixWord ++ tailWord_3036817) baseStart_3036817 baseEnd_3036817 := by
    simpa [prefixWord, tailWord_3036817, baseEnd_3036817] using wordTrace_append hprefix tailTrace_3036817
  have hstable : (prefixWord ++ tailWord_3036817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036817).length < 2 ^ (prefixWord ++ tailWord_3036817).sum := by decide
  have hdescent : baseEnd_3036817 < baseStart_3036817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036823 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 7]
def baseStart_3036823 : Nat := 118140960795 + 3036823 * 2 ^ 59
def prefixEnd_3036823 : Nat := 4983230072969 + 3 ^ 40 * 3036823 * 2
def baseEnd_3036823 : Nat := 173261095736541905527379

theorem tailTrace_3036823 : CollatzResearch.WordTrace tailWord_3036823 prefixEnd_3036823 173261095736541905527379 := by
  unfold tailWord_3036823
  simp only [CollatzResearch.WordTrace]
  refine ⟨110762034277116393921827123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73841356184744262614551415 110762034277116393921827123)
  ·
    refine ⟨166143051415674590882740685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110762034277116393921827123 166143051415674590882740685)
    ·
      refine ⟨62303644280877971581027757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166143051415674590882740685 62303644280877971581027757)
      ·
        refine ⟨23363866605329239342885409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62303644280877971581027757 23363866605329239342885409)
        ·
          refine ⟨17522899953996929507164057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23363866605329239342885409 17522899953996929507164057)
          ·
            refine ⟨13142174965497697130373043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17522899953996929507164057 13142174965497697130373043)
            ·
              refine ⟨19713262448246545695559565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13142174965497697130373043 19713262448246545695559565)
              ·
                refine ⟨7392473418092454635834837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19713262448246545695559565 7392473418092454635834837)
                ·
                  refine ⟨173261095736541905527379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7392473418092454635834837 173261095736541905527379)
                  ·
                    rfl

theorem cell23_3036823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 7].length) (baseStart_3036823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036823 prefixEnd_3036823 := by exact prefixLift 3036823
  have htrace : WordTrace (prefixWord ++ tailWord_3036823) baseStart_3036823 baseEnd_3036823 := by
    simpa [prefixWord, tailWord_3036823, baseEnd_3036823] using wordTrace_append hprefix tailTrace_3036823
  have hstable : (prefixWord ++ tailWord_3036823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036823).length < 2 ^ (prefixWord ++ tailWord_3036823).sum := by decide
  have hdescent : baseEnd_3036823 < baseStart_3036823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036863 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3036863 : Nat := 118140960795 + 3036863 * 2 ^ 59
def prefixEnd_3036863 : Nat := 4983230072969 + 3 ^ 40 * 3036863 * 2
def baseEnd_3036863 : Nat := 1559370400855056993246227

theorem tailTrace_3036863 : CollatzResearch.WordTrace tailWord_3036863 prefixEnd_3036863 1559370400855056993246227 := by
  unfold tailWord_3036863
  simp only [CollatzResearch.WordTrace]
  refine ⟨110763493196971480753283243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73842328797980987168855495 110763493196971480753283243)
  ·
    refine ⟨166145239795457221129924865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110763493196971480753283243 166145239795457221129924865)
    ·
      refine ⟨124608929846592915847443649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166145239795457221129924865 124608929846592915847443649)
      ·
        refine ⟨93456697384944686885582737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124608929846592915847443649 93456697384944686885582737)
        ·
          refine ⟨70092523038708515164187053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93456697384944686885582737 70092523038708515164187053)
          ·
            refine ⟨26284696139515693186570145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70092523038708515164187053 26284696139515693186570145)
            ·
              refine ⟨19713522104636769889927609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26284696139515693186570145 19713522104636769889927609)
              ·
                refine ⟨14785141578477577417445707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19713522104636769889927609 14785141578477577417445707)
                ·
                  refine ⟨22177712367716366126168561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14785141578477577417445707 22177712367716366126168561)
                  ·
                    refine ⟨16633284275787274594626421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22177712367716366126168561 16633284275787274594626421)
                    ·
                      refine ⟨1559370400855056993246227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16633284275787274594626421 1559370400855056993246227)
                      ·
                        rfl

theorem cell23_3036863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3036863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036863 prefixEnd_3036863 := by exact prefixLift 3036863
  have htrace : WordTrace (prefixWord ++ tailWord_3036863) baseStart_3036863 baseEnd_3036863 := by
    simpa [prefixWord, tailWord_3036863, baseEnd_3036863] using wordTrace_append hprefix tailTrace_3036863
  have hstable : (prefixWord ++ tailWord_3036863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036863).length < 2 ^ (prefixWord ++ tailWord_3036863).sum := by decide
  have hdescent : baseEnd_3036863 < baseStart_3036863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036874 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_3036874 : Nat := 118140960795 + 3036874 * 2 ^ 59
def prefixEnd_3036874 : Nat := 4983230072969 + 3 ^ 40 * 3036874 * 2
def baseEnd_3036874 : Nat := 173264005460250716689853

theorem tailTrace_3036874 : CollatzResearch.WordTrace tailWord_3036874 prefixEnd_3036874 173264005460250716689853 := by
  unfold tailWord_3036874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690973599982907407983419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73842596266621086421289117 27690973599982907407983419)
  ·
    refine ⟨41536460399974361111975129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27690973599982907407983419 41536460399974361111975129)
    ·
      refine ⟨31152345299980770833981347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41536460399974361111975129 31152345299980770833981347)
      ·
        refine ⟨46728517949971156250972021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31152345299980770833981347 46728517949971156250972021)
        ·
          refine ⟨4380798557809795898528627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46728517949971156250972021 4380798557809795898528627)
          ·
            refine ⟨6571197836714693847792941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380798557809795898528627 6571197836714693847792941)
            ·
              refine ⟨2464199188768010192922353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6571197836714693847792941 2464199188768010192922353)
              ·
                refine ⟨1848149391576007644691765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464199188768010192922353 1848149391576007644691765)
                ·
                  refine ⟨173264005460250716689853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848149391576007644691765 173264005460250716689853)
                  ·
                    rfl

theorem cell23_3036874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_3036874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036874 prefixEnd_3036874 := by exact prefixLift 3036874
  have htrace : WordTrace (prefixWord ++ tailWord_3036874) baseStart_3036874 baseEnd_3036874 := by
    simpa [prefixWord, tailWord_3036874, baseEnd_3036874] using wordTrace_append hprefix tailTrace_3036874
  have hstable : (prefixWord ++ tailWord_3036874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036874).length < 2 ^ (prefixWord ++ tailWord_3036874).sum := by decide
  have hdescent : baseEnd_3036874 < baseStart_3036874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036900 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_3036900 : Nat := 118140960795 + 3036900 * 2 ^ 59
def prefixEnd_3036900 : Nat := 4983230072969 + 3 ^ 40 * 3036900 * 2
def baseEnd_3036900 : Nat := 519796466546424449494519

theorem tailTrace_3036900 : CollatzResearch.WordTrace tailWord_3036900 prefixEnd_3036900 519796466546424449494519 := by
  unfold tailWord_3036900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55382421348918718036190077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73843228465224957381586769 55382421348918718036190077)
  ·
    refine ⟨20768408005844519263571279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55382421348918718036190077 20768408005844519263571279)
    ·
      refine ⟨31152612008766778895356919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20768408005844519263571279 31152612008766778895356919)
      ·
        refine ⟨46728918013150168343035379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31152612008766778895356919 46728918013150168343035379)
        ·
          refine ⟨70093377019725252514553069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46728918013150168343035379 70093377019725252514553069)
          ·
            refine ⟨26285016382396969692957401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70093377019725252514553069 26285016382396969692957401)
            ·
              refine ⟨19713762286797727269718051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26285016382396969692957401 19713762286797727269718051)
              ·
                refine ⟨29570643430196590904577077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19713762286797727269718051 29570643430196590904577077)
                ·
                  refine ⟨2772247821580930397304101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29570643430196590904577077 2772247821580930397304101)
                  ·
                    refine ⟨519796466546424449494519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772247821580930397304101 519796466546424449494519)
                    ·
                      rfl

theorem cell23_3036900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_3036900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036900 prefixEnd_3036900 := by exact prefixLift 3036900
  have htrace : WordTrace (prefixWord ++ tailWord_3036900) baseStart_3036900 baseEnd_3036900 := by
    simpa [prefixWord, tailWord_3036900, baseEnd_3036900] using wordTrace_append hprefix tailTrace_3036900
  have hstable : (prefixWord ++ tailWord_3036900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036900).length < 2 ^ (prefixWord ++ tailWord_3036900).sum := by decide
  have hdescent : baseEnd_3036900 < baseStart_3036900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036953 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_3036953 : Nat := 118140960795 + 3036953 * 2 ^ 59
def prefixEnd_3036953 : Nat := 4983230072969 + 3 ^ 40 * 3036953 * 2
def baseEnd_3036953 : Nat := 1559416614113961641120813

theorem tailTrace_3036953 : CollatzResearch.WordTrace tailWord_3036953 prefixEnd_3036953 1559416614113961641120813 := by
  unfold tailWord_3036953
  simp only [CollatzResearch.WordTrace]
  refine ⟨110766775766645426124059513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73844517177763617416039675 110766775766645426124059513)
  ·
    refine ⟨83075081824984069593044635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110766775766645426124059513 83075081824984069593044635)
    ·
      refine ⟨124612622737476104389566953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83075081824984069593044635 124612622737476104389566953)
      ·
        refine ⟨93459467053107078292175215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124612622737476104389566953 93459467053107078292175215)
        ·
          refine ⟨140189200579660617438262823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93459467053107078292175215 140189200579660617438262823)
          ·
            refine ⟨210283800869490926157394235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140189200579660617438262823 210283800869490926157394235)
            ·
              refine ⟨315425701304236389236091353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210283800869490926157394235 315425701304236389236091353)
              ·
                refine ⟨236569275978177291927068515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315425701304236389236091353 236569275978177291927068515)
                ·
                  refine ⟨354853913967265937890602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236569275978177291927068515 354853913967265937890602773)
                  ·
                    refine ⟨16633777217215590838622005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 354853913967265937890602773 16633777217215590838622005)
                    ·
                      refine ⟨1559416614113961641120813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16633777217215590838622005 1559416614113961641120813)
                      ·
                        rfl

theorem cell23_3036953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_3036953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036953 prefixEnd_3036953 := by exact prefixLift 3036953
  have htrace : WordTrace (prefixWord ++ tailWord_3036953) baseStart_3036953 baseEnd_3036953 := by
    simpa [prefixWord, tailWord_3036953, baseEnd_3036953] using wordTrace_append hprefix tailTrace_3036953
  have hstable : (prefixWord ++ tailWord_3036953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036953).length < 2 ^ (prefixWord ++ tailWord_3036953).sum := by decide
  have hdescent : baseEnd_3036953 < baseStart_3036953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036958 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3036958 : Nat := 118140960795 + 3036958 * 2 ^ 59
def prefixEnd_3036958 : Nat := 4983230072969 + 3 ^ 40 * 3036958 * 2
def baseEnd_3036958 : Nat := 1559419181517234121558291

theorem tailTrace_3036958 : CollatzResearch.WordTrace tailWord_3036958 prefixEnd_3036958 1559419181517234121558291 := by
  unfold tailWord_3036958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845869766453413997248941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73844638754418207985327685 13845869766453413997248941)
  ·
    refine ⟨5192201162420030248968353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13845869766453413997248941 5192201162420030248968353)
    ·
      refine ⟨3894150871815022686726265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5192201162420030248968353 3894150871815022686726265)
      ·
        refine ⟨2920613153861267015044699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3894150871815022686726265 2920613153861267015044699)
        ·
          refine ⟨4380919730791900522567049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920613153861267015044699 4380919730791900522567049)
          ·
            refine ⟨3285689798093925391925287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380919730791900522567049 3285689798093925391925287)
            ·
              refine ⟨4928534697140888087887931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285689798093925391925287 4928534697140888087887931)
              ·
                refine ⟨7392802045711332131831897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928534697140888087887931 7392802045711332131831897)
                ·
                  refine ⟨5544601534283499098873923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392802045711332131831897 5544601534283499098873923)
                  ·
                    refine ⟨8316902301425248648310885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5544601534283499098873923 8316902301425248648310885)
                    ·
                      refine ⟨1559419181517234121558291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8316902301425248648310885 1559419181517234121558291)
                      ·
                        rfl

theorem cell23_3036958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3036958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036958 prefixEnd_3036958 := by exact prefixLift 3036958
  have htrace : WordTrace (prefixWord ++ tailWord_3036958) baseStart_3036958 baseEnd_3036958 := by
    simpa [prefixWord, tailWord_3036958, baseEnd_3036958] using wordTrace_append hprefix tailTrace_3036958
  have hstable : (prefixWord ++ tailWord_3036958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036958).length < 2 ^ (prefixWord ++ tailWord_3036958).sum := by decide
  have hdescent : baseEnd_3036958 < baseStart_3036958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036960 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_3036960 : Nat := 118140960795 + 3036960 * 2 ^ 59
def prefixEnd_3036960 : Nat := 4983230072969 + 3 ^ 40 * 3036960 * 2
def baseEnd_3036960 : Nat := 519806736159514371244427

theorem tailTrace_3036960 : CollatzResearch.WordTrace tailWord_3036960 prefixEnd_3036960 519806736159514371244427 := by
  unfold tailWord_3036960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55383515538810033159782167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73844687385080044213042889 55383515538810033159782167)
  ·
    refine ⟨83075273308215049739673251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55383515538810033159782167 83075273308215049739673251)
    ·
      refine ⟨124612909962322574609509877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83075273308215049739673251 124612909962322574609509877)
      ·
        refine ⟨11682460308967741369641551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124612909962322574609509877 11682460308967741369641551)
        ·
          refine ⟨17523690463451612054462327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11682460308967741369641551 17523690463451612054462327)
          ·
            refine ⟨26285535695177418081693491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17523690463451612054462327 26285535695177418081693491)
            ·
              refine ⟨39428303542766127122540237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26285535695177418081693491 39428303542766127122540237)
              ·
                refine ⟨14785613828537297670952589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39428303542766127122540237 14785613828537297670952589)
                ·
                  refine ⟨5544605185701486626607221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14785613828537297670952589 5544605185701486626607221)
                  ·
                    refine ⟨519806736159514371244427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544605185701486626607221 519806736159514371244427)
                    ·
                      rfl

theorem cell23_3036960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_3036960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036960 prefixEnd_3036960 := by exact prefixLift 3036960
  have htrace : WordTrace (prefixWord ++ tailWord_3036960) baseStart_3036960 baseEnd_3036960 := by
    simpa [prefixWord, tailWord_3036960, baseEnd_3036960] using wordTrace_append hprefix tailTrace_3036960
  have hstable : (prefixWord ++ tailWord_3036960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036960).length < 2 ^ (prefixWord ++ tailWord_3036960).sum := by decide
  have hdescent : baseEnd_3036960 < baseStart_3036960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3036977 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_3036977 : Nat := 118140960795 + 3036977 * 2 ^ 59
def prefixEnd_3036977 : Nat := 4983230072969 + 3 ^ 40 * 3036977 * 2
def baseEnd_3036977 : Nat := 519809645883223182406901

theorem tailTrace_3036977 : CollatzResearch.WordTrace tailWord_3036977 prefixEnd_3036977 519809645883223182406901 := by
  unfold tailWord_3036977
  simp only [CollatzResearch.WordTrace]
  refine ⟨110767651118558478222933185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73845100745705652148622123 110767651118558478222933185)
  ·
    refine ⟨83075738338918858667199889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110767651118558478222933185 83075738338918858667199889)
    ·
      refine ⟨62306803754189144000399917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83075738338918858667199889 62306803754189144000399917)
      ·
        refine ⟨23365051407820929000149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62306803754189144000399917 23365051407820929000149969)
        ·
          refine ⟨17523788555865696750112477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23365051407820929000149969 17523788555865696750112477)
          ·
            refine ⟨6571420708449636281292179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17523788555865696750112477 6571420708449636281292179)
            ·
              refine ⟨9857131062674454421938269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571420708449636281292179 9857131062674454421938269)
              ·
                refine ⟨3696424148502920408226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9857131062674454421938269 3696424148502920408226851)
                ·
                  refine ⟨5544636222754380612340277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696424148502920408226851 5544636222754380612340277)
                  ·
                    refine ⟨519809645883223182406901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5544636222754380612340277 519809645883223182406901)
                    ·
                      rfl

theorem cell23_3036977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_3036977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3036977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3036977 prefixEnd_3036977 := by exact prefixLift 3036977
  have htrace : WordTrace (prefixWord ++ tailWord_3036977) baseStart_3036977 baseEnd_3036977 := by
    simpa [prefixWord, tailWord_3036977, baseEnd_3036977] using wordTrace_append hprefix tailTrace_3036977
  have hstable : (prefixWord ++ tailWord_3036977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3036977).length < 2 ^ (prefixWord ++ tailWord_3036977).sum := by decide
  have hdescent : baseEnd_3036977 < baseStart_3036977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3036977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037000 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3037000 : Nat := 118140960795 + 3037000 * 2 ^ 59
def prefixEnd_3037000 : Nat := 4983230072969 + 3 ^ 40 * 3037000 * 2
def baseEnd_3037000 : Nat := 1559440747704722957233097

theorem tailTrace_3037000 : CollatzResearch.WordTrace tailWord_3037000 prefixEnd_3037000 1559440747704722957233097 := by
  unfold tailWord_3037000
  simp only [CollatzResearch.WordTrace]
  refine ⟨55384244998737576575510227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73845659998316768767346969 55384244998737576575510227)
  ·
    refine ⟨83076367498106364863265341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55384244998737576575510227 83076367498106364863265341)
    ·
      refine ⟨31153637811789886823724503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83076367498106364863265341 31153637811789886823724503)
      ·
        refine ⟨46730456717684830235586755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31153637811789886823724503 46730456717684830235586755)
        ·
          refine ⟨70095685076527245353380133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46730456717684830235586755 70095685076527245353380133)
          ·
            refine ⟨13142940951848858503758775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70095685076527245353380133 13142940951848858503758775)
            ·
              refine ⟨19714411427773287755638163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13142940951848858503758775 19714411427773287755638163)
              ·
                refine ⟨29571617141659931633457245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19714411427773287755638163 29571617141659931633457245)
                ·
                  refine ⟨11089356428122474362546467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29571617141659931633457245 11089356428122474362546467)
                  ·
                    refine ⟨16634034642183711543819701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11089356428122474362546467 16634034642183711543819701)
                    ·
                      refine ⟨1559440747704722957233097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16634034642183711543819701 1559440747704722957233097)
                      ·
                        rfl

theorem cell23_3037000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3037000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037000 prefixEnd_3037000 := by exact prefixLift 3037000
  have htrace : WordTrace (prefixWord ++ tailWord_3037000) baseStart_3037000 baseEnd_3037000 := by
    simpa [prefixWord, tailWord_3037000, baseEnd_3037000] using wordTrace_append hprefix tailTrace_3037000
  have hstable : (prefixWord ++ tailWord_3037000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037000).length < 2 ^ (prefixWord ++ tailWord_3037000).sum := by decide
  have hdescent : baseEnd_3037000 < baseStart_3037000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037054 : List Nat := [4, 2, 3, 1, 1, 2, 2, 8]
def baseStart_3037054 : Nat := 118140960795 + 3037054 * 2 ^ 59
def prefixEnd_3037054 : Nat := 4983230072969 + 3 ^ 40 * 3037054 * 2
def baseEnd_3037054 : Nat := 57758091691113546146587

theorem tailTrace_3037054 : CollatzResearch.WordTrace tailWord_3037054 prefixEnd_3037054 57758091691113546146587 := by
  unfold tailWord_3037054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13846307442409940046685777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73846973026186346915657477 13846307442409940046685777)
  ·
    refine ⟨10384730581807455035014333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13846307442409940046685777 10384730581807455035014333)
    ·
      refine ⟨3894273968177795638130375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10384730581807455035014333 3894273968177795638130375)
      ·
        refine ⟨5841410952266693457195563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894273968177795638130375 5841410952266693457195563)
        ·
          refine ⟨8762116428400040185793345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841410952266693457195563 8762116428400040185793345)
          ·
            refine ⟨6571587321300030139345009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762116428400040185793345 6571587321300030139345009)
            ·
              refine ⟨4928690490975022604508757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571587321300030139345009 4928690490975022604508757)
              ·
                refine ⟨57758091691113546146587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4928690490975022604508757 57758091691113546146587)
                ·
                  rfl

theorem cell23_3037054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_3037054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037054 prefixEnd_3037054 := by exact prefixLift 3037054
  have htrace : WordTrace (prefixWord ++ tailWord_3037054) baseStart_3037054 baseEnd_3037054 := by
    simpa [prefixWord, tailWord_3037054, baseEnd_3037054] using wordTrace_append hprefix tailTrace_3037054
  have hstable : (prefixWord ++ tailWord_3037054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037054).length < 2 ^ (prefixWord ++ tailWord_3037054).sum := by decide
  have hdescent : baseEnd_3037054 < baseStart_3037054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037078 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3037078 : Nat := 118140960795 + 3037078 * 2 ^ 59
def prefixEnd_3037078 : Nat := 4983230072969 + 3 ^ 40 * 3037078 * 2
def baseEnd_3037078 : Nat := 1559480799195773652057739

theorem tailTrace_3037078 : CollatzResearch.WordTrace tailWord_3037078 prefixEnd_3037078 1559480799195773652057739 := by
  unfold tailWord_3037078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923208430699535779522493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73847556594128381648239925 6923208430699535779522493)
  ·
    refine ⟨2596203161512325917320935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6923208430699535779522493 2596203161512325917320935)
    ·
      refine ⟨3894304742268488875981403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596203161512325917320935 3894304742268488875981403)
      ·
        refine ⟨5841457113402733313972105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894304742268488875981403 5841457113402733313972105)
        ·
          refine ⟨4381092835052049985479079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841457113402733313972105 4381092835052049985479079)
          ·
            refine ⟨6571639252578074978218619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381092835052049985479079 6571639252578074978218619)
            ·
              refine ⟨9857458878867112467327929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571639252578074978218619 9857458878867112467327929)
              ·
                refine ⟨7393094159150334350495947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857458878867112467327929 7393094159150334350495947)
                ·
                  refine ⟨11089641238725501525743921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7393094159150334350495947 11089641238725501525743921)
                  ·
                    refine ⟨8317230929044126144307941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11089641238725501525743921 8317230929044126144307941)
                    ·
                      refine ⟨1559480799195773652057739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8317230929044126144307941 1559480799195773652057739)
                      ·
                        rfl

theorem cell23_3037078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3037078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037078 prefixEnd_3037078 := by exact prefixLift 3037078
  have htrace : WordTrace (prefixWord ++ tailWord_3037078) baseStart_3037078 baseEnd_3037078 := by
    simpa [prefixWord, tailWord_3037078, baseEnd_3037078] using wordTrace_append hprefix tailTrace_3037078
  have hstable : (prefixWord ++ tailWord_3037078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037078).length < 2 ^ (prefixWord ++ tailWord_3037078).sum := by decide
  have hdescent : baseEnd_3037078 < baseStart_3037078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037117 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3037117 : Nat := 118140960795 + 3037117 * 2 ^ 59
def prefixEnd_3037117 : Nat := 4983230072969 + 3 ^ 40 * 3037117 * 2
def baseEnd_3037117 : Nat := 1559500824941298999470059

theorem tailTrace_3037117 : CollatzResearch.WordTrace tailWord_3037117 prefixEnd_3037117 1559500824941298999470059 := by
  unfold tailWord_3037117
  simp only [CollatzResearch.WordTrace]
  refine ⟨110772757338051282133029605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73848504892034188088686403 110772757338051282133029605)
  ·
    refine ⟨20769892000884615399943051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110772757338051282133029605 20769892000884615399943051)
    ·
      refine ⟨31154838001326923099914577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769892000884615399943051 31154838001326923099914577)
      ·
        refine ⟨23366128500995192324935933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31154838001326923099914577 23366128500995192324935933)
        ·
          refine ⟨8762298187873197121850975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23366128500995192324935933 8762298187873197121850975)
          ·
            refine ⟨13143447281809795682776463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762298187873197121850975 13143447281809795682776463)
            ·
              refine ⟨19715170922714693524164695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143447281809795682776463 19715170922714693524164695)
              ·
                refine ⟨29572756384072040286247043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19715170922714693524164695 29572756384072040286247043)
                ·
                  refine ⟨44359134576108060429370565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29572756384072040286247043 44359134576108060429370565)
                  ·
                    refine ⟨8317337733020261330506981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44359134576108060429370565 8317337733020261330506981)
                    ·
                      refine ⟨1559500824941298999470059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8317337733020261330506981 1559500824941298999470059)
                      ·
                        rfl

theorem cell23_3037117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3037117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037117 prefixEnd_3037117 := by exact prefixLift 3037117
  have htrace : WordTrace (prefixWord ++ tailWord_3037117) baseStart_3037117 baseEnd_3037117 := by
    simpa [prefixWord, tailWord_3037117, baseEnd_3037117] using wordTrace_append hprefix tailTrace_3037117
  have hstable : (prefixWord ++ tailWord_3037117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037117).length < 2 ^ (prefixWord ++ tailWord_3037117).sum := by decide
  have hdescent : baseEnd_3037117 < baseStart_3037117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037142 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3037142 : Nat := 118140960795 + 3037142 * 2 ^ 59
def prefixEnd_3037142 : Nat := 4983230072969 + 3 ^ 40 * 3037142 * 2
def baseEnd_3037142 : Nat := 1559513661957661401657445

theorem tailTrace_3037142 : CollatzResearch.WordTrace tailWord_3037142 prefixEnd_3037142 1559513661957661401657445 := by
  unfold tailWord_3037142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923354322685044462668105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73849112775307140935126453 6923354322685044462668105)
  ·
    refine ⟨5192515742013783347001079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6923354322685044462668105 5192515742013783347001079)
    ·
      refine ⟨7788773613020675020501619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192515742013783347001079 7788773613020675020501619)
      ·
        refine ⟨11683160419531012530752429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788773613020675020501619 11683160419531012530752429)
        ·
          refine ⟨4381185157324129699032161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11683160419531012530752429 4381185157324129699032161)
          ·
            refine ⟨3285888867993097274274121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381185157324129699032161 3285888867993097274274121)
            ·
              refine ⟨2464416650994822955705591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285888867993097274274121 2464416650994822955705591)
              ·
                refine ⟨3696624976492234433558387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464416650994822955705591 3696624976492234433558387)
                ·
                  refine ⟨5544937464738351650337581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696624976492234433558387 5544937464738351650337581)
                  ·
                    refine ⟨2079351549276881868876593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5544937464738351650337581 2079351549276881868876593)
                    ·
                      refine ⟨1559513661957661401657445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079351549276881868876593 1559513661957661401657445)
                      ·
                        rfl

theorem cell23_3037142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3037142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037142 prefixEnd_3037142 := by exact prefixLift 3037142
  have htrace : WordTrace (prefixWord ++ tailWord_3037142) baseStart_3037142 baseEnd_3037142 := by
    simpa [prefixWord, tailWord_3037142, baseEnd_3037142] using wordTrace_append hprefix tailTrace_3037142
  have hstable : (prefixWord ++ tailWord_3037142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037142).length < 2 ^ (prefixWord ++ tailWord_3037142).sum := by decide
  have hdescent : baseEnd_3037142 < baseStart_3037142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037144 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 5]
def baseStart_3037144 : Nat := 118140960795 + 3037144 * 2 ^ 59
def prefixEnd_3037144 : Nat := 4983230072969 + 3 ^ 40 * 3037144 * 2
def baseEnd_3037144 : Nat := 173279409879885599314715

theorem tailTrace_3037144 : CollatzResearch.WordTrace tailWord_3037144 prefixEnd_3037144 173279409879885599314715 := by
  unfold tailWord_3037144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55386871054476732872131243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73849161405968977162841657 55386871054476732872131243)
  ·
    refine ⟨83080306581715099308196865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55386871054476732872131243 83080306581715099308196865)
    ·
      refine ⟨62310229936286324481147649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83080306581715099308196865 62310229936286324481147649)
      ·
        refine ⟨46732672452214743360860737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62310229936286324481147649 46732672452214743360860737)
        ·
          refine ⟨35049504339161057520645553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46732672452214743360860737 35049504339161057520645553)
          ·
            refine ⟨26287128254370793140484165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35049504339161057520645553 26287128254370793140484165)
            ·
              refine ⟨4928836547694523713840781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26287128254370793140484165 4928836547694523713840781)
              ·
                refine ⟨1848313705385446392690293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4928836547694523713840781 1848313705385446392690293)
                ·
                  refine ⟨173279409879885599314715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848313705385446392690293 173279409879885599314715)
                  ·
                    rfl

theorem cell23_3037144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 5].length) (baseStart_3037144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037144 prefixEnd_3037144 := by exact prefixLift 3037144
  have htrace : WordTrace (prefixWord ++ tailWord_3037144) baseStart_3037144 baseEnd_3037144 := by
    simpa [prefixWord, tailWord_3037144, baseEnd_3037144] using wordTrace_append hprefix tailTrace_3037144
  have hstable : (prefixWord ++ tailWord_3037144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037144).length < 2 ^ (prefixWord ++ tailWord_3037144).sum := by decide
  have hdescent : baseEnd_3037144 < baseStart_3037144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037177 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3037177 : Nat := 118140960795 + 3037177 * 2 ^ 59
def prefixEnd_3037177 : Nat := 4983230072969 + 3 ^ 40 * 3037177 * 2
def baseEnd_3037177 : Nat := 1559531633780568764719783

theorem tailTrace_3037177 : CollatzResearch.WordTrace tailWord_3037177 prefixEnd_3037177 1559531633780568764719783 := by
  unfold tailWord_3037177
  simp only [CollatzResearch.WordTrace]
  refine ⟨110774945717833912380213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73849963811889274920142523 110774945717833912380213785)
  ·
    refine ⟨83081209288375434285160339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110774945717833912380213785 83081209288375434285160339)
    ·
      refine ⟨124621813932563151427740509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83081209288375434285160339 124621813932563151427740509)
      ·
        refine ⟨46733180224711181785402691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124621813932563151427740509 46733180224711181785402691)
        ·
          refine ⟨70099770337066772678104037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46733180224711181785402691 70099770337066772678104037)
          ·
            refine ⟨13143706938200019877144507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70099770337066772678104037 13143706938200019877144507)
            ·
              refine ⟨19715560407300029815716761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143706938200019877144507 19715560407300029815716761)
              ·
                refine ⟨14786670305475022361787571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19715560407300029815716761 14786670305475022361787571)
                ·
                  refine ⟨22180005458212533542681357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14786670305475022361787571 22180005458212533542681357)
                  ·
                    refine ⟨8317502046829700078505509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22180005458212533542681357 8317502046829700078505509)
                    ·
                      refine ⟨1559531633780568764719783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8317502046829700078505509 1559531633780568764719783)
                      ·
                        rfl

theorem cell23_3037177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3037177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037177 prefixEnd_3037177 := by exact prefixLift 3037177
  have htrace : WordTrace (prefixWord ++ tailWord_3037177) baseStart_3037177 baseEnd_3037177 := by
    simpa [prefixWord, tailWord_3037177, baseEnd_3037177] using wordTrace_append hprefix tailTrace_3037177
  have hstable : (prefixWord ++ tailWord_3037177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037177).length < 2 ^ (prefixWord ++ tailWord_3037177).sum := by decide
  have hdescent : baseEnd_3037177 < baseStart_3037177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037221 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_3037221 : Nat := 118140960795 + 3037221 * 2 ^ 59
def prefixEnd_3037221 : Nat := 4983230072969 + 3 ^ 40 * 3037221 * 2
def baseEnd_3037221 : Nat := 519851408976455530856527

theorem tailTrace_3037221 : CollatzResearch.WordTrace tailWord_3037221 prefixEnd_3037221 519851408976455530856527 := by
  unfold tailWord_3037221
  simp only [CollatzResearch.WordTrace]
  refine ⟨110776550529674507894815517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73851033686449671929877011 110776550529674507894815517)
  ·
    refine ⟨41541206448627940460555819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110776550529674507894815517 41541206448627940460555819)
    ·
      refine ⟨62311809672941910690833729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41541206448627940460555819 62311809672941910690833729)
      ·
        refine ⟨46733857254706433018125297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62311809672941910690833729 46733857254706433018125297)
        ·
          refine ⟨35050392941029824763593973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46733857254706433018125297 35050392941029824763593973)
          ·
            refine ⟨3285974338221546071586935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35050392941029824763593973 3285974338221546071586935)
            ·
              refine ⟨4928961507332319107380403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285974338221546071586935 4928961507332319107380403)
              ·
                refine ⟨7393442260998478661070605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928961507332319107380403 7393442260998478661070605)
                ·
                  refine ⟨2772540847874429497901477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7393442260998478661070605 2772540847874429497901477)
                  ·
                    refine ⟨519851408976455530856527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772540847874429497901477 519851408976455530856527)
                    ·
                      rfl

theorem cell23_3037221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_3037221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037221 prefixEnd_3037221 := by exact prefixLift 3037221
  have htrace : WordTrace (prefixWord ++ tailWord_3037221) baseStart_3037221 baseEnd_3037221 := by
    simpa [prefixWord, tailWord_3037221, baseEnd_3037221] using wordTrace_append hprefix tailTrace_3037221
  have hstable : (prefixWord ++ tailWord_3037221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037221).length < 2 ^ (prefixWord ++ tailWord_3037221).sum := by decide
  have hdescent : baseEnd_3037221 < baseStart_3037221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037227 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3]
def baseStart_3037227 : Nat := 118140960795 + 3037227 * 2 ^ 59
def prefixEnd_3037227 : Nat := 4983230072969 + 3 ^ 40 * 3037227 * 2
def baseEnd_3037227 : Nat := 1559557307813293569094553

theorem tailTrace_3037227 : CollatzResearch.WordTrace tailWord_3037227 prefixEnd_3037227 1559557307813293569094553 := by
  unfold tailWord_3037227
  simp only [CollatzResearch.WordTrace]
  refine ⟨110776769367652770919533935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73851179578435180613022623 110776769367652770919533935)
  ·
    refine ⟨166165154051479156379300903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110776769367652770919533935 166165154051479156379300903)
    ·
      refine ⟨249247731077218734568951355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166165154051479156379300903 249247731077218734568951355)
      ·
        refine ⟨373871596615828101853427033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249247731077218734568951355 373871596615828101853427033)
        ·
          refine ⟨280403697461871076390070275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373871596615828101853427033 280403697461871076390070275)
          ·
            refine ⟨420605546192806614585105413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280403697461871076390070275 420605546192806614585105413)
            ·
              refine ⟨78863539911151240234707265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420605546192806614585105413 78863539911151240234707265)
              ·
                refine ⟨59147654933363430176030449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78863539911151240234707265 59147654933363430176030449)
                ·
                  refine ⟨44360741200022572632022837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59147654933363430176030449 44360741200022572632022837)
                  ·
                    refine ⟨4158819487502116184252141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44360741200022572632022837 4158819487502116184252141)
                    ·
                      refine ⟨1559557307813293569094553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4158819487502116184252141 1559557307813293569094553)
                      ·
                        rfl

theorem cell23_3037227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].length) (baseStart_3037227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037227 prefixEnd_3037227 := by exact prefixLift 3037227
  have htrace : WordTrace (prefixWord ++ tailWord_3037227) baseStart_3037227 baseEnd_3037227 := by
    simpa [prefixWord, tailWord_3037227, baseEnd_3037227] using wordTrace_append hprefix tailTrace_3037227
  have hstable : (prefixWord ++ tailWord_3037227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037227).length < 2 ^ (prefixWord ++ tailWord_3037227).sum := by decide
  have hdescent : baseEnd_3037227 < baseStart_3037227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037234 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3037234 : Nat := 118140960795 + 3037234 * 2 ^ 59
def prefixEnd_3037234 : Nat := 4983230072969 + 3 ^ 40 * 3037234 * 2
def baseEnd_3037234 : Nat := 173284544686430560189669

theorem tailTrace_3037234 : CollatzResearch.WordTrace tailWord_3037234 prefixEnd_3037234 173284544686430560189669 := by
  unfold tailWord_3037234
  simp only [CollatzResearch.WordTrace]
  refine ⟨27694256169656852778759689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73851349785751607410025837 27694256169656852778759689)
  ·
    refine ⟨20770692127242639584069767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27694256169656852778759689 20770692127242639584069767)
    ·
      refine ⟨31156038190863959376104651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20770692127242639584069767 31156038190863959376104651)
      ·
        refine ⟨46734057286295939064156977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156038190863959376104651 46734057286295939064156977)
        ·
          refine ⟨35050542964721954298117733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46734057286295939064156977 35050542964721954298117733)
          ·
            refine ⟨6571976805885366430897075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35050542964721954298117733 6571976805885366430897075)
            ·
              refine ⟨9857965208828049646345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571976805885366430897075 9857965208828049646345613)
              ·
                refine ⟨3696736953310518617379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9857965208828049646345613 3696736953310518617379605)
                ·
                  refine ⟨173284544686430560189669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3696736953310518617379605 173284544686430560189669)
                  ·
                    rfl

theorem cell23_3037234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3037234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037234 prefixEnd_3037234 := by exact prefixLift 3037234
  have htrace : WordTrace (prefixWord ++ tailWord_3037234) baseStart_3037234 baseEnd_3037234 := by
    simpa [prefixWord, tailWord_3037234, baseEnd_3037234] using wordTrace_append hprefix tailTrace_3037234
  have hstable : (prefixWord ++ tailWord_3037234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037234).length < 2 ^ (prefixWord ++ tailWord_3037234).sum := by decide
  have hdescent : baseEnd_3037234 < baseStart_3037234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037237 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3037237 : Nat := 118140960795 + 3037237 * 2 ^ 59
def prefixEnd_3037237 : Nat := 4983230072969 + 3 ^ 40 * 3037237 * 2
def baseEnd_3037237 : Nat := 1559562442619838529969507

theorem tailTrace_3037237 : CollatzResearch.WordTrace tailWord_3037237 prefixEnd_3037237 1559562442619838529969507 := by
  unfold tailWord_3037237
  simp only [CollatzResearch.WordTrace]
  refine ⟨110777134097616542627397965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73851422731744361751598643 110777134097616542627397965)
  ·
    refine ⟨41541425286606203485274237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110777134097616542627397965 41541425286606203485274237)
    ·
      refine ⟨15578034482477326306977839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41541425286606203485274237 15578034482477326306977839)
      ·
        refine ⟨23367051723715989460466759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15578034482477326306977839 23367051723715989460466759)
        ·
          refine ⟨35050577585573984190700139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23367051723715989460466759 35050577585573984190700139)
          ·
            refine ⟨52575866378360976286050209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35050577585573984190700139 52575866378360976286050209)
            ·
              refine ⟨39431899783770732214537657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52575866378360976286050209 39431899783770732214537657)
              ·
                refine ⟨29573924837828049160903243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39431899783770732214537657 29573924837828049160903243)
                ·
                  refine ⟨44360887256742073741354865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29573924837828049160903243 44360887256742073741354865)
                  ·
                    refine ⟨33270665442556555306016149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44360887256742073741354865 33270665442556555306016149)
                    ·
                      refine ⟨1559562442619838529969507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33270665442556555306016149 1559562442619838529969507)
                      ·
                        rfl

theorem cell23_3037237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3037237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037237 prefixEnd_3037237 := by exact prefixLift 3037237
  have htrace : WordTrace (prefixWord ++ tailWord_3037237) baseStart_3037237 baseEnd_3037237 := by
    simpa [prefixWord, tailWord_3037237, baseEnd_3037237] using wordTrace_append hprefix tailTrace_3037237
  have hstable : (prefixWord ++ tailWord_3037237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037237).length < 2 ^ (prefixWord ++ tailWord_3037237).sum := by decide
  have hdescent : baseEnd_3037237 < baseStart_3037237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037271 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_3037271 : Nat := 118140960795 + 3037271 * 2 ^ 59
def prefixEnd_3037271 : Nat := 4983230072969 + 3 ^ 40 * 3037271 * 2
def baseEnd_3037271 : Nat := 1559579900962091396944351

theorem tailTrace_3037271 : CollatzResearch.WordTrace tailWord_3037271 prefixEnd_3037271 1559579900962091396944351 := by
  unfold tailWord_3037271
  simp only [CollatzResearch.WordTrace]
  refine ⟨110778374179493366434135667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73852249452995577622757111 110778374179493366434135667)
  ·
    refine ⟨166167561269240049651203501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110778374179493366434135667 166167561269240049651203501)
    ·
      refine ⟨62312835475965018619201313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166167561269240049651203501 62312835475965018619201313)
      ·
        refine ⟨46734626606973763964400985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62312835475965018619201313 46734626606973763964400985)
        ·
          refine ⟨35050969955230322973300739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46734626606973763964400985 35050969955230322973300739)
          ·
            refine ⟨52576454932845484459951109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35050969955230322973300739 52576454932845484459951109)
            ·
              refine ⟨9858085299908528336240833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52576454932845484459951109 9858085299908528336240833)
              ·
                refine ⟨7393563974931396252180625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9858085299908528336240833 7393563974931396252180625)
                ·
                  refine ⟨5545172981198547189135469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393563974931396252180625 5545172981198547189135469)
                  ·
                    refine ⟨2079439867949455195925801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5545172981198547189135469 2079439867949455195925801)
                    ·
                      refine ⟨1559579900962091396944351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079439867949455195925801 1559579900962091396944351)
                      ·
                        rfl

theorem cell23_3037271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_3037271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037271 prefixEnd_3037271 := by exact prefixLift 3037271
  have htrace : WordTrace (prefixWord ++ tailWord_3037271) baseStart_3037271 baseEnd_3037271 := by
    simpa [prefixWord, tailWord_3037271, baseEnd_3037271] using wordTrace_append hprefix tailTrace_3037271
  have hstable : (prefixWord ++ tailWord_3037271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037271).length < 2 ^ (prefixWord ++ tailWord_3037271).sum := by decide
  have hdescent : baseEnd_3037271 < baseStart_3037271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037284 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_3037284 : Nat := 118140960795 + 3037284 * 2 ^ 59
def prefixEnd_3037284 : Nat := 4983230072969 + 3 ^ 40 * 3037284 * 2
def baseEnd_3037284 : Nat := 1559586576210599846081791

theorem tailTrace_3037284 : CollatzResearch.WordTrace tailWord_3037284 prefixEnd_3037284 1559586576210599846081791 := by
  unfold tailWord_3037284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55389424164223134827179453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73852565552297513102905937 55389424164223134827179453)
  ·
    refine ⟨20771034061583675560192295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55389424164223134827179453 20771034061583675560192295)
    ·
      refine ⟨31156551092375513340288443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20771034061583675560192295 31156551092375513340288443)
      ·
        refine ⟨46734826638563270010432665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156551092375513340288443 46734826638563270010432665)
        ·
          refine ⟨35051119978922452507824499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46734826638563270010432665 35051119978922452507824499)
          ·
            refine ⟨52576679968383678761736749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35051119978922452507824499 52576679968383678761736749)
            ·
              refine ⟨19716254988143879535651281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52576679968383678761736749 19716254988143879535651281)
              ·
                refine ⟨14787191241107909651738461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19716254988143879535651281 14787191241107909651738461)
                ·
                  refine ⟨5545196715415466119401923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14787191241107909651738461 5545196715415466119401923)
                  ·
                    refine ⟨8317795073123199179102885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5545196715415466119401923 8317795073123199179102885)
                    ·
                      refine ⟨1559586576210599846081791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8317795073123199179102885 1559586576210599846081791)
                      ·
                        rfl

theorem cell23_3037284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_3037284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037284 prefixEnd_3037284 := by exact prefixLift 3037284
  have htrace : WordTrace (prefixWord ++ tailWord_3037284) baseStart_3037284 baseEnd_3037284 := by
    simpa [prefixWord, tailWord_3037284, baseEnd_3037284] using wordTrace_append hprefix tailTrace_3037284
  have hstable : (prefixWord ++ tailWord_3037284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037284).length < 2 ^ (prefixWord ++ tailWord_3037284).sum := by decide
  have hdescent : baseEnd_3037284 < baseStart_3037284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037321 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_3037321 : Nat := 118140960795 + 3037321 * 2 ^ 59
def prefixEnd_3037321 : Nat := 4983230072969 + 3 ^ 40 * 3037321 * 2
def baseEnd_3037321 : Nat := 1559605574994816201319121

theorem tailTrace_3037321 : CollatzResearch.WordTrace tailWord_3037321 prefixEnd_3037321 1559605574994816201319121 := by
  unfold tailWord_3037321
  simp only [CollatzResearch.WordTrace]
  refine ⟨110780197829312224973455817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73853465219541483315637211 110780197829312224973455817)
  ·
    refine ⟨83085148371984168730091863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110780197829312224973455817 83085148371984168730091863)
    ·
      refine ⟨124627722557976253095137795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83085148371984168730091863 124627722557976253095137795)
      ·
        refine ⟨186941583836964379642706693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124627722557976253095137795 186941583836964379642706693)
        ·
          refine ⟨35051546969430821183007505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186941583836964379642706693 35051546969430821183007505)
          ·
            refine ⟨26288660227073115887255629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35051546969430821183007505 26288660227073115887255629)
            ·
              refine ⟨9858247585152418457720861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26288660227073115887255629 9858247585152418457720861)
              ·
                refine ⟨3696842844432156921645323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9858247585152418457720861 3696842844432156921645323)
                ·
                  refine ⟨5545264266648235382467985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696842844432156921645323 5545264266648235382467985)
                  ·
                    refine ⟨4158948199986176536850989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545264266648235382467985 4158948199986176536850989)
                    ·
                      refine ⟨1559605574994816201319121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4158948199986176536850989 1559605574994816201319121)
                      ·
                        rfl

theorem cell23_3037321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_3037321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037321 prefixEnd_3037321 := by exact prefixLift 3037321
  have htrace : WordTrace (prefixWord ++ tailWord_3037321) baseStart_3037321 baseEnd_3037321 := by
    simpa [prefixWord, tailWord_3037321, baseEnd_3037321] using wordTrace_append hprefix tailTrace_3037321
  have hstable : (prefixWord ++ tailWord_3037321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037321).length < 2 ^ (prefixWord ++ tailWord_3037321).sum := by decide
  have hdescent : baseEnd_3037321 < baseStart_3037321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037335 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_3037335 : Nat := 118140960795 + 3037335 * 2 ^ 59
def prefixEnd_3037335 : Nat := 4983230072969 + 3 ^ 40 * 3037335 * 2
def baseEnd_3037335 : Nat := 1559612763723979146544057

theorem tailTrace_3037335 : CollatzResearch.WordTrace tailWord_3037335 prefixEnd_3037335 1559612763723979146544057 := by
  unfold tailWord_3037335
  simp only [CollatzResearch.WordTrace]
  refine ⟨110780708451261505364465459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73853805634174336909643639 110780708451261505364465459)
  ·
    refine ⟨166171062676892258046698189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110780708451261505364465459 166171062676892258046698189)
    ·
      refine ⟨62314148503834596767511821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166171062676892258046698189 62314148503834596767511821)
      ·
        refine ⟨23367805688937973787816933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62314148503834596767511821 23367805688937973787816933)
        ·
          refine ⟨4381463566675870085215675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23367805688937973787816933 4381463566675870085215675)
          ·
            refine ⟨6572195350013805127823513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381463566675870085215675 6572195350013805127823513)
            ·
              refine ⟨4929146512510353845867635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572195350013805127823513 4929146512510353845867635)
              ·
                refine ⟨7393719768765530768801453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929146512510353845867635 7393719768765530768801453)
                ·
                  refine ⟨2772644913287074038300545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7393719768765530768801453 2772644913287074038300545)
                  ·
                    refine ⟨2079483684965305528725409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2772644913287074038300545 2079483684965305528725409)
                    ·
                      refine ⟨1559612763723979146544057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079483684965305528725409 1559612763723979146544057)
                      ·
                        rfl

theorem cell23_3037335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_3037335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037335 prefixEnd_3037335 := by exact prefixLift 3037335
  have htrace : WordTrace (prefixWord ++ tailWord_3037335) baseStart_3037335 baseEnd_3037335 := by
    simpa [prefixWord, tailWord_3037335, baseEnd_3037335] using wordTrace_append hprefix tailTrace_3037335
  have hstable : (prefixWord ++ tailWord_3037335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037335).length < 2 ^ (prefixWord ++ tailWord_3037335).sum := by decide
  have hdescent : baseEnd_3037335 < baseStart_3037335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037337 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_3037337 : Nat := 118140960795 + 3037337 * 2 ^ 59
def prefixEnd_3037337 : Nat := 4983230072969 + 3 ^ 40 * 3037337 * 2
def baseEnd_3037337 : Nat := 519871263561762712906349

theorem tailTrace_3037337 : CollatzResearch.WordTrace tailWord_3037337 prefixEnd_3037337 519871263561762712906349 := by
  unfold tailWord_3037337
  simp only [CollatzResearch.WordTrace]
  refine ⟨110780781397254259706038265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73853854264836173137358843 110780781397254259706038265)
  ·
    refine ⟨83085586047940694779528699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110780781397254259706038265 83085586047940694779528699)
    ·
      refine ⟨124628379071911042169293049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83085586047940694779528699 124628379071911042169293049)
      ·
        refine ⟨93471284303933281626969787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124628379071911042169293049 93471284303933281626969787)
        ·
          refine ⟨140206926455899922440454681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93471284303933281626969787 140206926455899922440454681)
          ·
            refine ⟨105155194841924941830341011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140206926455899922440454681 105155194841924941830341011)
            ·
              refine ⟨157732792262887412745511517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105155194841924941830341011 157732792262887412745511517)
              ·
                refine ⟨59149797098582779779566819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157732792262887412745511517 59149797098582779779566819)
                ·
                  refine ⟨88724695647874169669350229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59149797098582779779566819 88724695647874169669350229)
                  ·
                    refine ⟨519871263561762712906349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88724695647874169669350229 519871263561762712906349)
                    ·
                      rfl

theorem cell23_3037337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_3037337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037337 prefixEnd_3037337 := by exact prefixLift 3037337
  have htrace : WordTrace (prefixWord ++ tailWord_3037337) baseStart_3037337 baseEnd_3037337 := by
    simpa [prefixWord, tailWord_3037337, baseEnd_3037337] using wordTrace_append hprefix tailTrace_3037337
  have hstable : (prefixWord ++ tailWord_3037337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037337).length < 2 ^ (prefixWord ++ tailWord_3037337).sum := by decide
  have hdescent : baseEnd_3037337 < baseStart_3037337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037348 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_3037348 : Nat := 118140960795 + 3037348 * 2 ^ 59
def prefixEnd_3037348 : Nat := 4983230072969 + 3 ^ 40 * 3037348 * 2
def baseEnd_3037348 : Nat := 1559619438972487595681497

theorem tailTrace_3037348 : CollatzResearch.WordTrace tailWord_3037348 prefixEnd_3037348 1559619438972487595681497 := by
  unfold tailWord_3037348
  simp only [CollatzResearch.WordTrace]
  refine ⟨55390591300107204292344349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73854121733476272389792465 55390591300107204292344349)
  ·
    refine ⟨20771471737540201609629131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55390591300107204292344349 20771471737540201609629131)
    ·
      refine ⟨31157207606310302414443697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20771471737540201609629131 31157207606310302414443697)
      ·
        refine ⟨23367905704732726810832773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31157207606310302414443697 23367905704732726810832773)
        ·
          refine ⟨4381482319637386277031145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23367905704732726810832773 4381482319637386277031145)
          ·
            refine ⟨3286111739728039707773359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381482319637386277031145 3286111739728039707773359)
            ·
              refine ⟨4929167609592059561660039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286111739728039707773359 4929167609592059561660039)
              ·
                refine ⟨7393751414388089342490059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929167609592059561660039 7393751414388089342490059)
                ·
                  refine ⟨11090627121582134013735089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7393751414388089342490059 11090627121582134013735089)
                  ·
                    refine ⟨8317970341186600510301317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11090627121582134013735089 8317970341186600510301317)
                    ·
                      refine ⟨1559619438972487595681497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8317970341186600510301317 1559619438972487595681497)
                      ·
                        rfl

theorem cell23_3037348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_3037348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037348 prefixEnd_3037348 := by exact prefixLift 3037348
  have htrace : WordTrace (prefixWord ++ tailWord_3037348) baseStart_3037348 baseEnd_3037348 := by
    simpa [prefixWord, tailWord_3037348, baseEnd_3037348] using wordTrace_append hprefix tailTrace_3037348
  have hstable : (prefixWord ++ tailWord_3037348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037348).length < 2 ^ (prefixWord ++ tailWord_3037348).sum := by decide
  have hdescent : baseEnd_3037348 < baseStart_3037348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037358 : List Nat := [4, 1, 4, 2, 1, 1, 1, 9]
def baseStart_3037358 : Nat := 118140960795 + 3037358 * 2 ^ 59
def prefixEnd_3037358 : Nat := 4983230072969 + 3 ^ 40 * 3037358 * 2
def baseEnd_3037358 : Nat := 57763873102927131724313

theorem tailTrace_3037358 : CollatzResearch.WordTrace tailWord_3037358 prefixEnd_3037358 57763873102927131724313 := by
  unfold tailWord_3037358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847693416272272536569091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73854364886785453528368485 13847693416272272536569091)
  ·
    refine ⟨20771540124408408804853637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13847693416272272536569091 20771540124408408804853637)
    ·
      refine ⟨3894663773326576650910057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20771540124408408804853637 3894663773326576650910057)
      ·
        refine ⟨2920997829994932488182543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3894663773326576650910057 2920997829994932488182543)
        ·
          refine ⟨4381496744992398732273815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920997829994932488182543 4381496744992398732273815)
          ·
            refine ⟨6572245117488598098410723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381496744992398732273815 6572245117488598098410723)
            ·
              refine ⟨9858367676232897147616085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572245117488598098410723 9858367676232897147616085)
              ·
                refine ⟨57763873102927131724313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9858367676232897147616085 57763873102927131724313)
                ·
                  rfl

theorem cell23_3037358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_3037358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037358 prefixEnd_3037358 := by exact prefixLift 3037358
  have htrace : WordTrace (prefixWord ++ tailWord_3037358) baseStart_3037358 baseEnd_3037358 := by
    simpa [prefixWord, tailWord_3037358, baseEnd_3037358] using wordTrace_append hprefix tailTrace_3037358
  have hstable : (prefixWord ++ tailWord_3037358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037358).length < 2 ^ (prefixWord ++ tailWord_3037358).sum := by decide
  have hdescent : baseEnd_3037358 < baseStart_3037358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037441 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3037441 : Nat := 118140960795 + 3037441 * 2 ^ 59
def prefixEnd_3037441 : Nat := 4983230072969 + 3 ^ 40 * 3037441 * 2
def baseEnd_3037441 : Nat := 1559667192673355731818569

theorem tailTrace_3037441 : CollatzResearch.WordTrace tailWord_3037441 prefixEnd_3037441 1559667192673355731818569 := by
  unfold tailWord_3037441
  simp only [CollatzResearch.WordTrace]
  refine ⟨110784574588877485467824177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73856383059251656978549451 110784574588877485467824177)
  ·
    refine ⟨83088430941658114100868133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110784574588877485467824177 83088430941658114100868133)
    ·
      refine ⟨15579080801560896393912775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83088430941658114100868133 15579080801560896393912775)
      ·
        refine ⟨23368621202341344590869163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15579080801560896393912775 23368621202341344590869163)
        ·
          refine ⟨35052931803512016886303745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23368621202341344590869163 35052931803512016886303745)
          ·
            refine ⟨26289698852634012664727809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35052931803512016886303745 26289698852634012664727809)
            ·
              refine ⟨19717274139475509498545857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26289698852634012664727809 19717274139475509498545857)
              ·
                refine ⟨14787955604606632123909393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19717274139475509498545857 14787955604606632123909393)
                ·
                  refine ⟨11090966703454974092932045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14787955604606632123909393 11090966703454974092932045)
                  ·
                    refine ⟨4159112513795615284849517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11090966703454974092932045 4159112513795615284849517)
                    ·
                      refine ⟨1559667192673355731818569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159112513795615284849517 1559667192673355731818569)
                      ·
                        rfl

theorem cell23_3037441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3037441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037441 prefixEnd_3037441 := by exact prefixLift 3037441
  have htrace : WordTrace (prefixWord ++ tailWord_3037441) baseStart_3037441 baseEnd_3037441 := by
    simpa [prefixWord, tailWord_3037441, baseEnd_3037441] using wordTrace_append hprefix tailTrace_3037441
  have hstable : (prefixWord ++ tailWord_3037441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037441).length < 2 ^ (prefixWord ++ tailWord_3037441).sum := by decide
  have hdescent : baseEnd_3037441 < baseStart_3037441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037442 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3037442 : Nat := 118140960795 + 3037442 * 2 ^ 59
def prefixEnd_3037442 : Nat := 4983230072969 + 3 ^ 40 * 3037442 * 2
def baseEnd_3037442 : Nat := 1559667706154010227906065

theorem tailTrace_3037442 : CollatzResearch.WordTrace tailWord_3037442 prefixEnd_3037442 1559667706154010227906065 := by
  unfold tailWord_3037442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696152765468465659652645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73856407374582575092407053 27696152765468465659652645)
  ·
    refine ⟨5193028643525337311184871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27696152765468465659652645 5193028643525337311184871)
    ·
      refine ⟨7789542965288005966777307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5193028643525337311184871 7789542965288005966777307)
      ·
        refine ⟨11684314447932008950165961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7789542965288005966777307 11684314447932008950165961)
        ·
          refine ⟨8763235835949006712624471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11684314447932008950165961 8763235835949006712624471)
          ·
            refine ⟨13144853753923510068936707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8763235835949006712624471 13144853753923510068936707)
            ·
              refine ⟨19717280630885265103405061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144853753923510068936707 19717280630885265103405061)
              ·
                refine ⟨3696990118290987206888449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19717280630885265103405061 3696990118290987206888449)
                ·
                  refine ⟨2772742588718240405166337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3696990118290987206888449 2772742588718240405166337)
                  ·
                    refine ⟨2079556941538680303874753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2772742588718240405166337 2079556941538680303874753)
                    ·
                      refine ⟨1559667706154010227906065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079556941538680303874753 1559667706154010227906065)
                      ·
                        rfl

theorem cell23_3037442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3037442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037442 prefixEnd_3037442 := by exact prefixLift 3037442
  have htrace : WordTrace (prefixWord ++ tailWord_3037442) baseStart_3037442 baseEnd_3037442 := by
    simpa [prefixWord, tailWord_3037442, baseEnd_3037442] using wordTrace_append hprefix tailTrace_3037442
  have hstable : (prefixWord ++ tailWord_3037442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037442).length < 2 ^ (prefixWord ++ tailWord_3037442).sum := by decide
  have hdescent : baseEnd_3037442 < baseStart_3037442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037448 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 5]
def baseStart_3037448 : Nat := 118140960795 + 3037448 * 2 ^ 59
def prefixEnd_3037448 : Nat := 4983230072969 + 3 ^ 40 * 3037448 * 2
def baseEnd_3037448 : Nat := 173296754115326356047893

theorem tailTrace_3037448 : CollatzResearch.WordTrace tailWord_3037448 prefixEnd_3037448 173296754115326356047893 := by
  unfold tailWord_3037448
  simp only [CollatzResearch.WordTrace]
  refine ⟨55392414949926062831664499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73856553266568083775552665 55392414949926062831664499)
  ·
    refine ⟨83088622424889094247496749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55392414949926062831664499 83088622424889094247496749)
    ·
      refine ⟨31158233409333410342811281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83088622424889094247496749 31158233409333410342811281)
      ·
        refine ⟨23368675057000057757108461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31158233409333410342811281 23368675057000057757108461)
        ·
          refine ⟨8763253146375021658915673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23368675057000057757108461 8763253146375021658915673)
          ·
            refine ⟨6572439859781266244186755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8763253146375021658915673 6572439859781266244186755)
            ·
              refine ⟨9858659789671899366280133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572439859781266244186755 9858659789671899366280133)
              ·
                refine ⟨1848498710563481131177525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9858659789671899366280133 1848498710563481131177525)
                ·
                  refine ⟨173296754115326356047893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848498710563481131177525 173296754115326356047893)
                  ·
                    rfl

theorem cell23_3037448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 5].length) (baseStart_3037448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037448 prefixEnd_3037448 := by exact prefixLift 3037448
  have htrace : WordTrace (prefixWord ++ tailWord_3037448) baseStart_3037448 baseEnd_3037448 := by
    simpa [prefixWord, tailWord_3037448, baseEnd_3037448] using wordTrace_append hprefix tailTrace_3037448
  have hstable : (prefixWord ++ tailWord_3037448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037448).length < 2 ^ (prefixWord ++ tailWord_3037448).sum := by decide
  have hdescent : baseEnd_3037448 < baseStart_3037448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037451 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 7, 2]
def baseStart_3037451 : Nat := 118140960795 + 3037451 * 2 ^ 59
def prefixEnd_3037451 : Nat := 4983230072969 + 3 ^ 40 * 3037451 * 2
def baseEnd_3037451 : Nat := 1559672327479900692693523

theorem tailTrace_3037451 : CollatzResearch.WordTrace tailWord_3037451 prefixEnd_3037451 1559672327479900692693523 := by
  unfold tailWord_3037451
  simp only [CollatzResearch.WordTrace]
  refine ⟨110784939318841257175688207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73856626212560838117125471 110784939318841257175688207)
  ·
    refine ⟨166177408978261885763532311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110784939318841257175688207 166177408978261885763532311)
    ·
      refine ⟨249266113467392828645298467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166177408978261885763532311 249266113467392828645298467)
      ·
        refine ⟨373899170201089242967947701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249266113467392828645298467 373899170201089242967947701)
        ·
          refine ⟨35053047206352116528245097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373899170201089242967947701 35053047206352116528245097)
          ·
            refine ⟨26289785404764087396183823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35053047206352116528245097 26289785404764087396183823)
            ·
              refine ⟨39434678107146131094275735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26289785404764087396183823 39434678107146131094275735)
              ·
                refine ⟨59152017160719196641413603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39434678107146131094275735 59152017160719196641413603)
                ·
                  refine ⟨88728025741078794962120405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59152017160719196641413603 88728025741078794962120405)
                  ·
                    refine ⟨2079563103306534256924697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 88728025741078794962120405 2079563103306534256924697)
                    ·
                      refine ⟨1559672327479900692693523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079563103306534256924697 1559672327479900692693523)
                      ·
                        rfl

theorem cell23_3037451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7, 2].length) (baseStart_3037451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037451 prefixEnd_3037451 := by exact prefixLift 3037451
  have htrace : WordTrace (prefixWord ++ tailWord_3037451) baseStart_3037451 baseEnd_3037451 := by
    simpa [prefixWord, tailWord_3037451, baseEnd_3037451] using wordTrace_append hprefix tailTrace_3037451
  have hstable : (prefixWord ++ tailWord_3037451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037451).length < 2 ^ (prefixWord ++ tailWord_3037451).sum := by decide
  have hdescent : baseEnd_3037451 < baseStart_3037451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037491 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 5, 4]
def baseStart_3037491 : Nat := 118140960795 + 3037491 * 2 ^ 59
def prefixEnd_3037491 : Nat := 4983230072969 + 3 ^ 40 * 3037491 * 2
def baseEnd_3037491 : Nat := 519897622235360178731113

theorem tailTrace_3037491 : CollatzResearch.WordTrace tailWord_3037491 prefixEnd_3037491 519897622235360178731113 := by
  unfold tailWord_3037491
  simp only [CollatzResearch.WordTrace]
  refine ⟨110786398238696344007144327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73857598825797562671429551 110786398238696344007144327)
  ·
    refine ⟨166179597358044516010716491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110786398238696344007144327 166179597358044516010716491)
    ·
      refine ⟨249269396037066774016074737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166179597358044516010716491 249269396037066774016074737)
      ·
        refine ⟨186952047027800080512056053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249269396037066774016074737 186952047027800080512056053)
        ·
          refine ⟨17526754408856257548005255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186952047027800080512056053 17526754408856257548005255)
          ·
            refine ⟨26290131613284386322007883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17526754408856257548005255 26290131613284386322007883)
            ·
              refine ⟨39435197419926579483011825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26290131613284386322007883 39435197419926579483011825)
              ·
                refine ⟨29576398064944934612258869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39435197419926579483011825 29576398064944934612258869)
                ·
                  refine ⟨2772787318588587619899269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29576398064944934612258869 2772787318588587619899269)
                  ·
                    refine ⟨519897622235360178731113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772787318588587619899269 519897622235360178731113)
                    ·
                      rfl

theorem cell23_3037491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 4].length) (baseStart_3037491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037491 prefixEnd_3037491 := by exact prefixLift 3037491
  have htrace : WordTrace (prefixWord ++ tailWord_3037491) baseStart_3037491 baseEnd_3037491 := by
    simpa [prefixWord, tailWord_3037491, baseEnd_3037491] using wordTrace_append hprefix tailTrace_3037491
  have hstable : (prefixWord ++ tailWord_3037491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037491).length < 2 ^ (prefixWord ++ tailWord_3037491).sum := by decide
  have hdescent : baseEnd_3037491 < baseStart_3037491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037498 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_3037498 : Nat := 118140960795 + 3037498 * 2 ^ 59
def prefixEnd_3037498 : Nat := 4983230072969 + 3 ^ 40 * 3037498 * 2
def baseEnd_3037498 : Nat := 1559696461070662008805807

theorem tailTrace_3037498 : CollatzResearch.WordTrace tailWord_3037498 prefixEnd_3037498 1559696461070662008805807 := by
  unfold tailWord_3037498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696663387417746050662287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73857769033113989468432765 27696663387417746050662287)
  ·
    refine ⟨41544995081126619075993431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27696663387417746050662287 41544995081126619075993431)
    ·
      refine ⟨62317492621689928613990147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41544995081126619075993431 62317492621689928613990147)
      ·
        refine ⟨93476238932534892920985221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62317492621689928613990147 93476238932534892920985221)
        ·
          refine ⟨17526794799850292422684729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93476238932534892920985221 17526794799850292422684729)
          ·
            refine ⟨13145096099887719317013547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17526794799850292422684729 13145096099887719317013547)
            ·
              refine ⟨19717644149831578975520321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13145096099887719317013547 19717644149831578975520321)
              ·
                refine ⟨14788233112373684231640241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19717644149831578975520321 14788233112373684231640241)
                ·
                  refine ⟨11091174834280263173730181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14788233112373684231640241 11091174834280263173730181)
                  ·
                    refine ⟨2079595281427549345074409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11091174834280263173730181 2079595281427549345074409)
                    ·
                      refine ⟨1559696461070662008805807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079595281427549345074409 1559696461070662008805807)
                      ·
                        rfl

theorem cell23_3037498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_3037498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037498 prefixEnd_3037498 := by exact prefixLift 3037498
  have htrace : WordTrace (prefixWord ++ tailWord_3037498) baseStart_3037498 baseEnd_3037498 := by
    simpa [prefixWord, tailWord_3037498, baseEnd_3037498] using wordTrace_append hprefix tailTrace_3037498
  have hstable : (prefixWord ++ tailWord_3037498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037498).length < 2 ^ (prefixWord ++ tailWord_3037498).sum := by decide
  have hdescent : baseEnd_3037498 < baseStart_3037498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037565 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_3037565 : Nat := 118140960795 + 3037565 * 2 ^ 59
def prefixEnd_3037565 : Nat := 4983230072969 + 3 ^ 40 * 3037565 * 2
def baseEnd_3037565 : Nat := 1559730864274513246667999

theorem tailTrace_3037565 : CollatzResearch.WordTrace tailWord_3037565 prefixEnd_3037565 1559730864274513246667999 := by
  unfold tailWord_3037565
  simp only [CollatzResearch.WordTrace]
  refine ⟨110789097240428254645338149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73859398160285503096892099 110789097240428254645338149)
  ·
    refine ⟨20772955732580297746000903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110789097240428254645338149 20772955732580297746000903)
    ·
      refine ⟨31159433598870446619001355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20772955732580297746000903 31159433598870446619001355)
      ·
        refine ⟨46739150398305669928502033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31159433598870446619001355 46739150398305669928502033)
        ·
          refine ⟨35054362798729252446376525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46739150398305669928502033 35054362798729252446376525)
          ·
            refine ⟨13145386049523469667391197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35054362798729252446376525 13145386049523469667391197)
            ·
              refine ⟨4929519768571301125271699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13145386049523469667391197 4929519768571301125271699)
              ·
                refine ⟨7394279652856951687907549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929519768571301125271699 7394279652856951687907549)
                ·
                  refine ⟨2772854869821356882965331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7394279652856951687907549 2772854869821356882965331)
                  ·
                    refine ⟨4159282304732035324447997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2772854869821356882965331 4159282304732035324447997)
                    ·
                      refine ⟨1559730864274513246667999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159282304732035324447997 1559730864274513246667999)
                      ·
                        rfl

theorem cell23_3037565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_3037565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037565 prefixEnd_3037565 := by exact prefixLift 3037565
  have htrace : WordTrace (prefixWord ++ tailWord_3037565) baseStart_3037565 baseEnd_3037565 := by
    simpa [prefixWord, tailWord_3037565, baseEnd_3037565] using wordTrace_append hprefix tailTrace_3037565
  have hstable : (prefixWord ++ tailWord_3037565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037565).length < 2 ^ (prefixWord ++ tailWord_3037565).sum := by decide
  have hdescent : baseEnd_3037565 < baseStart_3037565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037591 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3037591 : Nat := 118140960795 + 3037591 * 2 ^ 59
def prefixEnd_3037591 : Nat := 4983230072969 + 3 ^ 40 * 3037591 * 2
def baseEnd_3037591 : Nat := 1559744214771530144942879

theorem tailTrace_3037591 : CollatzResearch.WordTrace tailWord_3037591 prefixEnd_3037591 1559744214771530144942879 := by
  unfold tailWord_3037591
  simp only [CollatzResearch.WordTrace]
  refine ⟨110790045538334061085784627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73860030358889374057189751 110790045538334061085784627)
  ·
    refine ⟨166185068307501091628676941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110790045538334061085784627 166185068307501091628676941)
    ·
      refine ⟨62319400615312909360753853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166185068307501091628676941 62319400615312909360753853)
      ·
        refine ⟨23369775230742341010282695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62319400615312909360753853 23369775230742341010282695)
        ·
          refine ⟨35054662846113511515424043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23369775230742341010282695 35054662846113511515424043)
          ·
            refine ⟨52581994269170267273136065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35054662846113511515424043 52581994269170267273136065)
            ·
              refine ⟨39436495701877700454852049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52581994269170267273136065 39436495701877700454852049)
              ·
                refine ⟨29577371776408275341139037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39436495701877700454852049 29577371776408275341139037)
                ·
                  refine ⟨11091514416153103252927139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29577371776408275341139037 11091514416153103252927139)
                  ·
                    refine ⟨16637271624229654879390709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11091514416153103252927139 16637271624229654879390709)
                    ·
                      refine ⟨1559744214771530144942879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16637271624229654879390709 1559744214771530144942879)
                      ·
                        rfl

theorem cell23_3037591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3037591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037591 prefixEnd_3037591 := by exact prefixLift 3037591
  have htrace : WordTrace (prefixWord ++ tailWord_3037591) baseStart_3037591 baseEnd_3037591 := by
    simpa [prefixWord, tailWord_3037591, baseEnd_3037591] using wordTrace_append hprefix tailTrace_3037591
  have hstable : (prefixWord ++ tailWord_3037591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037591).length < 2 ^ (prefixWord ++ tailWord_3037591).sum := by decide
  have hdescent : baseEnd_3037591 < baseStart_3037591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037592 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3037592 : Nat := 118140960795 + 3037592 * 2 ^ 59
def prefixEnd_3037592 : Nat := 4983230072969 + 3 ^ 40 * 3037592 * 2
def baseEnd_3037592 : Nat := 1559744728252184641030375

theorem tailTrace_3037592 : CollatzResearch.WordTrace tailWord_3037592 prefixEnd_3037592 1559744728252184641030375 := by
  unfold tailWord_3037592
  simp only [CollatzResearch.WordTrace]
  refine ⟨55395041005665219128285515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73860054674220292171047353 55395041005665219128285515)
  ·
    refine ⟨83092561508497828692428273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55395041005665219128285515 83092561508497828692428273)
    ·
      refine ⟨62319421131373371519321205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83092561508497828692428273 62319421131373371519321205)
      ·
        refine ⟨5842445731066253579936363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62319421131373371519321205 5842445731066253579936363)
        ·
          refine ⟨8763668596599380369904545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5842445731066253579936363 8763668596599380369904545)
          ·
            refine ⟨6572751447449535277428409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8763668596599380369904545 6572751447449535277428409)
            ·
              refine ⟨4929563585587151458071307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572751447449535277428409 4929563585587151458071307)
              ·
                refine ⟨7394345378380727187106961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929563585587151458071307 7394345378380727187106961)
                ·
                  refine ⟨5545759033785545390330221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7394345378380727187106961 5545759033785545390330221)
                  ·
                    refine ⟨2079659637669579521373833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5545759033785545390330221 2079659637669579521373833)
                    ·
                      refine ⟨1559744728252184641030375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079659637669579521373833 1559744728252184641030375)
                      ·
                        rfl

theorem cell23_3037592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3037592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037592 prefixEnd_3037592 := by exact prefixLift 3037592
  have htrace : WordTrace (prefixWord ++ tailWord_3037592) baseStart_3037592 baseEnd_3037592 := by
    simpa [prefixWord, tailWord_3037592, baseEnd_3037592] using wordTrace_append hprefix tailTrace_3037592
  have hstable : (prefixWord ++ tailWord_3037592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037592).length < 2 ^ (prefixWord ++ tailWord_3037592).sum := by decide
  have hdescent : baseEnd_3037592 < baseStart_3037592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037605 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_3037605 : Nat := 118140960795 + 3037605 * 2 ^ 59
def prefixEnd_3037605 : Nat := 4983230072969 + 3 ^ 40 * 3037605 * 2
def baseEnd_3037605 : Nat := 1559751403500693090167815

theorem tailTrace_3037605 : CollatzResearch.WordTrace tailWord_3037605 prefixEnd_3037605 1559751403500693090167815 := by
  unfold tailWord_3037605
  simp only [CollatzResearch.WordTrace]
  refine ⟨110790556160283341476794269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73860370773522227651196179 110790556160283341476794269)
  ·
    refine ⟨41546458560106253053797851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110790556160283341476794269 41546458560106253053797851)
    ·
      refine ⟨62319687840159379580696777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41546458560106253053797851 62319687840159379580696777)
      ·
        refine ⟨46739765880119534685522583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62319687840159379580696777 46739765880119534685522583)
        ·
          refine ⟨70109648820179302028283875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46739765880119534685522583 70109648820179302028283875)
          ·
            refine ⟨105164473230268953042425813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70109648820179302028283875 105164473230268953042425813)
            ·
              refine ⟨2464792341334428586931855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 105164473230268953042425813 2464792341334428586931855)
              ·
                refine ⟨3697188512001642880397783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464792341334428586931855 3697188512001642880397783)
                ·
                  refine ⟨5545782768002464320596675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697188512001642880397783 5545782768002464320596675)
                  ·
                    refine ⟨8318674152003696480895013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5545782768002464320596675 8318674152003696480895013)
                    ·
                      refine ⟨1559751403500693090167815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8318674152003696480895013 1559751403500693090167815)
                      ·
                        rfl

theorem cell23_3037605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_3037605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037605 prefixEnd_3037605 := by exact prefixLift 3037605
  have htrace : WordTrace (prefixWord ++ tailWord_3037605) baseStart_3037605 baseEnd_3037605 := by
    simpa [prefixWord, tailWord_3037605, baseEnd_3037605] using wordTrace_append hprefix tailTrace_3037605
  have hstable : (prefixWord ++ tailWord_3037605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037605).length < 2 ^ (prefixWord ++ tailWord_3037605).sum := by decide
  have hdescent : baseEnd_3037605 < baseStart_3037605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037610 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3037610 : Nat := 118140960795 + 3037610 * 2 ^ 59
def prefixEnd_3037610 : Nat := 4983230072969 + 3 ^ 40 * 3037610 * 2
def baseEnd_3037610 : Nat := 519917990301321856868431

theorem tailTrace_3037610 : CollatzResearch.WordTrace tailWord_3037610 prefixEnd_3037610 519917990301321856868431 := by
  unfold tailWord_3037610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27697684631316306832681571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73860492350176818220484189 27697684631316306832681571)
  ·
    refine ⟨41546526946974460249022357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27697684631316306832681571 41546526946974460249022357)
    ·
      refine ⟨1947493450639427824172923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41546526946974460249022357 1947493450639427824172923)
      ·
        refine ⟨2921240175959141736259385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947493450639427824172923 2921240175959141736259385)
        ·
          refine ⟨2190930131969356302194539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921240175959141736259385 2190930131969356302194539)
          ·
            refine ⟨3286395197954034453291809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190930131969356302194539 3286395197954034453291809)
            ·
              refine ⟨2464796398465525839968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286395197954034453291809 2464796398465525839968857)
              ·
                refine ⟨1848597298849144379976643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464796398465525839968857 1848597298849144379976643)
                ·
                  refine ⟨2772895948273716569964965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848597298849144379976643 2772895948273716569964965)
                  ·
                    refine ⟨519917990301321856868431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772895948273716569964965 519917990301321856868431)
                    ·
                      rfl

theorem cell23_3037610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3037610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037610 prefixEnd_3037610 := by exact prefixLift 3037610
  have htrace : WordTrace (prefixWord ++ tailWord_3037610) baseStart_3037610 baseEnd_3037610 := by
    simpa [prefixWord, tailWord_3037610, baseEnd_3037610] using wordTrace_append hprefix tailTrace_3037610
  have hstable : (prefixWord ++ tailWord_3037610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037610).length < 2 ^ (prefixWord ++ tailWord_3037610).sum := by decide
  have hdescent : baseEnd_3037610 < baseStart_3037610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037628 : List Nat := [2, 2, 2, 4, 1, 1, 3, 8]
def baseStart_3037628 : Nat := 118140960795 + 3037628 * 2 ^ 59
def prefixEnd_3037628 : Nat := 4983230072969 + 3 ^ 40 * 3037628 * 2
def baseEnd_3037628 : Nat := 57769007909472092599267

theorem tailTrace_3037628 : CollatzResearch.WordTrace tailWord_3037628 prefixEnd_3037628 57769007909472092599267 := by
  unfold tailWord_3037628
  simp only [CollatzResearch.WordTrace]
  refine ⟨55395697519600008202440769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73860930026133344269921025 55395697519600008202440769)
  ·
    refine ⟨41546773139700006151830577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55395697519600008202440769 41546773139700006151830577)
    ·
      refine ⟨31160079854775004613872933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41546773139700006151830577 31160079854775004613872933)
      ·
        refine ⟨5842514972770313365101175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31160079854775004613872933 5842514972770313365101175)
        ·
          refine ⟨8763772459155470047651763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5842514972770313365101175 8763772459155470047651763)
          ·
            refine ⟨13145658688733205071477645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8763772459155470047651763 13145658688733205071477645)
            ·
              refine ⟨4929622008274951901804117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13145658688733205071477645 4929622008274951901804117)
              ·
                refine ⟨57769007909472092599267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4929622008274951901804117 57769007909472092599267)
                ·
                  rfl

theorem cell23_3037628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 8].length) (baseStart_3037628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037628 prefixEnd_3037628 := by exact prefixLift 3037628
  have htrace : WordTrace (prefixWord ++ tailWord_3037628) baseStart_3037628 baseEnd_3037628 := by
    simpa [prefixWord, tailWord_3037628, baseEnd_3037628] using wordTrace_append hprefix tailTrace_3037628
  have hstable : (prefixWord ++ tailWord_3037628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037628).length < 2 ^ (prefixWord ++ tailWord_3037628).sum := by decide
  have hdescent : baseEnd_3037628 < baseStart_3037628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037666 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3037666 : Nat := 118140960795 + 3037666 * 2 ^ 59
def prefixEnd_3037666 : Nat := 4983230072969 + 3 ^ 40 * 3037666 * 2
def baseEnd_3037666 : Nat := 519927575273539117168345

theorem tailTrace_3037666 : CollatzResearch.WordTrace tailWord_3037666 prefixEnd_3037666 519927575273539117168345 := by
  unfold tailWord_3037666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27698195253265587223691213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73861854008708232596509901 27698195253265587223691213)
  ·
    refine ⟨10386823219974595208884205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27698195253265587223691213 10386823219974595208884205)
    ·
      refine ⟨3895058707490473203331577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10386823219974595208884205 3895058707490473203331577)
      ·
        refine ⟨2921294030617854902498683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3895058707490473203331577 2921294030617854902498683)
        ·
          refine ⟨4381941045926782353748025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921294030617854902498683 4381941045926782353748025)
          ·
            refine ⟨3286455784445086765311019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381941045926782353748025 3286455784445086765311019)
            ·
              refine ⟨4929683676667630147966529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286455784445086765311019 4929683676667630147966529)
              ·
                refine ⟨3697262757500722610974897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929683676667630147966529 3697262757500722610974897)
                ·
                  refine ⟨2772947068125541958231173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697262757500722610974897 2772947068125541958231173)
                  ·
                    refine ⟨519927575273539117168345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2772947068125541958231173 519927575273539117168345)
                    ·
                      rfl

theorem cell23_3037666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3037666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037666 prefixEnd_3037666 := by exact prefixLift 3037666
  have htrace : WordTrace (prefixWord ++ tailWord_3037666) baseStart_3037666 baseEnd_3037666 := by
    simpa [prefixWord, tailWord_3037666, baseEnd_3037666] using wordTrace_append hprefix tailTrace_3037666
  have hstable : (prefixWord ++ tailWord_3037666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037666).length < 2 ^ (prefixWord ++ tailWord_3037666).sum := by decide
  have hdescent : baseEnd_3037666 < baseStart_3037666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037672 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3037672 : Nat := 118140960795 + 3037672 * 2 ^ 59
def prefixEnd_3037672 : Nat := 4983230072969 + 3 ^ 40 * 3037672 * 2
def baseEnd_3037672 : Nat := 1559785806704544328030007

theorem tailTrace_3037672 : CollatzResearch.WordTrace tailWord_3037672 prefixEnd_3037672 1559785806704544328030007 := by
  unfold tailWord_3037672
  simp only [CollatzResearch.WordTrace]
  refine ⟨55396499925520305959741635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73861999900693741279655513 55396499925520305959741635)
  ·
    refine ⟨83094749888280458939612453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55396499925520305959741635 83094749888280458939612453)
    ·
      refine ⟨15580265604052586051177335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83094749888280458939612453 15580265604052586051177335)
      ·
        refine ⟨23370398406078879076766003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15580265604052586051177335 23370398406078879076766003)
        ·
          refine ⟨35055597609118318615149005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23370398406078879076766003 35055597609118318615149005)
          ·
            refine ⟨13145849103419369480680877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35055597609118318615149005 13145849103419369480680877)
            ·
              refine ⟨4929693413782263555255329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13145849103419369480680877 4929693413782263555255329)
              ·
                refine ⟨3697270060336697666441497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929693413782263555255329 3697270060336697666441497)
                ·
                  refine ⟨2772952545252523249831123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697270060336697666441497 2772952545252523249831123)
                  ·
                    refine ⟨4159428817878784874746685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2772952545252523249831123 4159428817878784874746685)
                    ·
                      refine ⟨1559785806704544328030007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159428817878784874746685 1559785806704544328030007)
                      ·
                        rfl

theorem cell23_3037672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3037672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037672 prefixEnd_3037672 := by exact prefixLift 3037672
  have htrace : WordTrace (prefixWord ++ tailWord_3037672) baseStart_3037672 baseEnd_3037672 := by
    simpa [prefixWord, tailWord_3037672, baseEnd_3037672] using wordTrace_append hprefix tailTrace_3037672
  have hstable : (prefixWord ++ tailWord_3037672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037672).length < 2 ^ (prefixWord ++ tailWord_3037672).sum := by decide
  have hdescent : baseEnd_3037672 < baseStart_3037672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_3037711 : Nat := 118140960795 + 3037711 * 2 ^ 59
def prefixEnd_3037711 : Nat := 4983230072969 + 3 ^ 40 * 3037711 * 2
def baseEnd_3037711 : Nat := 1559805832450069675442327

theorem tailTrace_3037711 : CollatzResearch.WordTrace tailWord_3037711 prefixEnd_3037711 1559805832450069675442327 := by
  unfold tailWord_3037711
  simp only [CollatzResearch.WordTrace]
  refine ⟨110794422297899321580152987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73862948198599547720101991 110794422297899321580152987)
  ·
    refine ⟨166191633446848982370229481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110794422297899321580152987 166191633446848982370229481)
    ·
      refine ⟨124643725085136736777672111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166191633446848982370229481 124643725085136736777672111)
      ·
        refine ⟨186965587627705105166508167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124643725085136736777672111 186965587627705105166508167)
        ·
          refine ⟨280448381441557657749762251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186965587627705105166508167 280448381441557657749762251)
          ·
            refine ⟨420672572162336486624643377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280448381441557657749762251 420672572162336486624643377)
            ·
              refine ⟨315504429121752364968482533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420672572162336486624643377 315504429121752364968482533)
              ·
                refine ⟨59157080460328568431590475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315504429121752364968482533 59157080460328568431590475)
                ·
                  refine ⟨88735620690492852647385713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59157080460328568431590475 88735620690492852647385713)
                  ·
                    refine ⟨66551715517869639485539285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88735620690492852647385713 66551715517869639485539285)
                    ·
                      refine ⟨1559805832450069675442327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66551715517869639485539285 1559805832450069675442327)
                      ·
                        rfl

theorem cell23_3037711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_3037711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037711 prefixEnd_3037711 := by exact prefixLift 3037711
  have htrace : WordTrace (prefixWord ++ tailWord_3037711) baseStart_3037711 baseEnd_3037711 := by
    simpa [prefixWord, tailWord_3037711, baseEnd_3037711] using wordTrace_append hprefix tailTrace_3037711
  have hstable : (prefixWord ++ tailWord_3037711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037711).length < 2 ^ (prefixWord ++ tailWord_3037711).sum := by decide
  have hdescent : baseEnd_3037711 < baseStart_3037711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037765 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_3037765 : Nat := 118140960795 + 3037765 * 2 ^ 59
def prefixEnd_3037765 : Nat := 4983230072969 + 3 ^ 40 * 3037765 * 2
def baseEnd_3037765 : Nat := 519944520135137488055693

theorem tailTrace_3037765 : CollatzResearch.WordTrace tailWord_3037765 prefixEnd_3037765 519944520135137488055693 := by
  unfold tailWord_3037765
  simp only [CollatzResearch.WordTrace]
  refine ⟨110796391839703688802618749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73864261226469125868412499 110796391839703688802618749)
  ·
    refine ⟨41548646939888883300982031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110796391839703688802618749 41548646939888883300982031)
    ·
      refine ⟨62322970409833324951473047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41548646939888883300982031 62322970409833324951473047)
      ·
        refine ⟨93484455614749987427209571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62322970409833324951473047 93484455614749987427209571)
        ·
          refine ⟨140226683422124981140814357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93484455614749987427209571 140226683422124981140814357)
          ·
            refine ⟨6573125785412108490975673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140226683422124981140814357 6573125785412108490975673)
            ·
              refine ⟨4929844339059081368231755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573125785412108490975673 4929844339059081368231755)
              ·
                refine ⟨7394766508588622052347633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929844339059081368231755 7394766508588622052347633)
                ·
                  refine ⟨5546074881441466539260725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7394766508588622052347633 5546074881441466539260725)
                  ·
                    refine ⟨519944520135137488055693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5546074881441466539260725 519944520135137488055693)
                    ·
                      rfl

theorem cell23_3037765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_3037765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037765 prefixEnd_3037765 := by exact prefixLift 3037765
  have htrace : WordTrace (prefixWord ++ tailWord_3037765) baseStart_3037765 baseEnd_3037765 := by
    simpa [prefixWord, tailWord_3037765, baseEnd_3037765] using wordTrace_append hprefix tailTrace_3037765
  have hstable : (prefixWord ++ tailWord_3037765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037765).length < 2 ^ (prefixWord ++ tailWord_3037765).sum := by decide
  have hdescent : baseEnd_3037765 < baseStart_3037765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037768 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3037768 : Nat := 118140960795 + 3037768 * 2 ^ 59
def prefixEnd_3037768 : Nat := 4983230072969 + 3 ^ 40 * 3037768 * 2
def baseEnd_3037768 : Nat := 1559835100847375952429565

theorem tailTrace_3037768 : CollatzResearch.WordTrace tailWord_3037768 prefixEnd_3037768 1559835100847375952429565 := by
  unfold tailWord_3037768
  simp only [CollatzResearch.WordTrace]
  refine ⟨55398250629346410157488979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73864334172461880209985305 55398250629346410157488979)
  ·
    refine ⟨83097375944019615236233469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55398250629346410157488979 83097375944019615236233469)
    ·
      refine ⟨31161515979007355713587551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83097375944019615236233469 31161515979007355713587551)
      ·
        refine ⟨46742273968511033570381327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31161515979007355713587551 46742273968511033570381327)
        ·
          refine ⟨70113410952766550355571991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46742273968511033570381327 70113410952766550355571991)
          ·
            refine ⟨105170116429149825533357987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70113410952766550355571991 105170116429149825533357987)
            ·
              refine ⟨157755174643724738300036981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105170116429149825533357987 157755174643724738300036981)
              ·
                refine ⟨14789547622849194215628467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157755174643724738300036981 14789547622849194215628467)
                ·
                  refine ⟨22184321434273791323442701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14789547622849194215628467 22184321434273791323442701)
                  ·
                    refine ⟨8319120537852671746291013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22184321434273791323442701 8319120537852671746291013)
                    ·
                      refine ⟨1559835100847375952429565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8319120537852671746291013 1559835100847375952429565)
                      ·
                        rfl

theorem cell23_3037768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3037768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037768 prefixEnd_3037768 := by exact prefixLift 3037768
  have htrace : WordTrace (prefixWord ++ tailWord_3037768) baseStart_3037768 baseEnd_3037768 := by
    simpa [prefixWord, tailWord_3037768, baseEnd_3037768] using wordTrace_append hprefix tailTrace_3037768
  have hstable : (prefixWord ++ tailWord_3037768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037768).length < 2 ^ (prefixWord ++ tailWord_3037768).sum := by decide
  have hdescent : baseEnd_3037768 < baseStart_3037768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037795 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 3, 4]
def baseStart_3037795 : Nat := 118140960795 + 3037795 * 2 ^ 59
def prefixEnd_3037795 : Nat := 4983230072969 + 3 ^ 40 * 3037795 * 2
def baseEnd_3037795 : Nat := 519949654941682448930647

theorem tailTrace_3037795 : CollatzResearch.WordTrace tailWord_3037795 prefixEnd_3037795 519949654941682448930647 := by
  unfold tailWord_3037795
  simp only [CollatzResearch.WordTrace]
  refine ⟨110797486029595003926210839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73864990686396669284140559 110797486029595003926210839)
  ·
    refine ⟨166196229044392505889316259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110797486029595003926210839 166196229044392505889316259)
    ·
      refine ⟨249294343566588758833974389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166196229044392505889316259 249294343566588758833974389)
      ·
        refine ⟨23371344709367696140685099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249294343566588758833974389 23371344709367696140685099)
        ·
          refine ⟨35057017064051544211027649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23371344709367696140685099 35057017064051544211027649)
          ·
            refine ⟨26292762798038658158270737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35057017064051544211027649 26292762798038658158270737)
            ·
              refine ⟨19719572098528993618703053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26292762798038658158270737 19719572098528993618703053)
              ·
                refine ⟨7394839536948372607013645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19719572098528993618703053 7394839536948372607013645)
                ·
                  refine ⟨2773064826355639727630117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7394839536948372607013645 2773064826355639727630117)
                  ·
                    refine ⟨519949654941682448930647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773064826355639727630117 519949654941682448930647)
                    ·
                      rfl

theorem cell23_3037795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 4].length) (baseStart_3037795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037795 prefixEnd_3037795 := by exact prefixLift 3037795
  have htrace : WordTrace (prefixWord ++ tailWord_3037795) baseStart_3037795 baseEnd_3037795 := by
    simpa [prefixWord, tailWord_3037795, baseEnd_3037795] using wordTrace_append hprefix tailTrace_3037795
  have hstable : (prefixWord ++ tailWord_3037795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037795).length < 2 ^ (prefixWord ++ tailWord_3037795).sum := by decide
  have hdescent : baseEnd_3037795 < baseStart_3037795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037802 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3037802 : Nat := 118140960795 + 3037802 * 2 ^ 59
def prefixEnd_3037802 : Nat := 4983230072969 + 3 ^ 40 * 3037802 * 2
def baseEnd_3037802 : Nat := 1559852559189628819404409

theorem tailTrace_3037802 : CollatzResearch.WordTrace tailWord_3037802 prefixEnd_3037802 1559852559189628819404409 := by
  unfold tailWord_3037802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27699435335142411030428915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73865160893713096081143773 27699435335142411030428915)
  ·
    refine ⟨41549153002713616545643373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27699435335142411030428915 41549153002713616545643373)
    ·
      refine ⟨15580932376017606204616265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41549153002713616545643373 15580932376017606204616265)
      ·
        refine ⟨11685699282013204653462199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15580932376017606204616265 11685699282013204653462199)
        ·
          refine ⟨17528548923019806980193299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685699282013204653462199 17528548923019806980193299)
          ·
            refine ⟨26292823384529710470289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17528548923019806980193299 26292823384529710470289949)
            ·
              refine ⟨9859808769198641426358731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26292823384529710470289949 9859808769198641426358731)
              ·
                refine ⟨14789713153797962139538097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9859808769198641426358731 14789713153797962139538097)
                ·
                  refine ⟨11092284865348471604653573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14789713153797962139538097 11092284865348471604653573)
                  ·
                    refine ⟨2079803412252838425872545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11092284865348471604653573 2079803412252838425872545)
                    ·
                      refine ⟨1559852559189628819404409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079803412252838425872545 1559852559189628819404409)
                      ·
                        rfl

theorem cell23_3037802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3037802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037802 prefixEnd_3037802 := by exact prefixLift 3037802
  have htrace : WordTrace (prefixWord ++ tailWord_3037802) baseStart_3037802 baseEnd_3037802 := by
    simpa [prefixWord, tailWord_3037802, baseEnd_3037802] using wordTrace_append hprefix tailTrace_3037802
  have hstable : (prefixWord ++ tailWord_3037802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037802).length < 2 ^ (prefixWord ++ tailWord_3037802).sum := by decide
  have hdescent : baseEnd_3037802 < baseStart_3037802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037829 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_3037829 : Nat := 118140960795 + 3037829 * 2 ^ 59
def prefixEnd_3037829 : Nat := 4983230072969 + 3 ^ 40 * 3037829 * 2
def baseEnd_3037829 : Nat := 519955474389100071255595

theorem tailTrace_3037829 : CollatzResearch.WordTrace tailWord_3037829 prefixEnd_3037829 519955474389100071255595 := by
  unfold tailWord_3037829
  simp only [CollatzResearch.WordTrace]
  refine ⟨110798726111471827732948541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73865817407647885155299027 110798726111471827732948541)
  ·
    refine ⟨41549522291801935399855703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110798726111471827732948541 41549522291801935399855703)
    ·
      refine ⟨62324283437702903099783555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41549522291801935399855703 62324283437702903099783555)
      ·
        refine ⟨93486425156554354649675333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62324283437702903099783555 93486425156554354649675333)
        ·
          refine ⟨17528704716853941496814125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93486425156554354649675333 17528704716853941496814125)
          ·
            refine ⟨6573264268820228061305297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17528704716853941496814125 6573264268820228061305297)
            ·
              refine ⟨4929948201615171045978973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573264268820228061305297 4929948201615171045978973)
              ·
                refine ⟨1848730575605689142242115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4929948201615171045978973 1848730575605689142242115)
                ·
                  refine ⟨2773095863408533713363173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848730575605689142242115 2773095863408533713363173)
                  ·
                    refine ⟨519955474389100071255595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773095863408533713363173 519955474389100071255595)
                    ·
                      rfl

theorem cell23_3037829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_3037829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037829 prefixEnd_3037829 := by exact prefixLift 3037829
  have htrace : WordTrace (prefixWord ++ tailWord_3037829) baseStart_3037829 baseEnd_3037829 := by
    simpa [prefixWord, tailWord_3037829, baseEnd_3037829] using wordTrace_append hprefix tailTrace_3037829
  have hstable : (prefixWord ++ tailWord_3037829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037829).length < 2 ^ (prefixWord ++ tailWord_3037829).sum := by decide
  have hdescent : baseEnd_3037829 < baseStart_3037829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037842 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3037842 : Nat := 118140960795 + 3037842 * 2 ^ 59
def prefixEnd_3037842 : Nat := 4983230072969 + 3 ^ 40 * 3037842 * 2
def baseEnd_3037842 : Nat := 173319233157312073656025

theorem tailTrace_3037842 : CollatzResearch.WordTrace tailWord_3037842 prefixEnd_3037842 173319233157312073656025 := by
  unfold tailWord_3037842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27699800065106182738292945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73866133506949820635447853 27699800065106182738292945)
  ·
    refine ⟨20774850048829637053719709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27699800065106182738292945 20774850048829637053719709)
    ·
      refine ⟨7790568768311113895144891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20774850048829637053719709 7790568768311113895144891)
      ·
        refine ⟨11685853152466670842717337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7790568768311113895144891 11685853152466670842717337)
        ·
          refine ⟨8764389864350003132038003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11685853152466670842717337 8764389864350003132038003)
          ·
            refine ⟨13146584796525004698057005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764389864350003132038003 13146584796525004698057005)
            ·
              refine ⟨4929969298696876761771377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13146584796525004698057005 4929969298696876761771377)
              ·
                refine ⟨3697476974022657571328533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929969298696876761771377 3697476974022657571328533)
                ·
                  refine ⟨173319233157312073656025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3697476974022657571328533 173319233157312073656025)
                  ·
                    rfl

theorem cell23_3037842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3037842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037842 prefixEnd_3037842 := by exact prefixLift 3037842
  have htrace : WordTrace (prefixWord ++ tailWord_3037842) baseStart_3037842 baseEnd_3037842 := by
    simpa [prefixWord, tailWord_3037842, baseEnd_3037842] using wordTrace_append hprefix tailTrace_3037842
  have hstable : (prefixWord ++ tailWord_3037842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037842).length < 2 ^ (prefixWord ++ tailWord_3037842).sum := by decide
  have hdescent : baseEnd_3037842 < baseStart_3037842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037869 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3037869 : Nat := 118140960795 + 3037869 * 2 ^ 59
def prefixEnd_3037869 : Nat := 4983230072969 + 3 ^ 40 * 3037869 * 2
def baseEnd_3037869 : Nat := 1559886962393480057266601

theorem tailTrace_3037869 : CollatzResearch.WordTrace tailWord_3037869 prefixEnd_3037869 1559886962393480057266601 := by
  unfold tailWord_3037869
  simp only [CollatzResearch.WordTrace]
  refine ⟨110800185031326914564404661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73866790020884609709603107 110800185031326914564404661)
  ·
    refine ⟨10387517346686898240412937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110800185031326914564404661 10387517346686898240412937)
    ·
      refine ⟨7790638010015173680309703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10387517346686898240412937 7790638010015173680309703)
      ·
        refine ⟨11685957015022760520464555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7790638010015173680309703 11685957015022760520464555)
        ·
          refine ⟨17528935522534140780696833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685957015022760520464555 17528935522534140780696833)
          ·
            refine ⟨13146701641900605585522625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17528935522534140780696833 13146701641900605585522625)
            ·
              refine ⟨9860026231425454189141969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13146701641900605585522625 9860026231425454189141969)
              ·
                refine ⟨7395019673569090641856477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860026231425454189141969 7395019673569090641856477)
                ·
                  refine ⟨2773132377588408990696179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7395019673569090641856477 2773132377588408990696179)
                  ·
                    refine ⟨4159698566382613486044269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2773132377588408990696179 4159698566382613486044269)
                    ·
                      refine ⟨1559886962393480057266601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159698566382613486044269 1559886962393480057266601)
                      ·
                        rfl

theorem cell23_3037869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3037869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037869 prefixEnd_3037869 := by exact prefixLift 3037869
  have htrace : WordTrace (prefixWord ++ tailWord_3037869) baseStart_3037869 baseEnd_3037869 := by
    simpa [prefixWord, tailWord_3037869, baseEnd_3037869] using wordTrace_append hprefix tailTrace_3037869
  have hstable : (prefixWord ++ tailWord_3037869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037869).length < 2 ^ (prefixWord ++ tailWord_3037869).sum := by decide
  have hdescent : baseEnd_3037869 < baseStart_3037869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037902 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3037902 : Nat := 118140960795 + 3037902 * 2 ^ 59
def prefixEnd_3037902 : Nat := 4983230072969 + 3 ^ 40 * 3037902 * 2
def baseEnd_3037902 : Nat := 519967969085026142717983

theorem tailTrace_3037902 : CollatzResearch.WordTrace tailWord_3037902 prefixEnd_3037902 519967969085026142717983 := by
  unfold tailWord_3037902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850173580025920150044495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73867592426804907466903973 13850173580025920150044495)
  ·
    refine ⟨20775260370038880225066743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850173580025920150044495 20775260370038880225066743)
    ·
      refine ⟨31162890555058320337600115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775260370038880225066743 31162890555058320337600115)
      ·
        refine ⟨46744335832587480506400173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31162890555058320337600115 46744335832587480506400173)
        ·
          refine ⟨17529125937220305189900065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46744335832587480506400173 17529125937220305189900065)
          ·
            refine ⟨13146844452915228892425049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17529125937220305189900065 13146844452915228892425049)
            ·
              refine ⟨9860133339686421669318787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13146844452915228892425049 9860133339686421669318787)
              ·
                refine ⟨14790200009529632503978181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860133339686421669318787 14790200009529632503978181)
                ·
                  refine ⟨2773162501786806094495909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14790200009529632503978181 2773162501786806094495909)
                  ·
                    refine ⟨519967969085026142717983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773162501786806094495909 519967969085026142717983)
                    ·
                      rfl

theorem cell23_3037902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3037902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037902 prefixEnd_3037902 := by exact prefixLift 3037902
  have htrace : WordTrace (prefixWord ++ tailWord_3037902) baseStart_3037902 baseEnd_3037902 := by
    simpa [prefixWord, tailWord_3037902, baseEnd_3037902] using wordTrace_append hprefix tailTrace_3037902
  have hstable : (prefixWord ++ tailWord_3037902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037902).length < 2 ^ (prefixWord ++ tailWord_3037902).sum := by decide
  have hdescent : baseEnd_3037902 < baseStart_3037902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037919 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 2, 4]
def baseStart_3037919 : Nat := 118140960795 + 3037919 * 2 ^ 59
def prefixEnd_3037919 : Nat := 4983230072969 + 3 ^ 40 * 3037919 * 2
def baseEnd_3037919 : Nat := 519970878808734953880457

theorem tailTrace_3037919 : CollatzResearch.WordTrace tailWord_3037919 prefixEnd_3037919 519970878808734953880457 := by
  unfold tailWord_3037919
  simp only [CollatzResearch.WordTrace]
  refine ⟨110802008681145773103724811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73868005787430515402483207 110802008681145773103724811)
  ·
    refine ⟨166203013021718659655587217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110802008681145773103724811 166203013021718659655587217)
    ·
      refine ⟨124652259766288994741690413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166203013021718659655587217 124652259766288994741690413)
      ·
        refine ⟨46744597412358373028133905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124652259766288994741690413 46744597412358373028133905)
        ·
          refine ⟨35058448059268779771100429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46744597412358373028133905 35058448059268779771100429)
          ·
            refine ⟨13146918022225792414162661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35058448059268779771100429 13146918022225792414162661)
            ·
              refine ⟨2465047129167336077655499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13146918022225792414162661 2465047129167336077655499)
              ·
                refine ⟨3697570693751004116483249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465047129167336077655499 3697570693751004116483249)
                ·
                  refine ⟨2773178020313253087362437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697570693751004116483249 2773178020313253087362437)
                  ·
                    refine ⟨519970878808734953880457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773178020313253087362437 519970878808734953880457)
                    ·
                      rfl

theorem cell23_3037919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_3037919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037919 prefixEnd_3037919 := by exact prefixLift 3037919
  have htrace : WordTrace (prefixWord ++ tailWord_3037919) baseStart_3037919 baseEnd_3037919 := by
    simpa [prefixWord, tailWord_3037919, baseEnd_3037919] using wordTrace_append hprefix tailTrace_3037919
  have hstable : (prefixWord ++ tailWord_3037919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037919).length < 2 ^ (prefixWord ++ tailWord_3037919).sum := by decide
  have hdescent : baseEnd_3037919 < baseStart_3037919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037952 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2]
def baseStart_3037952 : Nat := 118140960795 + 3037952 * 2 ^ 59
def prefixEnd_3037952 : Nat := 4983230072969 + 3 ^ 40 * 3037952 * 2
def baseEnd_3037952 : Nat := 1559929581287803232528719

theorem tailTrace_3037952 : CollatzResearch.WordTrace tailWord_3037952 prefixEnd_3037952 1559929581287803232528719 := by
  unfold tailWord_3037952
  simp only [CollatzResearch.WordTrace]
  refine ⟨55401606145013109869838055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73868808193350813159784073 55401606145013109869838055)
  ·
    refine ⟨83102409217519664804757083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55401606145013109869838055 83102409217519664804757083)
    ·
      refine ⟨124653613826279497207135625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83102409217519664804757083 124653613826279497207135625)
      ·
        refine ⟨93490210369709622905351719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124653613826279497207135625 93490210369709622905351719)
        ·
          refine ⟨140235315554564434358027579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93490210369709622905351719 140235315554564434358027579)
          ·
            refine ⟨210352973331846651537041369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140235315554564434358027579 210352973331846651537041369)
            ·
              refine ⟨157764729998884988652781027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210352973331846651537041369 157764729998884988652781027)
              ·
                refine ⟨236647094998327482979171541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157764729998884988652781027 236647094998327482979171541)
                ·
                  refine ⟨5546416289023300382324333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 236647094998327482979171541 5546416289023300382324333)
                  ·
                    refine ⟨2079906108383737643371625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5546416289023300382324333 2079906108383737643371625)
                    ·
                      refine ⟨1559929581287803232528719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079906108383737643371625 1559929581287803232528719)
                      ·
                        rfl

theorem cell23_3037952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_3037952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037952 prefixEnd_3037952 := by exact prefixLift 3037952
  have htrace : WordTrace (prefixWord ++ tailWord_3037952) baseStart_3037952 baseEnd_3037952 := by
    simpa [prefixWord, tailWord_3037952, baseEnd_3037952] using wordTrace_append hprefix tailTrace_3037952
  have hstable : (prefixWord ++ tailWord_3037952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037952).length < 2 ^ (prefixWord ++ tailWord_3037952).sum := by decide
  have hdescent : baseEnd_3037952 < baseStart_3037952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037960 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_3037960 : Nat := 118140960795 + 3037960 * 2 ^ 59
def prefixEnd_3037960 : Nat := 4983230072969 + 3 ^ 40 * 3037960 * 2
def baseEnd_3037960 : Nat := 1559933689133039201228683

theorem tailTrace_3037960 : CollatzResearch.WordTrace tailWord_3037960 prefixEnd_3037960 1559933689133039201228683 := by
  unfold tailWord_3037960
  simp only [CollatzResearch.WordTrace]
  refine ⟨55401752036998618552983667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73869002715998158070644889 55401752036998618552983667)
  ·
    refine ⟨83102628055497927829475501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55401752036998618552983667 83102628055497927829475501)
    ·
      refine ⟨31163485520811722936053313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83102628055497927829475501 31163485520811722936053313)
      ·
        refine ⟨23372614140608792202039985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31163485520811722936053313 23372614140608792202039985)
        ·
          refine ⟨17529460605456594151529989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23372614140608792202039985 17529460605456594151529989)
          ·
            refine ⟨3286773863523111403411873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17529460605456594151529989 3286773863523111403411873)
            ·
              refine ⟨2465080397642333552558905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286773863523111403411873 2465080397642333552558905)
              ·
                refine ⟨1848810298231750164419179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2465080397642333552558905 1848810298231750164419179)
                ·
                  refine ⟨2773215447347625246628769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848810298231750164419179 2773215447347625246628769)
                  ·
                    refine ⟨2079911585510718934971577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2773215447347625246628769 2079911585510718934971577)
                    ·
                      refine ⟨1559933689133039201228683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079911585510718934971577 1559933689133039201228683)
                      ·
                        rfl

theorem cell23_3037960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_3037960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037960 prefixEnd_3037960 := by exact prefixLift 3037960
  have htrace : WordTrace (prefixWord ++ tailWord_3037960) baseStart_3037960 baseEnd_3037960 := by
    simpa [prefixWord, tailWord_3037960, baseEnd_3037960] using wordTrace_append hprefix tailTrace_3037960
  have hstable : (prefixWord ++ tailWord_3037960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037960).length < 2 ^ (prefixWord ++ tailWord_3037960).sum := by decide
  have hdescent : baseEnd_3037960 < baseStart_3037960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037995 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_3037995 : Nat := 118140960795 + 3037995 * 2 ^ 59
def prefixEnd_3037995 : Nat := 4983230072969 + 3 ^ 40 * 3037995 * 2
def baseEnd_3037995 : Nat := 1559951660955946564291021

theorem tailTrace_3037995 : CollatzResearch.WordTrace tailWord_3037995 prefixEnd_3037995 1559951660955946564291021 := by
  unfold tailWord_3037995
  simp only [CollatzResearch.WordTrace]
  refine ⟨110804780628870438083491439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73869853752580292055660959 110804780628870438083491439)
  ·
    refine ⟨166207170943305657125237159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110804780628870438083491439 166207170943305657125237159)
    ·
      refine ⟨249310756414958485687855739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166207170943305657125237159 249310756414958485687855739)
      ·
        refine ⟨373966134622437728531783609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249310756414958485687855739 373966134622437728531783609)
        ·
          refine ⟨280474600966828296398837707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373966134622437728531783609 280474600966828296398837707)
          ·
            refine ⟨420711901450242444598256561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280474600966828296398837707 420711901450242444598256561)
            ·
              refine ⟨315533926087681833448692421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420711901450242444598256561 315533926087681833448692421)
              ·
                refine ⟨59162611141440343771629829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315533926087681833448692421 59162611141440343771629829)
                ·
                  refine ⟨11092989589020064457180593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59162611141440343771629829 11092989589020064457180593)
                  ·
                    refine ⟨8319742191765048342885445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11092989589020064457180593 8319742191765048342885445)
                    ·
                      refine ⟨1559951660955946564291021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8319742191765048342885445 1559951660955946564291021)
                      ·
                        rfl

theorem cell23_3037995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_3037995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037995 prefixEnd_3037995 := by exact prefixLift 3037995
  have htrace : WordTrace (prefixWord ++ tailWord_3037995) baseStart_3037995 baseEnd_3037995 := by
    simpa [prefixWord, tailWord_3037995, baseEnd_3037995] using wordTrace_append hprefix tailTrace_3037995
  have hstable : (prefixWord ++ tailWord_3037995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037995).length < 2 ^ (prefixWord ++ tailWord_3037995).sum := by decide
  have hdescent : baseEnd_3037995 < baseStart_3037995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037997 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3037997 : Nat := 118140960795 + 3037997 * 2 ^ 59
def prefixEnd_3037997 : Nat := 4983230072969 + 3 ^ 40 * 3037997 * 2
def baseEnd_3037997 : Nat := 1559952687917255556466013

theorem tailTrace_3037997 : CollatzResearch.WordTrace tailWord_3037997 prefixEnd_3037997 1559952687917255556466013 := by
  unfold tailWord_3037997
  simp only [CollatzResearch.WordTrace]
  refine ⟨110804853574863192425064245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73869902383242128283376163 110804853574863192425064245)
  ·
    refine ⟨10387955022643424289849773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110804853574863192425064245 10387955022643424289849773)
    ·
      refine ⟨3895483133491284108693665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10387955022643424289849773 3895483133491284108693665)
      ·
        refine ⟨2921612350118463081520249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3895483133491284108693665 2921612350118463081520249)
        ·
          refine ⟨2191209262588847311140187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921612350118463081520249 2191209262588847311140187)
          ·
            refine ⟨3286813893883270966710281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191209262588847311140187 3286813893883270966710281)
            ·
              refine ⟨2465110420412453225032711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286813893883270966710281 2465110420412453225032711)
              ·
                refine ⟨3697665630618679837549067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465110420412453225032711 3697665630618679837549067)
                ·
                  refine ⟨5546498445928019756323601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697665630618679837549067 5546498445928019756323601)
                  ·
                    refine ⟨4159873834446014817242701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5546498445928019756323601 4159873834446014817242701)
                    ·
                      refine ⟨1559952687917255556466013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159873834446014817242701 1559952687917255556466013)
                      ·
                        rfl

theorem cell23_3037997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3037997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3037997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3037997 prefixEnd_3037997 := by exact prefixLift 3037997
  have htrace : WordTrace (prefixWord ++ tailWord_3037997) baseStart_3037997 baseEnd_3037997 := by
    simpa [prefixWord, tailWord_3037997, baseEnd_3037997] using wordTrace_append hprefix tailTrace_3037997
  have hstable : (prefixWord ++ tailWord_3037997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037997).length < 2 ^ (prefixWord ++ tailWord_3037997).sum := by decide
  have hdescent : baseEnd_3037997 < baseStart_3037997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038003 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 1, 3, 2]
def baseStart_3038003 : Nat := 118140960795 + 3038003 * 2 ^ 59
def prefixEnd_3038003 : Nat := 4983230072969 + 3 ^ 40 * 3038003 * 2
def baseEnd_3038003 : Nat := 1559955768801182532990985

theorem tailTrace_3038003 : CollatzResearch.WordTrace tailWord_3038003 prefixEnd_3038003 1559955768801182532990985 := by
  unfold tailWord_3038003
  simp only [CollatzResearch.WordTrace]
  refine ⟨110805072412841455449782663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73870048275227636966521775 110805072412841455449782663)
  ·
    refine ⟨166207608619262183174673995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110805072412841455449782663 166207608619262183174673995)
    ·
      refine ⟨249311412928893274762010993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166207608619262183174673995 249311412928893274762010993)
      ·
        refine ⟨186983559696669956071508245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249311412928893274762010993 186983559696669956071508245)
        ·
          refine ⟨8764854360781404190851949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186983559696669956071508245 8764854360781404190851949)
          ·
            refine ⟨3286820385293026571569481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8764854360781404190851949 3286820385293026571569481)
            ·
              refine ⟨2465115288969769928677111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286820385293026571569481 2465115288969769928677111)
              ·
                refine ⟨3697672933454654893015667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465115288969769928677111 3697672933454654893015667)
                ·
                  refine ⟨5546509400181982339523501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697672933454654893015667 5546509400181982339523501)
                  ·
                    refine ⟨2079941025068243377321313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5546509400181982339523501 2079941025068243377321313)
                    ·
                      refine ⟨1559955768801182532990985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079941025068243377321313 1559955768801182532990985)
                      ·
                        rfl

theorem cell23_3038003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 3, 2].length) (baseStart_3038003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038003 prefixEnd_3038003 := by exact prefixLift 3038003
  have htrace : WordTrace (prefixWord ++ tailWord_3038003) baseStart_3038003 baseEnd_3038003 := by
    simpa [prefixWord, tailWord_3038003, baseEnd_3038003] using wordTrace_append hprefix tailTrace_3038003
  have hstable : (prefixWord ++ tailWord_3038003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038003).length < 2 ^ (prefixWord ++ tailWord_3038003).sum := by decide
  have hdescent : baseEnd_3038003 < baseStart_3038003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038032 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_3038032 : Nat := 118140960795 + 3038032 * 2 ^ 59
def prefixEnd_3038032 : Nat := 4983230072969 + 3 ^ 40 * 3038032 * 2
def baseEnd_3038032 : Nat := 1559970659740162919528351

theorem tailTrace_3038032 : CollatzResearch.WordTrace tailWord_3038032 prefixEnd_3038032 1559970659740162919528351 := by
  unfold tailWord_3038032
  simp only [CollatzResearch.WordTrace]
  refine ⟨55403065064868196701294175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73870753419824262268392233 55403065064868196701294175)
  ·
    refine ⟨83104597597302295051941263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55403065064868196701294175 83104597597302295051941263)
    ·
      refine ⟨124656896395953442577911895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83104597597302295051941263 124656896395953442577911895)
      ·
        refine ⟨186985344593930163866867843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124656896395953442577911895 186985344593930163866867843)
        ·
          refine ⟨280478016890895245800301765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186985344593930163866867843 280478016890895245800301765)
          ·
            refine ⟨52589628167042858587556581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280478016890895245800301765 52589628167042858587556581)
            ·
              refine ⟨9860555281320535985166859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52589628167042858587556581 9860555281320535985166859)
              ·
                refine ⟨14790832921980803977750289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860555281320535985166859 14790832921980803977750289)
                ·
                  refine ⟨11093124691485602983312717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14790832921980803977750289 11093124691485602983312717)
                  ·
                    refine ⟨4159921759307101118742269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11093124691485602983312717 4159921759307101118742269)
                    ·
                      refine ⟨1559970659740162919528351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4159921759307101118742269 1559970659740162919528351)
                      ·
                        rfl

theorem cell23_3038032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_3038032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038032 prefixEnd_3038032 := by exact prefixLift 3038032
  have htrace : WordTrace (prefixWord ++ tailWord_3038032) baseStart_3038032 baseEnd_3038032 := by
    simpa [prefixWord, tailWord_3038032, baseEnd_3038032] using wordTrace_append hprefix tailTrace_3038032
  have hstable : (prefixWord ++ tailWord_3038032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038032).length < 2 ^ (prefixWord ++ tailWord_3038032).sum := by decide
  have hdescent : baseEnd_3038032 < baseStart_3038032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038033 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_3038033 : Nat := 118140960795 + 3038033 * 2 ^ 59
def prefixEnd_3038033 : Nat := 4983230072969 + 3 ^ 40 * 3038033 * 2
def baseEnd_3038033 : Nat := 1559971173220817415615847

theorem tailTrace_3038033 : CollatzResearch.WordTrace tailWord_3038033 prefixEnd_3038033 1559971173220817415615847 := by
  unfold tailWord_3038033
  simp only [CollatzResearch.WordTrace]
  refine ⟨110806166602732770573374753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73870777735155180382249835 110806166602732770573374753)
  ·
    refine ⟨83104624952049577930031065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110806166602732770573374753 83104624952049577930031065)
    ·
      refine ⟨62328468714037183447523299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83104624952049577930031065 62328468714037183447523299)
      ·
        refine ⟨93492703071055775171284949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62328468714037183447523299 93492703071055775171284949)
        ·
          refine ⟨2191235228227869730576991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93492703071055775171284949 2191235228227869730576991)
          ·
            refine ⟨3286852842341804595865487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191235228227869730576991 3286852842341804595865487)
            ·
              refine ⟨4930279263512706893798231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286852842341804595865487 4930279263512706893798231)
              ·
                refine ⟨7395418895269060340697347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930279263512706893798231 7395418895269060340697347)
                ·
                  refine ⟨11093128342903590511046021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7395418895269060340697347 11093128342903590511046021)
                  ·
                    refine ⟨2079961564294423220821129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11093128342903590511046021 2079961564294423220821129)
                    ·
                      refine ⟨1559971173220817415615847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2079961564294423220821129 1559971173220817415615847)
                      ·
                        rfl

theorem cell23_3038033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_3038033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038033 prefixEnd_3038033 := by exact prefixLift 3038033
  have htrace : WordTrace (prefixWord ++ tailWord_3038033) baseStart_3038033 baseEnd_3038033 := by
    simpa [prefixWord, tailWord_3038033, baseEnd_3038033] using wordTrace_append hprefix tailTrace_3038033
  have hstable : (prefixWord ++ tailWord_3038033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038033).length < 2 ^ (prefixWord ++ tailWord_3038033).sum := by decide
  have hdescent : baseEnd_3038033 < baseStart_3038033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038052 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3038052 : Nat := 118140960795 + 3038052 * 2 ^ 59
def prefixEnd_3038052 : Nat := 4983230072969 + 3 ^ 40 * 3038052 * 2
def baseEnd_3038052 : Nat := 519993643117750947092753

theorem tailTrace_3038052 : CollatzResearch.WordTrace tailWord_3038052 prefixEnd_3038052 519993643117750947092753 := by
  unfold tailWord_3038052
  simp only [CollatzResearch.WordTrace]
  refine ⟨55403429794831968409158205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73871239726442624545544273 55403429794831968409158205)
  ·
    refine ⟨20776286173061988153434327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55403429794831968409158205 20776286173061988153434327)
    ·
      refine ⟨31164429259592982230151491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20776286173061988153434327 31164429259592982230151491)
      ·
        refine ⟨46746643889389473345227237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31164429259592982230151491 46746643889389473345227237)
        ·
          refine ⟨8764995729260526252230107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46746643889389473345227237 8764995729260526252230107)
          ·
            refine ⟨13147493593890789378345161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764995729260526252230107 13147493593890789378345161)
            ·
              refine ⟨9860620195418092033758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13147493593890789378345161 9860620195418092033758871)
              ·
                refine ⟨14790930293127138050638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860620195418092033758871 14790930293127138050638307)
                ·
                  refine ⟨22186395439690707075957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14790930293127138050638307 22186395439690707075957461)
                  ·
                    refine ⟨519993643117750947092753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22186395439690707075957461 519993643117750947092753)
                    ·
                      rfl

theorem cell23_3038052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3038052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038052 prefixEnd_3038052 := by exact prefixLift 3038052
  have htrace : WordTrace (prefixWord ++ tailWord_3038052) baseStart_3038052 baseEnd_3038052 := by
    simpa [prefixWord, tailWord_3038052, baseEnd_3038052] using wordTrace_append hprefix tailTrace_3038052
  have hstable : (prefixWord ++ tailWord_3038052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038052).length < 2 ^ (prefixWord ++ tailWord_3038052).sum := by decide
  have hdescent : baseEnd_3038052 < baseStart_3038052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038056 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 5]
def baseStart_3038056 : Nat := 118140960795 + 3038056 * 2 ^ 59
def prefixEnd_3038056 : Nat := 4983230072969 + 3 ^ 40 * 3038056 * 2
def baseEnd_3038056 : Nat := 173331442586207869514249

theorem tailTrace_3038056 : CollatzResearch.WordTrace tailWord_3038056 prefixEnd_3038056 173331442586207869514249 := by
  unfold tailWord_3038056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55403502740824722750731011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73871336987766297000974681 55403502740824722750731011)
  ·
    refine ⟨83105254111237084126096517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55403502740824722750731011 83105254111237084126096517)
    ·
      refine ⟨15582235145856953273643097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83105254111237084126096517 15582235145856953273643097)
      ·
        refine ⟨11686676359392714955232323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15582235145856953273643097 11686676359392714955232323)
        ·
          refine ⟨17530014539089072432848485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686676359392714955232323 17530014539089072432848485)
          ·
            refine ⟨3286877726079201081159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17530014539089072432848485 3286877726079201081159091)
            ·
              refine ⟨4930316589118801621738637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286877726079201081159091 4930316589118801621738637)
              ·
                refine ⟨1848868720919550608151989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4930316589118801621738637 1848868720919550608151989)
                ·
                  refine ⟨173331442586207869514249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1848868720919550608151989 173331442586207869514249)
                  ·
                    rfl

theorem cell23_3038056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 5].length) (baseStart_3038056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038056 prefixEnd_3038056 := by exact prefixLift 3038056
  have htrace : WordTrace (prefixWord ++ tailWord_3038056) baseStart_3038056 baseEnd_3038056 := by
    simpa [prefixWord, tailWord_3038056, baseEnd_3038056] using wordTrace_append hprefix tailTrace_3038056
  have hstable : (prefixWord ++ tailWord_3038056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038056).length < 2 ^ (prefixWord ++ tailWord_3038056).sum := by decide
  have hdescent : baseEnd_3038056 < baseStart_3038056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038069 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_3038069 : Nat := 118140960795 + 3038069 * 2 ^ 59
def prefixEnd_3038069 : Nat := 4983230072969 + 3 ^ 40 * 3038069 * 2
def baseEnd_3038069 : Nat := 519996552841459758255227

theorem tailTrace_3038069 : CollatzResearch.WordTrace tailWord_3038069 prefixEnd_3038069 519996552841459758255227 := by
  unfold tailWord_3038069
  simp only [CollatzResearch.WordTrace]
  refine ⟨110807479630602348721685261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73871653087068232481123507 110807479630602348721685261)
  ·
    refine ⟨41552804861475880770631973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110807479630602348721685261 41552804861475880770631973)
    ·
      refine ⟨7791150911526727644493495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41552804861475880770631973 7791150911526727644493495)
      ·
        refine ⟨11686726367290091466740243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791150911526727644493495 11686726367290091466740243)
        ·
          refine ⟨17530089550935137200110365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11686726367290091466740243 17530089550935137200110365)
          ·
            refine ⟨6573783581600676450041387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17530089550935137200110365 6573783581600676450041387)
            ·
              refine ⟨9860675372401014675062081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6573783581600676450041387 9860675372401014675062081)
              ·
                refine ⟨7395506529300761006296561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860675372401014675062081 7395506529300761006296561)
                ·
                  refine ⟨5546629896975570754722421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395506529300761006296561 5546629896975570754722421)
                  ·
                    refine ⟨519996552841459758255227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5546629896975570754722421 519996552841459758255227)
                    ·
                      rfl

theorem cell23_3038069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_3038069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038069 prefixEnd_3038069 := by exact prefixLift 3038069
  have htrace : WordTrace (prefixWord ++ tailWord_3038069) baseStart_3038069 baseEnd_3038069 := by
    simpa [prefixWord, tailWord_3038069, baseEnd_3038069] using wordTrace_append hprefix tailTrace_3038069
  have hstable : (prefixWord ++ tailWord_3038069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038069).length < 2 ^ (prefixWord ++ tailWord_3038069).sum := by decide
  have hdescent : baseEnd_3038069 < baseStart_3038069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038092 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3038092 : Nat := 118140960795 + 3038092 * 2 ^ 59
def prefixEnd_3038092 : Nat := 4983230072969 + 3 ^ 40 * 3038092 * 2
def baseEnd_3038092 : Nat := 1560001468579432684778075

theorem tailTrace_3038092 : CollatzResearch.WordTrace tailWord_3038092 prefixEnd_3038092 1560001468579432684778075 := by
  unfold tailWord_3038092
  simp only [CollatzResearch.WordTrace]
  refine ⟨55404159254759511824886265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73872212339679349099848353 55404159254759511824886265)
  ·
    refine ⟨41553119441069633868664699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55404159254759511824886265 41553119441069633868664699)
    ·
      refine ⟨62329679161604450802997049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41553119441069633868664699 62329679161604450802997049)
      ·
        refine ⟨46747259371203338102247787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62329679161604450802997049 46747259371203338102247787)
        ·
          refine ⟨70120889056805007153371681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46747259371203338102247787 70120889056805007153371681)
          ·
            refine ⟨52590666792603755365028761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70120889056805007153371681 52590666792603755365028761)
            ·
              refine ⟨39443000094452816523771571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52590666792603755365028761 39443000094452816523771571)
              ·
                refine ⟨59164500141679224785657357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39443000094452816523771571 59164500141679224785657357)
                ·
                  refine ⟨22186687553129709294621509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59164500141679224785657357 22186687553129709294621509)
                  ·
                    refine ⟨4160003916211820492741533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22186687553129709294621509 4160003916211820492741533)
                    ·
                      refine ⟨1560001468579432684778075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4160003916211820492741533 1560001468579432684778075)
                      ·
                        rfl

theorem cell23_3038092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3038092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038092 prefixEnd_3038092 := by exact prefixLift 3038092
  have htrace : WordTrace (prefixWord ++ tailWord_3038092) baseStart_3038092 baseEnd_3038092 := by
    simpa [prefixWord, tailWord_3038092, baseEnd_3038092] using wordTrace_append hprefix tailTrace_3038092
  have hstable : (prefixWord ++ tailWord_3038092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038092).length < 2 ^ (prefixWord ++ tailWord_3038092).sum := by decide
  have hdescent : baseEnd_3038092 < baseStart_3038092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038106 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3038106 : Nat := 118140960795 + 3038106 * 2 ^ 59
def prefixEnd_3038106 : Nat := 4983230072969 + 3 ^ 40 * 3038106 * 2
def baseEnd_3038106 : Nat := 1560008657308595630003011

theorem tailTrace_3038106 : CollatzResearch.WordTrace tailWord_3038106 prefixEnd_3038106 1560008657308595630003011 := by
  unfold tailWord_3038106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702207282867076010195543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73872552754312202693854781 27702207282867076010195543)
  ·
    refine ⟨41553310924300614015293315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27702207282867076010195543 41553310924300614015293315)
    ·
      refine ⟨62329966386450921022939973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41553310924300614015293315 62329966386450921022939973)
      ·
        refine ⟨11686868697459547691801245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62329966386450921022939973 11686868697459547691801245)
        ·
          refine ⟨4382575761547330384425467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11686868697459547691801245 4382575761547330384425467)
          ·
            refine ⟨6573863642320995576638201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382575761547330384425467 6573863642320995576638201)
            ·
              refine ⟨4930397731740746682478651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573863642320995576638201 4930397731740746682478651)
              ·
                refine ⟨7395596597611120023717977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930397731740746682478651 7395596597611120023717977)
                ·
                  refine ⟨5546697448208340017788483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395596597611120023717977 5546697448208340017788483)
                  ·
                    refine ⟨8320046172312510026682725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546697448208340017788483 8320046172312510026682725)
                    ·
                      refine ⟨1560008657308595630003011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8320046172312510026682725 1560008657308595630003011)
                      ·
                        rfl

theorem cell23_3038106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3038106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038106 prefixEnd_3038106 := by exact prefixLift 3038106
  have htrace : WordTrace (prefixWord ++ tailWord_3038106) baseStart_3038106 baseEnd_3038106 := by
    simpa [prefixWord, tailWord_3038106, baseEnd_3038106] using wordTrace_append hprefix tailTrace_3038106
  have hstable : (prefixWord ++ tailWord_3038106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038106).length < 2 ^ (prefixWord ++ tailWord_3038106).sum := by decide
  have hdescent : baseEnd_3038106 < baseStart_3038106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038116 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_3038116 : Nat := 118140960795 + 3038116 * 2 ^ 59
def prefixEnd_3038116 : Nat := 4983230072969 + 3 ^ 40 * 3038116 * 2
def baseEnd_3038116 : Nat := 520004597371713530292655

theorem tailTrace_3038116 : CollatzResearch.WordTrace tailWord_3038116 prefixEnd_3038116 520004597371713530292655 := by
  unfold tailWord_3038116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55404596930716037874323101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73872795907621383832430801 55404596930716037874323101)
  ·
    refine ⟨20776723849018514202871163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55404596930716037874323101 20776723849018514202871163)
    ·
      refine ⟨31165085773527771304306745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20776723849018514202871163 31165085773527771304306745)
      ·
        refine ⟨23373814330145828478230059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31165085773527771304306745 23373814330145828478230059)
        ·
          refine ⟨35060721495218742717345089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23373814330145828478230059 35060721495218742717345089)
          ·
            refine ⟨26295541121414057038008817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35060721495218742717345089 26295541121414057038008817)
            ·
              refine ⟨19721655841060542778506613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26295541121414057038008817 19721655841060542778506613)
              ·
                refine ⟨1848905235099425885484995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19721655841060542778506613 1848905235099425885484995)
                ·
                  refine ⟨2773357852649138828227493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848905235099425885484995 2773357852649138828227493)
                  ·
                    refine ⟨520004597371713530292655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773357852649138828227493 520004597371713530292655)
                    ·
                      rfl

theorem cell23_3038116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_3038116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038116 prefixEnd_3038116 := by exact prefixLift 3038116
  have htrace : WordTrace (prefixWord ++ tailWord_3038116) baseStart_3038116 baseEnd_3038116 := by
    simpa [prefixWord, tailWord_3038116, baseEnd_3038116] using wordTrace_append hprefix tailTrace_3038116
  have hstable : (prefixWord ++ tailWord_3038116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038116).length < 2 ^ (prefixWord ++ tailWord_3038116).sum := by decide
  have hdescent : baseEnd_3038116 < baseStart_3038116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038156 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3038156 : Nat := 118140960795 + 3038156 * 2 ^ 59
def prefixEnd_3038156 : Nat := 4983230072969 + 3 ^ 40 * 3038156 * 2
def baseEnd_3038156 : Nat := 1560034331341320434377781

theorem tailTrace_3038156 : CollatzResearch.WordTrace tailWord_3038156 prefixEnd_3038156 1560034331341320434377781 := by
  unfold tailWord_3038156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405326390643581290051161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73873768520858108386734881 55405326390643581290051161)
  ·
    refine ⟨41553994792982685967538371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55405326390643581290051161 41553994792982685967538371)
    ·
      refine ⟨62330992189474028951307557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41553994792982685967538371 62330992189474028951307557)
      ·
        refine ⟨11687061035526380428370167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62330992189474028951307557 11687061035526380428370167)
        ·
          refine ⟨17530591553289570642555251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11687061035526380428370167 17530591553289570642555251)
          ·
            refine ⟨26295887329934355963832877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17530591553289570642555251 26295887329934355963832877)
            ·
              refine ⟨9860957748725383486437329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26295887329934355963832877 9860957748725383486437329)
              ·
                refine ⟨7395718311544037614827997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9860957748725383486437329 7395718311544037614827997)
                ·
                  refine ⟨2773394366829014105560499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7395718311544037614827997 2773394366829014105560499)
                  ·
                    refine ⟨4160091550243521158340749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2773394366829014105560499 4160091550243521158340749)
                    ·
                      refine ⟨1560034331341320434377781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4160091550243521158340749 1560034331341320434377781)
                      ·
                        rfl

theorem cell23_3038156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3038156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038156 prefixEnd_3038156 := by exact prefixLift 3038156
  have htrace : WordTrace (prefixWord ++ tailWord_3038156) baseStart_3038156 baseEnd_3038156 := by
    simpa [prefixWord, tailWord_3038156, baseEnd_3038156] using wordTrace_append hprefix tailTrace_3038156
  have hstable : (prefixWord ++ tailWord_3038156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038156).length < 2 ^ (prefixWord ++ tailWord_3038156).sum := by decide
  have hdescent : baseEnd_3038156 < baseStart_3038156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038157 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3038157 : Nat := 118140960795 + 3038157 * 2 ^ 59
def prefixEnd_3038157 : Nat := 4983230072969 + 3 ^ 40 * 3038157 * 2
def baseEnd_3038157 : Nat := 1560034844821974930465277

theorem tailTrace_3038157 : CollatzResearch.WordTrace tailWord_3038157 prefixEnd_3038157 1560034844821974930465277 := by
  unfold tailWord_3038157
  simp only [CollatzResearch.WordTrace]
  refine ⟨110810689254283539750888725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73873792836189026500592483 110810689254283539750888725)
  ·
    refine ⟨5194251058794540925822909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110810689254283539750888725 5194251058794540925822909)
    ·
      refine ⟨1947844147047952847183591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5194251058794540925822909 1947844147047952847183591)
      ·
        refine ⟨2921766220571929270775387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947844147047952847183591 2921766220571929270775387)
        ·
          refine ⟨4382649330857893906163081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921766220571929270775387 4382649330857893906163081)
          ·
            refine ⟨3286986998143420429622311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4382649330857893906163081 3286986998143420429622311)
            ·
              refine ⟨4930480497215130644433467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286986998143420429622311 4930480497215130644433467)
              ·
                refine ⟨7395720745822695966650201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930480497215130644433467 7395720745822695966650201)
                ·
                  refine ⟨5546790559367021974987651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395720745822695966650201 5546790559367021974987651)
                  ·
                    refine ⟨8320185839050532962481477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546790559367021974987651 8320185839050532962481477)
                    ·
                      refine ⟨1560034844821974930465277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8320185839050532962481477 1560034844821974930465277)
                      ·
                        rfl

theorem cell23_3038157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3038157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038157 prefixEnd_3038157 := by exact prefixLift 3038157
  have htrace : WordTrace (prefixWord ++ tailWord_3038157) baseStart_3038157 baseEnd_3038157 := by
    simpa [prefixWord, tailWord_3038157, baseEnd_3038157] using wordTrace_append hprefix tailTrace_3038157
  have hstable : (prefixWord ++ tailWord_3038157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038157).length < 2 ^ (prefixWord ++ tailWord_3038157).sum := by decide
  have hdescent : baseEnd_3038157 < baseStart_3038157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038192 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3038192 : Nat := 118140960795 + 3038192 * 2 ^ 59
def prefixEnd_3038192 : Nat := 4983230072969 + 3 ^ 40 * 3038192 * 2
def baseEnd_3038192 : Nat := 1560052816644882293527615

theorem tailTrace_3038192 : CollatzResearch.WordTrace tailWord_3038192 prefixEnd_3038192 1560052816644882293527615 := by
  unfold tailWord_3038192
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405982904578370364206415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73874643872771160485608553 55405982904578370364206415)
  ·
    refine ⟨83108974356867555546309623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55405982904578370364206415 83108974356867555546309623)
    ·
      refine ⟨124663461535301333319464435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83108974356867555546309623 124663461535301333319464435)
      ·
        refine ⟨186995192302951999979196653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124663461535301333319464435 186995192302951999979196653)
        ·
          refine ⟨70123197113606999992198745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186995192302951999979196653 70123197113606999992198745)
          ·
            refine ⟨52592397835205249994149059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70123197113606999992198745 52592397835205249994149059)
            ·
              refine ⟨78888596752807874991223589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52592397835205249994149059 78888596752807874991223589)
              ·
                refine ⟨14791611891151476560854423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78888596752807874991223589 14791611891151476560854423)
                ·
                  refine ⟨22187417836727214841281635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14791611891151476560854423 22187417836727214841281635)
                  ·
                    refine ⟨33281126755090822261922453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22187417836727214841281635 33281126755090822261922453)
                    ·
                      refine ⟨1560052816644882293527615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33281126755090822261922453 1560052816644882293527615)
                      ·
                        rfl

theorem cell23_3038192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3038192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038192 prefixEnd_3038192 := by exact prefixLift 3038192
  have htrace : WordTrace (prefixWord ++ tailWord_3038192) baseStart_3038192 baseEnd_3038192 := by
    simpa [prefixWord, tailWord_3038192, baseEnd_3038192] using wordTrace_append hprefix tailTrace_3038192
  have hstable : (prefixWord ++ tailWord_3038192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038192).length < 2 ^ (prefixWord ++ tailWord_3038192).sum := by decide
  have hdescent : baseEnd_3038192 < baseStart_3038192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038209 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3038209 : Nat := 118140960795 + 3038209 * 2 ^ 59
def prefixEnd_3038209 : Nat := 4983230072969 + 3 ^ 40 * 3038209 * 2
def baseEnd_3038209 : Nat := 1560061545816008727015037

theorem tailTrace_3038209 : CollatzResearch.WordTrace tailWord_3038209 prefixEnd_3038209 1560061545816008727015037 := by
  unfold tailWord_3038209
  simp only [CollatzResearch.WordTrace]
  refine ⟨110812585850095152631781681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73875057233396768421187787 110812585850095152631781681)
  ·
    refine ⟨83109439387571364473836261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110812585850095152631781681 83109439387571364473836261)
    ·
      refine ⟨15583019885169630838844299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83109439387571364473836261 15583019885169630838844299)
      ·
        refine ⟨23374529827754446258266449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15583019885169630838844299 23374529827754446258266449)
        ·
          refine ⟨17530897370815834693699837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23374529827754446258266449 17530897370815834693699837)
          ·
            refine ⟨6574086514055938010137439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17530897370815834693699837 6574086514055938010137439)
            ·
              refine ⟨9861129771083907015206159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574086514055938010137439 9861129771083907015206159)
              ·
                refine ⟨14791694656625860522809239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861129771083907015206159 14791694656625860522809239)
                ·
                  refine ⟨22187541984938790784213859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14791694656625860522809239 22187541984938790784213859)
                  ·
                    refine ⟨33281312977408186176320789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22187541984938790784213859 33281312977408186176320789)
                    ·
                      refine ⟨1560061545816008727015037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33281312977408186176320789 1560061545816008727015037)
                      ·
                        rfl

theorem cell23_3038209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3038209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038209 prefixEnd_3038209 := by exact prefixLift 3038209
  have htrace : WordTrace (prefixWord ++ tailWord_3038209) baseStart_3038209 baseEnd_3038209 := by
    simpa [prefixWord, tailWord_3038209, baseEnd_3038209] using wordTrace_append hprefix tailTrace_3038209
  have hstable : (prefixWord ++ tailWord_3038209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038209).length < 2 ^ (prefixWord ++ tailWord_3038209).sum := by decide
  have hdescent : baseEnd_3038209 < baseStart_3038209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038210 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3038210 : Nat := 118140960795 + 3038210 * 2 ^ 59
def prefixEnd_3038210 : Nat := 4983230072969 + 3 ^ 40 * 3038210 * 2
def baseEnd_3038210 : Nat := 520020686432221074367511

theorem tailTrace_3038210 : CollatzResearch.WordTrace tailWord_3038210 prefixEnd_3038210 520020686432221074367511 := by
  unfold tailWord_3038210
  simp only [CollatzResearch.WordTrace]
  refine ⟨27703155580772882450642021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73875081548727686535045389 27703155580772882450642021)
  ·
    refine ⟨5194341671394915459495379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27703155580772882450642021 5194341671394915459495379)
    ·
      refine ⟨7791512507092373189243069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194341671394915459495379 7791512507092373189243069)
      ·
        refine ⟨2921817190159639945966151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7791512507092373189243069 2921817190159639945966151)
        ·
          refine ⟨4382725785239459918949227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921817190159639945966151 4382725785239459918949227)
          ·
            refine ⟨6574088677859189878423841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382725785239459918949227 6574088677859189878423841)
            ·
              refine ⟨4930566508394392408817881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574088677859189878423841 4930566508394392408817881)
              ·
                refine ⟨3697924881295794306613411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4930566508394392408817881 3697924881295794306613411)
                ·
                  refine ⟨5546887321943691459920117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697924881295794306613411 5546887321943691459920117)
                  ·
                    refine ⟨520020686432221074367511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5546887321943691459920117 520020686432221074367511)
                    ·
                      rfl

theorem cell23_3038210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3038210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038210 prefixEnd_3038210 := by exact prefixLift 3038210
  have htrace : WordTrace (prefixWord ++ tailWord_3038210) baseStart_3038210 baseEnd_3038210 := by
    simpa [prefixWord, tailWord_3038210, baseEnd_3038210] using wordTrace_append hprefix tailTrace_3038210
  have hstable : (prefixWord ++ tailWord_3038210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038210).length < 2 ^ (prefixWord ++ tailWord_3038210).sum := by decide
  have hdescent : baseEnd_3038210 < baseStart_3038210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038216 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3038216 : Nat := 118140960795 + 3038216 * 2 ^ 59
def prefixEnd_3038216 : Nat := 4983230072969 + 3 ^ 40 * 3038216 * 2
def baseEnd_3038216 : Nat := 1560065140180590199627505

theorem tailTrace_3038216 : CollatzResearch.WordTrace tailWord_3038216 prefixEnd_3038216 1560065140180590199627505 := by
  unfold tailWord_3038216
  simp only [CollatzResearch.WordTrace]
  refine ⟨55406420580534896413643251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73875227440713195218191001 55406420580534896413643251)
  ·
    refine ⟨83109630870802344620464877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55406420580534896413643251 83109630870802344620464877)
    ·
      refine ⟨31166111576550879232674329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83109630870802344620464877 31166111576550879232674329)
      ·
        refine ⟨23374583682413159424505747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31166111576550879232674329 23374583682413159424505747)
        ·
          refine ⟨35061875523619739136758621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23374583682413159424505747 35061875523619739136758621)
          ·
            refine ⟨13148203321357402176284483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35061875523619739136758621 13148203321357402176284483)
            ·
              refine ⟨19722304982036103264426725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13148203321357402176284483 19722304982036103264426725)
              ·
                refine ⟨3697932184131769362080011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19722304982036103264426725 3697932184131769362080011)
                ·
                  refine ⟨5546898276197654043120017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697932184131769362080011 5546898276197654043120017)
                  ·
                    refine ⟨4160173707148240532340013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5546898276197654043120017 4160173707148240532340013)
                    ·
                      refine ⟨1560065140180590199627505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4160173707148240532340013 1560065140180590199627505)
                      ·
                        rfl

theorem cell23_3038216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3038216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038216 prefixEnd_3038216 := by exact prefixLift 3038216
  have htrace : WordTrace (prefixWord ++ tailWord_3038216) baseStart_3038216 baseEnd_3038216 := by
    simpa [prefixWord, tailWord_3038216, baseEnd_3038216] using wordTrace_append hprefix tailTrace_3038216
  have hstable : (prefixWord ++ tailWord_3038216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038216).length < 2 ^ (prefixWord ++ tailWord_3038216).sum := by decide
  have hdescent : baseEnd_3038216 < baseStart_3038216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038219 : List Nat := [1, 1, 1, 1, 6, 2, 4, 7]
def baseStart_3038219 : Nat := 118140960795 + 3038219 * 2 ^ 59
def prefixEnd_3038219 : Nat := 4983230072969 + 3 ^ 40 * 3038219 * 2
def baseEnd_3038219 : Nat := 57780247430464951403333

theorem tailTrace_3038219 : CollatzResearch.WordTrace tailWord_3038219 prefixEnd_3038219 57780247430464951403333 := by
  unfold tailWord_3038219
  simp only [CollatzResearch.WordTrace]
  refine ⟨110812950580058924339645711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73875300386705949559763807 110812950580058924339645711)
  ·
    refine ⟨166219425870088386509468567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110812950580058924339645711 166219425870088386509468567)
    ·
      refine ⟨249329138805132579764202851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166219425870088386509468567 249329138805132579764202851)
      ·
        refine ⟨373993708207698869646304277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249329138805132579764202851 373993708207698869646304277)
        ·
          refine ⟨17530955072235884514670513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 373993708207698869646304277 17530955072235884514670513)
          ·
            refine ⟨13148216304176913386002885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17530955072235884514670513 13148216304176913386002885)
            ·
              refine ⟨2465290557033171259875541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13148216304176913386002885 2465290557033171259875541)
              ·
                refine ⟨57780247430464951403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2465290557033171259875541 57780247430464951403333)
                ·
                  rfl

theorem cell23_3038219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 7].length) (baseStart_3038219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038219 prefixEnd_3038219 := by exact prefixLift 3038219
  have htrace : WordTrace (prefixWord ++ tailWord_3038219) baseStart_3038219 baseEnd_3038219 := by
    simpa [prefixWord, tailWord_3038219, baseEnd_3038219] using wordTrace_append hprefix tailTrace_3038219
  have hstable : (prefixWord ++ tailWord_3038219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038219).length < 2 ^ (prefixWord ++ tailWord_3038219).sum := by decide
  have hdescent : baseEnd_3038219 < baseStart_3038219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038236 : List Nat := [2, 2, 3, 1, 5, 1, 9]
def baseStart_3038236 : Nat := 118140960795 + 3038236 * 2 ^ 59
def prefixEnd_3038236 : Nat := 4983230072969 + 3 ^ 40 * 3038236 * 2
def baseEnd_3038236 : Nat := 19260190244366421251573

theorem tailTrace_3038236 : CollatzResearch.WordTrace tailWord_3038236 prefixEnd_3038236 19260190244366421251573 := by
  unfold tailWord_3038236
  simp only [CollatzResearch.WordTrace]
  refine ⟨55406785310498668121507281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73875713747331557495343041 55406785310498668121507281)
  ·
    refine ⟨41555088982874001091130461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55406785310498668121507281 41555088982874001091130461)
    ·
      refine ⟨15583158368577750409173923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41555088982874001091130461 15583158368577750409173923)
      ·
        refine ⟨23374737552866625613760885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15583158368577750409173923 23374737552866625613760885)
        ·
          refine ⟨2191381645581246151290083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23374737552866625613760885 2191381645581246151290083)
          ·
            refine ⟨3287072468371869226935125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191381645581246151290083 3287072468371869226935125)
            ·
              refine ⟨19260190244366421251573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3287072468371869226935125 19260190244366421251573)
              ·
                rfl

theorem cell23_3038236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 9].length) (baseStart_3038236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038236 prefixEnd_3038236 := by exact prefixLift 3038236
  have htrace : WordTrace (prefixWord ++ tailWord_3038236) baseStart_3038236 baseEnd_3038236 := by
    simpa [prefixWord, tailWord_3038236, baseEnd_3038236] using wordTrace_append hprefix tailTrace_3038236
  have hstable : (prefixWord ++ tailWord_3038236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038236).length < 2 ^ (prefixWord ++ tailWord_3038236).sum := by decide
  have hdescent : baseEnd_3038236 < baseStart_3038236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038247 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3038247 : Nat := 118140960795 + 3038247 * 2 ^ 59
def prefixEnd_3038247 : Nat := 4983230072969 + 3 ^ 40 * 3038247 * 2
def baseEnd_3038247 : Nat := 1560081058080879578339863

theorem tailTrace_3038247 : CollatzResearch.WordTrace tailWord_3038247 prefixEnd_3038247 1560081058080879578339863 := by
  unfold tailWord_3038247
  simp only [CollatzResearch.WordTrace]
  refine ⟨110813971823957485121664995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73875981215971656747776663 110813971823957485121664995)
  ·
    refine ⟨166220957735936227682497493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110813971823957485121664995 166220957735936227682497493)
    ·
      refine ⟨3895803696936005336308535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166220957735936227682497493 3895803696936005336308535)
      ·
        refine ⟨5843705545404008004462803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895803696936005336308535 5843705545404008004462803)
        ·
          refine ⟨8765558318106012006694205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843705545404008004462803 8765558318106012006694205)
          ·
            refine ⟨3287084369289754502510327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8765558318106012006694205 3287084369289754502510327)
            ·
              refine ⟨4930626553934631753765491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287084369289754502510327 4930626553934631753765491)
              ·
                refine ⟨7395939830901947630648237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930626553934631753765491 7395939830901947630648237)
                ·
                  refine ⟨2773477436588230361493089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7395939830901947630648237 2773477436588230361493089)
                  ·
                    refine ⟨2080108077441172771119817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2773477436588230361493089 2080108077441172771119817)
                    ·
                      refine ⟨1560081058080879578339863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080108077441172771119817 1560081058080879578339863)
                      ·
                        rfl

theorem cell23_3038247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3038247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038247 prefixEnd_3038247 := by exact prefixLift 3038247
  have htrace : WordTrace (prefixWord ++ tailWord_3038247) baseStart_3038247 baseEnd_3038247 := by
    simpa [prefixWord, tailWord_3038247, baseEnd_3038247] using wordTrace_append hprefix tailTrace_3038247
  have hstable : (prefixWord ++ tailWord_3038247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038247).length < 2 ^ (prefixWord ++ tailWord_3038247).sum := by decide
  have hdescent : baseEnd_3038247 < baseStart_3038247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038256 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2]
def baseStart_3038256 : Nat := 118140960795 + 3038256 * 2 ^ 59
def prefixEnd_3038256 : Nat := 4983230072969 + 3 ^ 40 * 3038256 * 2
def baseEnd_3038256 : Nat := 1560085679406770043127321

theorem tailTrace_3038256 : CollatzResearch.WordTrace tailWord_3038256 prefixEnd_3038256 1560085679406770043127321 := by
  unfold tailWord_3038256
  simp only [CollatzResearch.WordTrace]
  refine ⟨55407150040462439829371311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73876200053949919772495081 55407150040462439829371311)
  ·
    refine ⟨83110725060693659744056967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55407150040462439829371311 83110725060693659744056967)
    ·
      refine ⟨124666087591040489616085451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83110725060693659744056967 124666087591040489616085451)
      ·
        refine ⟨186999131386560734424128177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124666087591040489616085451 186999131386560734424128177)
        ·
          refine ⟨140249348539920550818096133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186999131386560734424128177 140249348539920550818096133)
          ·
            refine ⟨26296752851235103278393025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140249348539920550818096133 26296752851235103278393025)
            ·
              refine ⟨19722564638426327458794769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26296752851235103278393025 19722564638426327458794769)
              ·
                refine ⟨14791923478819745594096077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19722564638426327458794769 14791923478819745594096077)
                ·
                  refine ⟨5546971304557404597786029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14791923478819745594096077 5546971304557404597786029)
                  ·
                    refine ⟨2080114239209026724169761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5546971304557404597786029 2080114239209026724169761)
                    ·
                      refine ⟨1560085679406770043127321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080114239209026724169761 1560085679406770043127321)
                      ·
                        rfl

theorem cell23_3038256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2].length) (baseStart_3038256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038256 prefixEnd_3038256 := by exact prefixLift 3038256
  have htrace : WordTrace (prefixWord ++ tailWord_3038256) baseStart_3038256 baseEnd_3038256 := by
    simpa [prefixWord, tailWord_3038256, baseEnd_3038256] using wordTrace_append hprefix tailTrace_3038256
  have hstable : (prefixWord ++ tailWord_3038256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038256).length < 2 ^ (prefixWord ++ tailWord_3038256).sum := by decide
  have hdescent : baseEnd_3038256 < baseStart_3038256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038289 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_3038289 : Nat := 118140960795 + 3038289 * 2 ^ 59
def prefixEnd_3038289 : Nat := 4983230072969 + 3 ^ 40 * 3038289 * 2
def baseEnd_3038289 : Nat := 1560102624268368414014669

theorem tailTrace_3038289 : CollatzResearch.WordTrace tailWord_3038289 prefixEnd_3038289 1560102624268368414014669 := by
  unfold tailWord_3038289
  simp only [CollatzResearch.WordTrace]
  refine ⟨110815503689805326294693921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73877002459870217529795947 110815503689805326294693921)
  ·
    refine ⟨83111627767353994721020441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110815503689805326294693921 83111627767353994721020441)
    ·
      refine ⟨62333720825515496040765331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83111627767353994721020441 62333720825515496040765331)
      ·
        refine ⟨93500581238273244061147997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62333720825515496040765331 93500581238273244061147997)
        ·
          refine ⟨35062717964352466522930499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93500581238273244061147997 35062717964352466522930499)
          ·
            refine ⟨52594076946528699784395749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35062717964352466522930499 52594076946528699784395749)
            ·
              refine ⟨9861389427474131209574203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52594076946528699784395749 9861389427474131209574203)
              ·
                refine ⟨14792084141211196814361305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861389427474131209574203 14792084141211196814361305)
                ·
                  refine ⟨11094063105908397610770979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14792084141211196814361305 11094063105908397610770979)
                  ·
                    refine ⟨16641094658862596416156469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11094063105908397610770979 16641094658862596416156469)
                    ·
                      refine ⟨1560102624268368414014669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16641094658862596416156469 1560102624268368414014669)
                      ·
                        rfl

theorem cell23_3038289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_3038289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038289 prefixEnd_3038289 := by exact prefixLift 3038289
  have htrace : WordTrace (prefixWord ++ tailWord_3038289) baseStart_3038289 baseEnd_3038289 := by
    simpa [prefixWord, tailWord_3038289, baseEnd_3038289] using wordTrace_append hprefix tailTrace_3038289
  have hstable : (prefixWord ++ tailWord_3038289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038289).length < 2 ^ (prefixWord ++ tailWord_3038289).sum := by decide
  have hdescent : baseEnd_3038289 < baseStart_3038289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038309 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 7]
def baseStart_3038309 : Nat := 118140960795 + 3038309 * 2 ^ 59
def prefixEnd_3038309 : Nat := 4983230072969 + 3 ^ 40 * 3038309 * 2
def baseEnd_3038309 : Nat := 173345877097939815084953

theorem tailTrace_3038309 : CollatzResearch.WordTrace tailWord_3038309 prefixEnd_3038309 173345877097939815084953 := by
  unfold tailWord_3038309
  simp only [CollatzResearch.WordTrace]
  refine ⟨110816233149732869710421981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73877488766488579806947987 110816233149732869710421981)
  ·
    refine ⟨41556087431149826141408243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110816233149732869710421981 41556087431149826141408243)
    ·
      refine ⟨62334131146724739212112365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41556087431149826141408243 62334131146724739212112365)
      ·
        refine ⟨23375299180021777204542137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62334131146724739212112365 23375299180021777204542137)
        ·
          refine ⟨17531474385016332903406603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23375299180021777204542137 17531474385016332903406603)
          ·
            refine ⟨26297211577524499355109905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17531474385016332903406603 26297211577524499355109905)
            ·
              refine ⟨19722908683143374516332429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26297211577524499355109905 19722908683143374516332429)
              ·
                refine ⟨7396090756178765443624661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19722908683143374516332429 7396090756178765443624661)
                ·
                  refine ⟨173345877097939815084953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7396090756178765443624661 173345877097939815084953)
                  ·
                    rfl

theorem cell23_3038309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_3038309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038309 prefixEnd_3038309 := by exact prefixLift 3038309
  have htrace : WordTrace (prefixWord ++ tailWord_3038309) baseStart_3038309 baseEnd_3038309 := by
    simpa [prefixWord, tailWord_3038309, baseEnd_3038309] using wordTrace_append hprefix tailTrace_3038309
  have hstable : (prefixWord ++ tailWord_3038309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038309).length < 2 ^ (prefixWord ++ tailWord_3038309).sum := by decide
  have hdescent : baseEnd_3038309 < baseStart_3038309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038326 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_3038326 : Nat := 118140960795 + 3038326 * 2 ^ 59
def prefixEnd_3038326 : Nat := 4983230072969 + 3 ^ 40 * 3038326 * 2
def baseEnd_3038326 : Nat := 173346847005842752139111

theorem tailTrace_3038326 : CollatzResearch.WordTrace tailWord_3038326 prefixEnd_3038326 173346847005842752139111 := by
  unfold tailWord_3038326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926053324416955100861927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73877902127114187742527221 6926053324416955100861927)
  ·
    refine ⟨10389079986625432651292891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6926053324416955100861927 10389079986625432651292891)
    ·
      refine ⟨15583619979938148976939337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10389079986625432651292891 15583619979938148976939337)
      ·
        refine ⟨11687714984953611732704503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15583619979938148976939337 11687714984953611732704503)
        ·
          refine ⟨17531572477430417599056755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11687714984953611732704503 17531572477430417599056755)
          ·
            refine ⟨26297358716145626398585133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17531572477430417599056755 26297358716145626398585133)
            ·
              refine ⟨9861509518554609899469425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26297358716145626398585133 9861509518554609899469425)
              ·
                refine ⟨7396132138915957424602069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9861509518554609899469425 7396132138915957424602069)
                ·
                  refine ⟨173346847005842752139111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7396132138915957424602069 173346847005842752139111)
                  ·
                    rfl

theorem cell23_3038326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_3038326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038326 prefixEnd_3038326 := by exact prefixLift 3038326
  have htrace : WordTrace (prefixWord ++ tailWord_3038326) baseStart_3038326 baseEnd_3038326 := by
    simpa [prefixWord, tailWord_3038326, baseEnd_3038326] using wordTrace_append hprefix tailTrace_3038326
  have hstable : (prefixWord ++ tailWord_3038326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038326).length < 2 ^ (prefixWord ++ tailWord_3038326).sum := by decide
  have hdescent : baseEnd_3038326 < baseStart_3038326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038339 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 7]
def baseStart_3038339 : Nat := 118140960795 + 3038339 * 2 ^ 59
def prefixEnd_3038339 : Nat := 4983230072969 + 3 ^ 40 * 3038339 * 2
def baseEnd_3038339 : Nat := 520042766100364406129813

theorem tailTrace_3038339 : CollatzResearch.WordTrace tailWord_3038339 prefixEnd_3038339 520042766100364406129813 := by
  unfold tailWord_3038339
  simp only [CollatzResearch.WordTrace]
  refine ⟨110817327339624184834014071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73878218226416123222676047 110817327339624184834014071)
  ·
    refine ⟨166225991009436277251021107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110817327339624184834014071 166225991009436277251021107)
    ·
      refine ⟨249338986514154415876531661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166225991009436277251021107 249338986514154415876531661)
      ·
        refine ⟨93502119942807905953699373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249338986514154415876531661 93502119942807905953699373)
        ·
          refine ⟨35063294978552964732637265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93502119942807905953699373 35063294978552964732637265)
          ·
            refine ⟨26297471233914723549477949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35063294978552964732637265 26297471233914723549477949)
            ·
              refine ⟨9861551712718021331054231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26297471233914723549477949 9861551712718021331054231)
              ·
                refine ⟨14792327569077031996581347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861551712718021331054231 14792327569077031996581347)
                ·
                  refine ⟨22188491353615547994872021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14792327569077031996581347 22188491353615547994872021)
                  ·
                    refine ⟨520042766100364406129813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22188491353615547994872021 520042766100364406129813)
                    ·
                      rfl

theorem cell23_3038339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_3038339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038339 prefixEnd_3038339 := by exact prefixLift 3038339
  have htrace : WordTrace (prefixWord ++ tailWord_3038339) baseStart_3038339 baseEnd_3038339 := by
    simpa [prefixWord, tailWord_3038339, baseEnd_3038339] using wordTrace_append hprefix tailTrace_3038339
  have hstable : (prefixWord ++ tailWord_3038339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038339).length < 2 ^ (prefixWord ++ tailWord_3038339).sum := by decide
  have hdescent : baseEnd_3038339 < baseStart_3038339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038399 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 8]
def baseStart_3038399 : Nat := 118140960795 + 3038399 * 2 ^ 59
def prefixEnd_3038399 : Nat := 4983230072969 + 3 ^ 40 * 3038399 * 2
def baseEnd_3038399 : Nat := 173351011904484775959907

theorem tailTrace_3038399 : CollatzResearch.WordTrace tailWord_3038399 prefixEnd_3038399 173351011904484775959907 := by
  unfold tailWord_3038399
  simp only [CollatzResearch.WordTrace]
  refine ⟨110819515719406815081198251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73879677146271210054132167 110819515719406815081198251)
  ·
    refine ⟨166229273579110222621797377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110819515719406815081198251 166229273579110222621797377)
    ·
      refine ⟨124671955184332666966348033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166229273579110222621797377 124671955184332666966348033)
      ·
        refine ⟨93503966388249500224761025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124671955184332666966348033 93503966388249500224761025)
        ·
          refine ⟨70127974791187125168570769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93503966388249500224761025 70127974791187125168570769)
          ·
            refine ⟨52595981093390343876428077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70127974791187125168570769 52595981093390343876428077)
            ·
              refine ⟨19723492910021378953660529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52595981093390343876428077 19723492910021378953660529)
              ·
                refine ⟨14792619682516034215245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19723492910021378953660529 14792619682516034215245397)
                ·
                  refine ⟨173351011904484775959907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14792619682516034215245397 173351011904484775959907)
                  ·
                    rfl

theorem cell23_3038399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 8].length) (baseStart_3038399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038399 prefixEnd_3038399 := by exact prefixLift 3038399
  have htrace : WordTrace (prefixWord ++ tailWord_3038399) baseStart_3038399 baseEnd_3038399 := by
    simpa [prefixWord, tailWord_3038399, baseEnd_3038399] using wordTrace_append hprefix tailTrace_3038399
  have hstable : (prefixWord ++ tailWord_3038399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038399).length < 2 ^ (prefixWord ++ tailWord_3038399).sum := by decide
  have hdescent : baseEnd_3038399 < baseStart_3038399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038403 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 1, 4]
def baseStart_3038403 : Nat := 118140960795 + 3038403 * 2 ^ 59
def prefixEnd_3038403 : Nat := 4983230072969 + 3 ^ 40 * 3038403 * 2
def baseEnd_3038403 : Nat := 520053720354326989329715

theorem tailTrace_3038403 : CollatzResearch.WordTrace tailWord_3038403 prefixEnd_3038403 520053720354326989329715 := by
  unfold tailWord_3038403
  simp only [CollatzResearch.WordTrace]
  refine ⟨110819661611392323764343863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73879774407594882509562575 110819661611392323764343863)
  ·
    refine ⟨166229492417088485646515795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110819661611392323764343863 166229492417088485646515795)
    ·
      refine ⟨249344238625632728469773693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166229492417088485646515795 249344238625632728469773693)
      ·
        refine ⟨93504089484612273176165135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249344238625632728469773693 93504089484612273176165135)
        ·
          refine ⟨140256134226918409764247703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93504089484612273176165135 140256134226918409764247703)
          ·
            refine ⟨210384201340377614646371555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140256134226918409764247703 210384201340377614646371555)
            ·
              refine ⟨315576302010566421969557333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210384201340377614646371555 315576302010566421969557333)
              ·
                refine ⟨1849079894593162628727875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 315576302010566421969557333 1849079894593162628727875)
                ·
                  refine ⟨2773619841889743943091813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849079894593162628727875 2773619841889743943091813)
                  ·
                    refine ⟨520053720354326989329715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2773619841889743943091813 520053720354326989329715)
                    ·
                      rfl

theorem cell23_3038403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 4].length) (baseStart_3038403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038403 prefixEnd_3038403 := by exact prefixLift 3038403
  have htrace : WordTrace (prefixWord ++ tailWord_3038403) baseStart_3038403 baseEnd_3038403 := by
    simpa [prefixWord, tailWord_3038403, baseEnd_3038403] using wordTrace_append hprefix tailTrace_3038403
  have hstable : (prefixWord ++ tailWord_3038403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038403).length < 2 ^ (prefixWord ++ tailWord_3038403).sum := by decide
  have hdescent : baseEnd_3038403 < baseStart_3038403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038433 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 6]
def baseStart_3038433 : Nat := 118140960795 + 3038433 * 2 ^ 59
def prefixEnd_3038433 : Nat := 4983230072969 + 3 ^ 40 * 3038433 * 2
def baseEnd_3038433 : Nat := 173352951720290650068223

theorem tailTrace_3038433 : CollatzResearch.WordTrace tailWord_3038433 prefixEnd_3038433 173352951720290650068223 := by
  unfold tailWord_3038433
  simp only [CollatzResearch.WordTrace]
  refine ⟨110820755801283638887935953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73880503867522425925290635 110820755801283638887935953)
  ·
    refine ⟨83115566850962729165951965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110820755801283638887935953 83115566850962729165951965)
    ·
      refine ⟨31168337569111023437231987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83115566850962729165951965 31168337569111023437231987)
      ·
        refine ⟨46752506353666535155847981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31168337569111023437231987 46752506353666535155847981)
        ·
          refine ⟨17532189882624950683442993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46752506353666535155847981 17532189882624950683442993)
          ·
            refine ⟨13149142411968713012582245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17532189882624950683442993 13149142411968713012582245)
            ·
              refine ⟨2465464202244133689859171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13149142411968713012582245 2465464202244133689859171)
              ·
                refine ⟨3698196303366200534788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465464202244133689859171 3698196303366200534788757)
                ·
                  refine ⟨173352951720290650068223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3698196303366200534788757 173352951720290650068223)
                  ·
                    rfl

theorem cell23_3038433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_3038433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038433 prefixEnd_3038433 := by exact prefixLift 3038433
  have htrace : WordTrace (prefixWord ++ tailWord_3038433) baseStart_3038433 baseEnd_3038433 := by
    simpa [prefixWord, tailWord_3038433, baseEnd_3038433] using wordTrace_append hprefix tailTrace_3038433
  have hstable : (prefixWord ++ tailWord_3038433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038433).length < 2 ^ (prefixWord ++ tailWord_3038433).sum := by decide
  have hdescent : baseEnd_3038433 < baseStart_3038433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038493 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_3038493 : Nat := 118140960795 + 3038493 * 2 ^ 59
def prefixEnd_3038493 : Nat := 4983230072969 + 3 ^ 40 * 3038493 * 2
def baseEnd_3038493 : Nat := 520069124773961871954577

theorem tailTrace_3038493 : CollatzResearch.WordTrace tailWord_3038493 prefixEnd_3038493 520069124773961871954577 := by
  unfold tailWord_3038493
  simp only [CollatzResearch.WordTrace]
  refine ⟨110822944181066269135120133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73881962787377512756746755 110822944181066269135120133)
  ·
    refine ⟨20779302033949925462835025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110822944181066269135120133 20779302033949925462835025)
    ·
      refine ⟨15584476525462444097126269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20779302033949925462835025 15584476525462444097126269)
      ·
        refine ⟨5844178697048416536422351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15584476525462444097126269 5844178697048416536422351)
        ·
          refine ⟨8766268045572624804633527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844178697048416536422351 8766268045572624804633527)
          ·
            refine ⟨13149402068358937206950291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766268045572624804633527 13149402068358937206950291)
            ·
              refine ⟨19724103102538405810425437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13149402068358937206950291 19724103102538405810425437)
              ·
                refine ⟨7396538663451902178909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19724103102538405810425437 7396538663451902178909539)
                ·
                  refine ⟨11094807995177853268364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7396538663451902178909539 11094807995177853268364309)
                  ·
                    refine ⟨520069124773961871954577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11094807995177853268364309 520069124773961871954577)
                    ·
                      rfl

theorem cell23_3038493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_3038493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038493 prefixEnd_3038493 := by exact prefixLift 3038493
  have htrace : WordTrace (prefixWord ++ tailWord_3038493) baseStart_3038493 baseEnd_3038493 := by
    simpa [prefixWord, tailWord_3038493, baseEnd_3038493] using wordTrace_append hprefix tailTrace_3038493
  have hstable : (prefixWord ++ tailWord_3038493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038493).length < 2 ^ (prefixWord ++ tailWord_3038493).sum := by decide
  have hdescent : baseEnd_3038493 < baseStart_3038493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038494 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3038494 : Nat := 118140960795 + 3038494 * 2 ^ 59
def prefixEnd_3038494 : Nat := 4983230072969 + 3 ^ 40 * 3038494 * 2
def baseEnd_3038494 : Nat := 1560207887802540111951227

theorem tailTrace_3038494 : CollatzResearch.WordTrace tailWord_3038494 prefixEnd_3038494 1560207887802540111951227 := by
  unfold tailWord_3038494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852872581757830788238317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73881987102708430870604357 13852872581757830788238317)
  ·
    refine ⟨5194827218159186545589369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13852872581757830788238317 5194827218159186545589369)
    ·
      refine ⟨3896120413619389909192027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5194827218159186545589369 3896120413619389909192027)
      ·
        refine ⟨5844180620429084863788041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896120413619389909192027 5844180620429084863788041)
        ·
          refine ⟨4383135465321813647841031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5844180620429084863788041 4383135465321813647841031)
          ·
            refine ⟨6574703197982720471761547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383135465321813647841031 6574703197982720471761547)
            ·
              refine ⟨9862054796974080707642321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574703197982720471761547 9862054796974080707642321)
              ·
                refine ⟨7396541097730560530731741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9862054796974080707642321 7396541097730560530731741)
                ·
                  refine ⟨2773702911648960199024403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7396541097730560530731741 2773702911648960199024403)
                  ·
                    refine ⟨4160554367473440298536605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2773702911648960199024403 4160554367473440298536605)
                    ·
                      refine ⟨1560207887802540111951227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4160554367473440298536605 1560207887802540111951227)
                      ·
                        rfl

theorem cell23_3038494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3038494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038494 prefixEnd_3038494 := by exact prefixLift 3038494
  have htrace : WordTrace (prefixWord ++ tailWord_3038494) baseStart_3038494 baseEnd_3038494 := by
    simpa [prefixWord, tailWord_3038494, baseEnd_3038494] using wordTrace_append hprefix tailTrace_3038494
  have hstable : (prefixWord ++ tailWord_3038494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038494).length < 2 ^ (prefixWord ++ tailWord_3038494).sum := by decide
  have hdescent : baseEnd_3038494 < baseStart_3038494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038513 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3038513 : Nat := 118140960795 + 3038513 * 2 ^ 59
def prefixEnd_3038513 : Nat := 4983230072969 + 3 ^ 40 * 3038513 * 2
def baseEnd_3038513 : Nat := 1560217643934975537613639

theorem tailTrace_3038513 : CollatzResearch.WordTrace tailWord_3038513 prefixEnd_3038513 1560217643934975537613639 := by
  unfold tailWord_3038513
  simp only [CollatzResearch.WordTrace]
  refine ⟨110823673640993812550848193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73882449093995875033898795 110823673640993812550848193)
  ·
    refine ⟨83117755230745359413136145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110823673640993812550848193 83117755230745359413136145)
    ·
      refine ⟨62338316423059019559852109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83117755230745359413136145 62338316423059019559852109)
      ·
        refine ⟨23376868658647132334944541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62338316423059019559852109 23376868658647132334944541)
        ·
          refine ⟨8766325746992674625604203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23376868658647132334944541 8766325746992674625604203)
          ·
            refine ⟨13149488620489011938406305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766325746992674625604203 13149488620489011938406305)
            ·
              refine ⟨9862116465366758953804729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13149488620489011938406305 9862116465366758953804729)
              ·
                refine ⟨7396587349025069215353547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9862116465366758953804729 7396587349025069215353547)
                ·
                  refine ⟨11094881023537603823030321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7396587349025069215353547 11094881023537603823030321)
                  ·
                    refine ⟨8321160767653202867272741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11094881023537603823030321 8321160767653202867272741)
                    ·
                      refine ⟨1560217643934975537613639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321160767653202867272741 1560217643934975537613639)
                      ·
                        rfl

theorem cell23_3038513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3038513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038513 prefixEnd_3038513 := by exact prefixLift 3038513
  have htrace : WordTrace (prefixWord ++ tailWord_3038513) baseStart_3038513 baseEnd_3038513 := by
    simpa [prefixWord, tailWord_3038513, baseEnd_3038513] using wordTrace_append hprefix tailTrace_3038513
  have hstable : (prefixWord ++ tailWord_3038513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038513).length < 2 ^ (prefixWord ++ tailWord_3038513).sum := by decide
  have hdescent : baseEnd_3038513 < baseStart_3038513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038517 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_3038517 : Nat := 118140960795 + 3038517 * 2 ^ 59
def prefixEnd_3038517 : Nat := 4983230072969 + 3 ^ 40 * 3038517 * 2
def baseEnd_3038517 : Nat := 1560219697857593521963621

theorem tailTrace_3038517 : CollatzResearch.WordTrace tailWord_3038517 prefixEnd_3038517 1560219697857593521963621 := by
  unfold tailWord_3038517
  simp only [CollatzResearch.WordTrace]
  refine ⟨110823819532979321233993805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73882546355319547489329203 110823819532979321233993805)
  ·
    refine ⟨41558932324867245462747677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110823819532979321233993805 41558932324867245462747677)
    ·
      refine ⟨15584599621825217048530379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41558932324867245462747677 15584599621825217048530379)
      ·
        refine ⟨23376899432737825572795569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15584599621825217048530379 23376899432737825572795569)
        ·
          refine ⟨17532674574553369179596677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23376899432737825572795569 17532674574553369179596677)
          ·
            refine ⟨3287376482728756721174377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17532674574553369179596677 3287376482728756721174377)
            ·
              refine ⟨2465532362046567540880783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287376482728756721174377 2465532362046567540880783)
              ·
                refine ⟨3698298543069851311321175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465532362046567540880783 3698298543069851311321175)
                ·
                  refine ⟨5547447814604776966981763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698298543069851311321175 5547447814604776966981763)
                  ·
                    refine ⟨8321171721907165450472645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547447814604776966981763 8321171721907165450472645)
                    ·
                      refine ⟨1560219697857593521963621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321171721907165450472645 1560219697857593521963621)
                      ·
                        rfl

theorem cell23_3038517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_3038517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038517 prefixEnd_3038517 := by exact prefixLift 3038517
  have htrace : WordTrace (prefixWord ++ tailWord_3038517) baseStart_3038517 baseEnd_3038517 := by
    simpa [prefixWord, tailWord_3038517, baseEnd_3038517] using wordTrace_append hprefix tailTrace_3038517
  have hstable : (prefixWord ++ tailWord_3038517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038517).length < 2 ^ (prefixWord ++ tailWord_3038517).sum := by decide
  have hdescent : baseEnd_3038517 < baseStart_3038517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038557 : List Nat := [1, 4, 5, 1, 1, 1, 1, 9]
def baseStart_3038557 : Nat := 118140960795 + 3038557 * 2 ^ 59
def prefixEnd_3038557 : Nat := 4983230072969 + 3 ^ 40 * 3038557 * 2
def baseEnd_3038557 : Nat := 57786675447547161683831

theorem tailTrace_3038557 : CollatzResearch.WordTrace tailWord_3038557 prefixEnd_3038557 57786675447547161683831 := by
  unfold tailWord_3038557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110825278452834408065449925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73883518968556272043633283 110825278452834408065449925)
  ·
    refine ⟨20779739709906451512271861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110825278452834408065449925 20779739709906451512271861)
    ·
      refine ⟨1948100597803729829275487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20779739709906451512271861 1948100597803729829275487)
      ·
        refine ⟨2922150896705594743913231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948100597803729829275487 2922150896705594743913231)
        ·
          refine ⟨4383226345058392115869847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922150896705594743913231 4383226345058392115869847)
          ·
            refine ⟨6574839517587588173804771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383226345058392115869847 6574839517587588173804771)
            ·
              refine ⟨9862259276381382260707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574839517587588173804771 9862259276381382260707157)
              ·
                refine ⟨57786675447547161683831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9862259276381382260707157 57786675447547161683831)
                ·
                  rfl

theorem cell23_3038557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 9].length) (baseStart_3038557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038557 prefixEnd_3038557 := by exact prefixLift 3038557
  have htrace : WordTrace (prefixWord ++ tailWord_3038557) baseStart_3038557 baseEnd_3038557 := by
    simpa [prefixWord, tailWord_3038557, baseEnd_3038557] using wordTrace_append hprefix tailTrace_3038557
  have hstable : (prefixWord ++ tailWord_3038557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038557).length < 2 ^ (prefixWord ++ tailWord_3038557).sum := by decide
  have hdescent : baseEnd_3038557 < baseStart_3038557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038568 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3038568 : Nat := 118140960795 + 3038568 * 2 ^ 59
def prefixEnd_3038568 : Nat := 4983230072969 + 3 ^ 40 * 3038568 * 2
def baseEnd_3038568 : Nat := 1560245885370972822425887

theorem tailTrace_3038568 : CollatzResearch.WordTrace tailWord_3038568 prefixEnd_3038568 1560245885370972822425887 := by
  unfold tailWord_3038568
  simp only [CollatzResearch.WordTrace]
  refine ⟨55412839827897278472050179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73883786437196371296066905 55412839827897278472050179)
  ·
    refine ⟨83119259741845917708075269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55412839827897278472050179 83119259741845917708075269)
    ·
      refine ⟨15584861201596109570264113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83119259741845917708075269 15584861201596109570264113)
      ·
        refine ⟨11688645901197082177698085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15584861201596109570264113 11688645901197082177698085)
        ·
          refine ⟨2191621106474452908318391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11688645901197082177698085 2191621106474452908318391)
          ·
            refine ⟨3287431659711679362477587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191621106474452908318391 3287431659711679362477587)
            ·
              refine ⟨4931147489567519043716381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287431659711679362477587 4931147489567519043716381)
              ·
                refine ⟨1849180308587819641393643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4931147489567519043716381 1849180308587819641393643)
                ·
                  refine ⟨2773770462881729462090465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849180308587819641393643 2773770462881729462090465)
                  ·
                    refine ⟨2080327847161297096567849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2773770462881729462090465 2080327847161297096567849)
                    ·
                      refine ⟨1560245885370972822425887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080327847161297096567849 1560245885370972822425887)
                      ·
                        rfl

theorem cell23_3038568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3038568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038568 prefixEnd_3038568 := by exact prefixLift 3038568
  have htrace : WordTrace (prefixWord ++ tailWord_3038568) baseStart_3038568 baseEnd_3038568 := by
    simpa [prefixWord, tailWord_3038568, baseEnd_3038568] using wordTrace_append hprefix tailTrace_3038568
  have hstable : (prefixWord ++ tailWord_3038568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038568).length < 2 ^ (prefixWord ++ tailWord_3038568).sum := by decide
  have hdescent : baseEnd_3038568 < baseStart_3038568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038601 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 2, 1, 3]
def baseStart_3038601 : Nat := 118140960795 + 3038601 * 2 ^ 59
def prefixEnd_3038601 : Nat := 4983230072969 + 3 ^ 40 * 3038601 * 2
def baseEnd_3038601 : Nat := 1560262830232571193313235

theorem tailTrace_3038601 : CollatzResearch.WordTrace tailWord_3038601 prefixEnd_3038601 1560262830232571193313235 := by
  unfold tailWord_3038601
  simp only [CollatzResearch.WordTrace]
  refine ⟨110826883264675003580051657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73884588843116669053367771 110826883264675003580051657)
  ·
    refine ⟨83120162448506252685038743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110826883264675003580051657 83120162448506252685038743)
    ·
      refine ⟨124680243672759379027558115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83120162448506252685038743 124680243672759379027558115)
      ·
        refine ⟨187020365509139068541337173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124680243672759379027558115 187020365509139068541337173)
        ·
          refine ⟨2191644908310223459468795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 187020365509139068541337173 2191644908310223459468795)
          ·
            refine ⟨3287467362465335189203193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191644908310223459468795 3287467362465335189203193)
            ·
              refine ⟨2465600521849001391902395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287467362465335189203193 2465600521849001391902395)
              ·
                refine ⟨3698400782773502087853593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465600521849001391902395 3698400782773502087853593)
                ·
                  refine ⟨2773800587080126565890195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698400782773502087853593 2773800587080126565890195)
                  ·
                    refine ⟨4160700880620189848835293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2773800587080126565890195 4160700880620189848835293)
                    ·
                      refine ⟨1560262830232571193313235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4160700880620189848835293 1560262830232571193313235)
                      ·
                        rfl

theorem cell23_3038601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 1, 3].length) (baseStart_3038601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038601 prefixEnd_3038601 := by exact prefixLift 3038601
  have htrace : WordTrace (prefixWord ++ tailWord_3038601) baseStart_3038601 baseEnd_3038601 := by
    simpa [prefixWord, tailWord_3038601, baseEnd_3038601] using wordTrace_append hprefix tailTrace_3038601
  have hstable : (prefixWord ++ tailWord_3038601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038601).length < 2 ^ (prefixWord ++ tailWord_3038601).sum := by decide
  have hdescent : baseEnd_3038601 < baseStart_3038601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038653 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3038653 : Nat := 118140960795 + 3038653 * 2 ^ 59
def prefixEnd_3038653 : Nat := 4983230072969 + 3 ^ 40 * 3038653 * 2
def baseEnd_3038653 : Nat := 1560289531226604989862995

theorem tailTrace_3038653 : CollatzResearch.WordTrace tailWord_3038653 prefixEnd_3038653 1560289531226604989862995 := by
  unfold tailWord_3038653
  simp only [CollatzResearch.WordTrace]
  refine ⟨110828779860486616460944613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73885853240324410973963075 110828779860486616460944613)
  ·
    refine ⟨20780396223841240586427115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110828779860486616460944613 20780396223841240586427115)
    ·
      refine ⟨31170594335761860879640673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20780396223841240586427115 31170594335761860879640673)
      ·
        refine ⟨23377945751821395659730505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31170594335761860879640673 23377945751821395659730505)
        ·
          refine ⟨17533459313866046744797879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23377945751821395659730505 17533459313866046744797879)
          ·
            refine ⟨26300188970799070117196819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17533459313866046744797879 26300188970799070117196819)
            ·
              refine ⟨39450283456198605175795229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26300188970799070117196819 39450283456198605175795229)
              ·
                refine ⟨14793856296074476940923211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39450283456198605175795229 14793856296074476940923211)
                ·
                  refine ⟨22190784444111715411384817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14793856296074476940923211 22190784444111715411384817)
                  ·
                    refine ⟨16643088333083786558538613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22190784444111715411384817 16643088333083786558538613)
                    ·
                      refine ⟨1560289531226604989862995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16643088333083786558538613 1560289531226604989862995)
                      ·
                        rfl

theorem cell23_3038653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3038653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038653 prefixEnd_3038653 := by exact prefixLift 3038653
  have htrace : WordTrace (prefixWord ++ tailWord_3038653) baseStart_3038653 baseEnd_3038653 := by
    simpa [prefixWord, tailWord_3038653, baseEnd_3038653] using wordTrace_append hprefix tailTrace_3038653
  have hstable : (prefixWord ++ tailWord_3038653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038653).length < 2 ^ (prefixWord ++ tailWord_3038653).sum := by decide
  have hdescent : baseEnd_3038653 < baseStart_3038653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038663 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3038663 : Nat := 118140960795 + 3038663 * 2 ^ 59
def prefixEnd_3038663 : Nat := 4983230072969 + 3 ^ 40 * 3038663 * 2
def baseEnd_3038663 : Nat := 1560294666033149950737949

theorem tailTrace_3038663 : CollatzResearch.WordTrace tailWord_3038663 prefixEnd_3038663 1560294666033149950737949 := by
  unfold tailWord_3038663
  simp only [CollatzResearch.WordTrace]
  refine ⟨110829144590450388168808643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73886096393633592112539095 110829144590450388168808643)
  ·
    refine ⟨166243716885675582253212965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110829144590450388168808643 166243716885675582253212965)
    ·
      refine ⟨31170696916064171672477431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166243716885675582253212965 31170696916064171672477431)
      ·
        refine ⟨46756045374096257508716147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31170696916064171672477431 46756045374096257508716147)
        ·
          refine ⟨70134068061144386263074221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46756045374096257508716147 70134068061144386263074221)
          ·
            refine ⟨26300275522929144848652833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70134068061144386263074221 26300275522929144848652833)
            ·
              refine ⟨19725206642196858636489625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26300275522929144848652833 19725206642196858636489625)
              ·
                refine ⟨14793904981647643977367219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19725206642196858636489625 14793904981647643977367219)
                ·
                  refine ⟨22190857472471465966050829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14793904981647643977367219 22190857472471465966050829)
                  ·
                    refine ⟨8321571552176799737269061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22190857472471465966050829 8321571552176799737269061)
                    ·
                      refine ⟨1560294666033149950737949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321571552176799737269061 1560294666033149950737949)
                      ·
                        rfl

theorem cell23_3038663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3038663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038663 prefixEnd_3038663 := by exact prefixLift 3038663
  have htrace : WordTrace (prefixWord ++ tailWord_3038663) baseStart_3038663 baseEnd_3038663 := by
    simpa [prefixWord, tailWord_3038663, baseEnd_3038663] using wordTrace_append hprefix tailTrace_3038663
  have hstable : (prefixWord ++ tailWord_3038663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038663).length < 2 ^ (prefixWord ++ tailWord_3038663).sum := by decide
  have hdescent : baseEnd_3038663 < baseStart_3038663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038680 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3038680 : Nat := 118140960795 + 3038680 * 2 ^ 59
def prefixEnd_3038680 : Nat := 4983230072969 + 3 ^ 40 * 3038680 * 2
def baseEnd_3038680 : Nat := 1560303395204276384225371

theorem tailTrace_3038680 : CollatzResearch.WordTrace tailWord_3038680 prefixEnd_3038680 1560303395204276384225371 := by
  unfold tailWord_3038680
  simp only [CollatzResearch.WordTrace]
  refine ⟨55414882315694400036088747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73886509754259200048118329 55414882315694400036088747)
  ·
    refine ⟨83122323473541600054133121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55414882315694400036088747 83122323473541600054133121)
    ·
      refine ⟨62341742605156200040599841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83122323473541600054133121 62341742605156200040599841)
      ·
        refine ⟨46756306953867150030449881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62341742605156200040599841 46756306953867150030449881)
        ·
          refine ⟨35067230215400362522837411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46756306953867150030449881 35067230215400362522837411)
          ·
            refine ⟨52600845323100543784256117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35067230215400362522837411 52600845323100543784256117)
            ·
              refine ⟨4931329249040675979774011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52600845323100543784256117 4931329249040675979774011)
              ·
                refine ⟨7396993873561013969661017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931329249040675979774011 7396993873561013969661017)
                ·
                  refine ⟨5547745405170760477245763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7396993873561013969661017 5547745405170760477245763)
                  ·
                    refine ⟨8321618107756140715868645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547745405170760477245763 8321618107756140715868645)
                    ·
                      refine ⟨1560303395204276384225371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321618107756140715868645 1560303395204276384225371)
                      ·
                        rfl

theorem cell23_3038680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3038680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038680 prefixEnd_3038680 := by exact prefixLift 3038680
  have htrace : WordTrace (prefixWord ++ tailWord_3038680) baseStart_3038680 baseEnd_3038680 := by
    simpa [prefixWord, tailWord_3038680, baseEnd_3038680] using wordTrace_append hprefix tailTrace_3038680
  have hstable : (prefixWord ++ tailWord_3038680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038680).length < 2 ^ (prefixWord ++ tailWord_3038680).sum := by decide
  have hdescent : baseEnd_3038680 < baseStart_3038680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038770 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3038770 : Nat := 118140960795 + 3038770 * 2 ^ 59
def prefixEnd_3038770 : Nat := 4983230072969 + 3 ^ 40 * 3038770 * 2
def baseEnd_3038770 : Nat := 1560349608463181032099957

theorem tailTrace_3038770 : CollatzResearch.WordTrace tailWord_3038770 prefixEnd_3038770 1560349608463181032099957 := by
  unfold tailWord_3038770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708261800265686360738441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73888698134041830295302509 27708261800265686360738441)
  ·
    refine ⟨20781196350199264770553831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27708261800265686360738441 20781196350199264770553831)
    ·
      refine ⟨31171794525298897155830747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20781196350199264770553831 31171794525298897155830747)
      ·
        refine ⟨46757691787948345733746121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31171794525298897155830747 46757691787948345733746121)
        ·
          refine ⟨35068268840961259300309591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46757691787948345733746121 35068268840961259300309591)
          ·
            refine ⟨52602403261441888950464387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35068268840961259300309591 52602403261441888950464387)
            ·
              refine ⟨78903604892162833425696581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52602403261441888950464387 78903604892162833425696581)
              ·
                refine ⟨14794425917280531267318109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78903604892162833425696581 14794425917280531267318109)
                ·
                  refine ⟨5547909718980199225244291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14794425917280531267318109 5547909718980199225244291)
                  ·
                    refine ⟨8321864578470298837866437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547909718980199225244291 8321864578470298837866437)
                    ·
                      refine ⟨1560349608463181032099957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321864578470298837866437 1560349608463181032099957)
                      ·
                        rfl

theorem cell23_3038770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3038770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038770 prefixEnd_3038770 := by exact prefixLift 3038770
  have htrace : WordTrace (prefixWord ++ tailWord_3038770) baseStart_3038770 baseEnd_3038770 := by
    simpa [prefixWord, tailWord_3038770, baseEnd_3038770] using wordTrace_append hprefix tailTrace_3038770
  have hstable : (prefixWord ++ tailWord_3038770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038770).length < 2 ^ (prefixWord ++ tailWord_3038770).sum := by decide
  have hdescent : baseEnd_3038770 < baseStart_3038770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038800 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_3038800 : Nat := 118140960795 + 3038800 * 2 ^ 59
def prefixEnd_3038800 : Nat := 4983230072969 + 3 ^ 40 * 3038800 * 2
def baseEnd_3038800 : Nat := 1560365012882815914724819

theorem tailTrace_3038800 : CollatzResearch.WordTrace tailWord_3038800 prefixEnd_3038800 1560365012882815914724819 := by
  unfold tailWord_3038800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55417070695477030283272927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73889427593969373711030569 55417070695477030283272927)
  ·
    refine ⟨83125606043215545424909391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55417070695477030283272927 83125606043215545424909391)
    ·
      refine ⟨124688409064823318137364087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83125606043215545424909391 124688409064823318137364087)
      ·
        refine ⟨187032613597234977206046131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124688409064823318137364087 187032613597234977206046131)
        ·
          refine ⟨280548920395852465809069197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187032613597234977206046131 280548920395852465809069197)
          ·
            refine ⟨105205845148444674678400949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280548920395852465809069197 105205845148444674678400949)
            ·
              refine ⟨9863047982666688251100089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105205845148444674678400949 9863047982666688251100089)
              ·
                refine ⟨7397285987000016188325067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9863047982666688251100089 7397285987000016188325067)
                ·
                  refine ⟨11095928980500024282487601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397285987000016188325067 11095928980500024282487601)
                  ·
                    refine ⟨8321946735375018211865701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11095928980500024282487601 8321946735375018211865701)
                    ·
                      refine ⟨1560365012882815914724819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321946735375018211865701 1560365012882815914724819)
                      ·
                        rfl

theorem cell23_3038800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_3038800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038800 prefixEnd_3038800 := by exact prefixLift 3038800
  have htrace : WordTrace (prefixWord ++ tailWord_3038800) baseStart_3038800 baseEnd_3038800 := by
    simpa [prefixWord, tailWord_3038800, baseEnd_3038800] using wordTrace_append hprefix tailTrace_3038800
  have hstable : (prefixWord ++ tailWord_3038800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038800).length < 2 ^ (prefixWord ++ tailWord_3038800).sum := by decide
  have hdescent : baseEnd_3038800 < baseStart_3038800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038804 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_3038804 : Nat := 118140960795 + 3038804 * 2 ^ 59
def prefixEnd_3038804 : Nat := 4983230072969 + 3 ^ 40 * 3038804 * 2
def baseEnd_3038804 : Nat := 1560367066805433899074801

theorem tailTrace_3038804 : CollatzResearch.WordTrace tailWord_3038804 prefixEnd_3038804 1560367066805433899074801 := by
  unfold tailWord_3038804
  simp only [CollatzResearch.WordTrace]
  refine ⟨55417143641469784624845733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73889524855293046166460977 55417143641469784624845733)
  ·
    refine ⟨10390714432775584617158575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55417143641469784624845733 10390714432775584617158575)
    ·
      refine ⟨15586071649163376925737863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390714432775584617158575 15586071649163376925737863)
      ·
        refine ⟨23379107473745065388606795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15586071649163376925737863 23379107473745065388606795)
        ·
          refine ⟨35068661210617598082910193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23379107473745065388606795 35068661210617598082910193)
          ·
            refine ⟨26301495907963198562182645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35068661210617598082910193 26301495907963198562182645)
            ·
              refine ⟨2465765241371549865204623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26301495907963198562182645 2465765241371549865204623)
              ·
                refine ⟨3698647862057324797806935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465765241371549865204623 3698647862057324797806935)
                ·
                  refine ⟨5547971793085987196710403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3698647862057324797806935 5547971793085987196710403)
                  ·
                    refine ⟨8321957689628980795065605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5547971793085987196710403 8321957689628980795065605)
                    ·
                      refine ⟨1560367066805433899074801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8321957689628980795065605 1560367066805433899074801)
                      ·
                        rfl

theorem cell23_3038804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_3038804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038804 prefixEnd_3038804 := by exact prefixLift 3038804
  have htrace : WordTrace (prefixWord ++ tailWord_3038804) baseStart_3038804 baseEnd_3038804 := by
    simpa [prefixWord, tailWord_3038804, baseEnd_3038804] using wordTrace_append hprefix tailTrace_3038804
  have hstable : (prefixWord ++ tailWord_3038804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038804).length < 2 ^ (prefixWord ++ tailWord_3038804).sum := by decide
  have hdescent : baseEnd_3038804 < baseStart_3038804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038807 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3038807 : Nat := 118140960795 + 3038807 * 2 ^ 59
def prefixEnd_3038807 : Nat := 4983230072969 + 3 ^ 40 * 3038807 * 2
def baseEnd_3038807 : Nat := 1560368607247397387337287

theorem tailTrace_3038807 : CollatzResearch.WordTrace tailWord_3038807 prefixEnd_3038807 1560368607247397387337287 := by
  unfold tailWord_3038807
  simp only [CollatzResearch.WordTrace]
  refine ⟨110834396701928700762050675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73889597801285800508033783 110834396701928700762050675)
  ·
    refine ⟨166251595052893051143076013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110834396701928700762050675 166251595052893051143076013)
    ·
      refine ⟨62344348144834894178653505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166251595052893051143076013 62344348144834894178653505)
      ·
        refine ⟨46758261108626170633990129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62344348144834894178653505 46758261108626170633990129)
        ·
          refine ⟨35068695831469627975492597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46758261108626170633990129 35068695831469627975492597)
          ·
            refine ⟨3287690234200277622702431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35068695831469627975492597 3287690234200277622702431)
            ·
              refine ⟨4931535351300416434053647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287690234200277622702431 4931535351300416434053647)
              ·
                refine ⟨7397303026950624651080471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931535351300416434053647 7397303026950624651080471)
                ·
                  refine ⟨11095954540425936976620707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397303026950624651080471 11095954540425936976620707)
                  ·
                    refine ⟨16643931810638905464931061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11095954540425936976620707 16643931810638905464931061)
                    ·
                      refine ⟨1560368607247397387337287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16643931810638905464931061 1560368607247397387337287)
                      ·
                        rfl

theorem cell23_3038807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3038807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038807 prefixEnd_3038807 := by exact prefixLift 3038807
  have htrace : WordTrace (prefixWord ++ tailWord_3038807) baseStart_3038807 baseEnd_3038807 := by
    simpa [prefixWord, tailWord_3038807, baseEnd_3038807] using wordTrace_append hprefix tailTrace_3038807
  have hstable : (prefixWord ++ tailWord_3038807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038807).length < 2 ^ (prefixWord ++ tailWord_3038807).sum := by decide
  have hdescent : baseEnd_3038807 < baseStart_3038807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038871 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3038871 : Nat := 118140960795 + 3038871 * 2 ^ 59
def prefixEnd_3038871 : Nat := 4983230072969 + 3 ^ 40 * 3038871 * 2
def baseEnd_3038871 : Nat := 1560401470009285136936993

theorem tailTrace_3038871 : CollatzResearch.WordTrace tailWord_3038871 prefixEnd_3038871 1560401470009285136936993 := by
  unfold tailWord_3038871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110836730973696839692380467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73891153982464559794920311 110836730973696839692380467)
  ·
    refine ⟨166255096460545259538570701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110836730973696839692380467 166255096460545259538570701)
    ·
      refine ⟨62345661172704472326964013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166255096460545259538570701 62345661172704472326964013)
      ·
        refine ⟨23379622939764177122611505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62345661172704472326964013 23379622939764177122611505)
        ·
          refine ⟨17534717204823132841958629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23379622939764177122611505 17534717204823132841958629)
          ·
            refine ⟨3287759475904337407867243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17534717204823132841958629 3287759475904337407867243)
            ·
              refine ⟨4931639213856506111800865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287759475904337407867243 4931639213856506111800865)
              ·
                refine ⟨3698729410392379583850649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931639213856506111800865 3698729410392379583850649)
                ·
                  refine ⟨2774047057794284687887987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698729410392379583850649 2774047057794284687887987)
                  ·
                    refine ⟨4161070586691427031831981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2774047057794284687887987 4161070586691427031831981)
                    ·
                      refine ⟨1560401470009285136936993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4161070586691427031831981 1560401470009285136936993)
                      ·
                        rfl

theorem cell23_3038871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3038871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038871 prefixEnd_3038871 := by exact prefixLift 3038871
  have htrace : WordTrace (prefixWord ++ tailWord_3038871) baseStart_3038871 baseEnd_3038871 := by
    simpa [prefixWord, tailWord_3038871, baseEnd_3038871] using wordTrace_append hprefix tailTrace_3038871
  have hstable : (prefixWord ++ tailWord_3038871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038871).length < 2 ^ (prefixWord ++ tailWord_3038871).sum := by decide
  have hdescent : baseEnd_3038871 < baseStart_3038871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038945 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_3038945 : Nat := 118140960795 + 3038945 * 2 ^ 59
def prefixEnd_3038945 : Nat := 4983230072969 + 3 ^ 40 * 3038945 * 2
def baseEnd_3038945 : Nat := 1560439467577717847411653

theorem tailTrace_3038945 : CollatzResearch.WordTrace tailWord_3038945 prefixEnd_3038945 1560439467577717847411653 := by
  unfold tailWord_3038945
  simp only [CollatzResearch.WordTrace]
  refine ⟨110839429975428750330574289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73892953316952500220382859 110839429975428750330574289)
  ·
    refine ⟨83129572481571562747930717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110839429975428750330574289 83129572481571562747930717)
    ·
      refine ⟨31173589680589336030474019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83129572481571562747930717 31173589680589336030474019)
      ·
        refine ⟨46760384520884004045711029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31173589680589336030474019 46760384520884004045711029)
        ·
          refine ⟨4383786048832875379285409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46760384520884004045711029 4383786048832875379285409)
          ·
            refine ⟨3287839536624656534464057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4383786048832875379285409 3287839536624656534464057)
            ·
              refine ⟨2465879652468492400848043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3287839536624656534464057 2465879652468492400848043)
              ·
                refine ⟨3698819478702738601272065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465879652468492400848043 3698819478702738601272065)
                ·
                  refine ⟨2774114609027053950954049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698819478702738601272065 2774114609027053950954049)
                  ·
                    refine ⟨2080585956770290463215537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774114609027053950954049 2080585956770290463215537)
                    ·
                      refine ⟨1560439467577717847411653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080585956770290463215537 1560439467577717847411653)
                      ·
                        rfl

theorem cell23_3038945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_3038945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038945 prefixEnd_3038945 := by exact prefixLift 3038945
  have htrace : WordTrace (prefixWord ++ tailWord_3038945) baseStart_3038945 baseEnd_3038945 := by
    simpa [prefixWord, tailWord_3038945, baseEnd_3038945] using wordTrace_append hprefix tailTrace_3038945
  have hstable : (prefixWord ++ tailWord_3038945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038945).length < 2 ^ (prefixWord ++ tailWord_3038945).sum := by decide
  have hdescent : baseEnd_3038945 < baseStart_3038945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038967 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_3038967 : Nat := 118140960795 + 3038967 * 2 ^ 59
def prefixEnd_3038967 : Nat := 4983230072969 + 3 ^ 40 * 3038967 * 2
def baseEnd_3038967 : Nat := 1560450764152116761336551

theorem tailTrace_3038967 : CollatzResearch.WordTrace tailWord_3038967 prefixEnd_3038967 1560450764152116761336551 := by
  unfold tailWord_3038967
  simp only [CollatzResearch.WordTrace]
  refine ⟨110840232381349048087875155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73893488254232698725250103 110840232381349048087875155)
  ·
    refine ⟨166260348572023572131812733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110840232381349048087875155 166260348572023572131812733)
    ·
      refine ⟨62347630714508839549429775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166260348572023572131812733 62347630714508839549429775)
      ·
        refine ⟨93521446071763259324144663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62347630714508839549429775 93521446071763259324144663)
        ·
          refine ⟨140282169107644888986216995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93521446071763259324144663 140282169107644888986216995)
          ·
            refine ⟨210423253661467333479325493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140282169107644888986216995 210423253661467333479325493)
            ·
              refine ⟨19727180030762562513686765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210423253661467333479325493 19727180030762562513686765)
              ·
                refine ⟨7397692511535960942632537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19727180030762562513686765 7397692511535960942632537)
                ·
                  refine ⟨5548269383651970706974403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7397692511535960942632537 5548269383651970706974403)
                  ·
                    refine ⟨8322404075477956060461605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5548269383651970706974403 8322404075477956060461605)
                    ·
                      refine ⟨1560450764152116761336551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8322404075477956060461605 1560450764152116761336551)
                      ·
                        rfl

theorem cell23_3038967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_3038967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038967 prefixEnd_3038967 := by exact prefixLift 3038967
  have htrace : WordTrace (prefixWord ++ tailWord_3038967) baseStart_3038967 baseEnd_3038967 := by
    simpa [prefixWord, tailWord_3038967, baseEnd_3038967] using wordTrace_append hprefix tailTrace_3038967
  have hstable : (prefixWord ++ tailWord_3038967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038967).length < 2 ^ (prefixWord ++ tailWord_3038967).sum := by decide
  have hdescent : baseEnd_3038967 < baseStart_3038967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038984 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_3038984 : Nat := 118140960795 + 3038984 * 2 ^ 59
def prefixEnd_3038984 : Nat := 4983230072969 + 3 ^ 40 * 3038984 * 2
def baseEnd_3038984 : Nat := 1560459493323243194823973

theorem tailTrace_3038984 : CollatzResearch.WordTrace tailWord_3038984 prefixEnd_3038984 1560459493323243194823973 := by
  unfold tailWord_3038984
  simp only [CollatzResearch.WordTrace]
  refine ⟨55420426211143729995622003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73893901614858306660829337 55420426211143729995622003)
  ·
    refine ⟨83130639316715594993433005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55420426211143729995622003 83130639316715594993433005)
    ·
      refine ⟨31173989743768348122537377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83130639316715594993433005 31173989743768348122537377)
      ·
        refine ⟨23380492307826261091903033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31173989743768348122537377 23380492307826261091903033)
        ·
          refine ⟨17535369230869695818927275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23380492307826261091903033 17535369230869695818927275)
          ·
            refine ⟨26303053846304543728390913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535369230869695818927275 26303053846304543728390913)
            ·
              refine ⟨19727290384728407796293185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26303053846304543728390913 19727290384728407796293185)
              ·
                refine ⟨14795467788546305847219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19727290384728407796293185 14795467788546305847219889)
                ·
                  refine ⟨11096600841409729385414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14795467788546305847219889 11096600841409729385414917)
                  ·
                    refine ⟨2080612657764324259765297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11096600841409729385414917 2080612657764324259765297)
                    ·
                      refine ⟨1560459493323243194823973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080612657764324259765297 1560459493323243194823973)
                      ·
                        rfl

theorem cell23_3038984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_3038984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3038984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3038984 prefixEnd_3038984 := by exact prefixLift 3038984
  have htrace : WordTrace (prefixWord ++ tailWord_3038984) baseStart_3038984 baseEnd_3038984 := by
    simpa [prefixWord, tailWord_3038984, baseEnd_3038984] using wordTrace_append hprefix tailTrace_3038984
  have hstable : (prefixWord ++ tailWord_3038984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038984).length < 2 ^ (prefixWord ++ tailWord_3038984).sum := by decide
  have hdescent : baseEnd_3038984 < baseStart_3038984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039007 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 6]
def baseStart_3039007 : Nat := 118140960795 + 3039007 * 2 ^ 59
def prefixEnd_3039007 : Nat := 4983230072969 + 3 ^ 40 * 3039007 * 2
def baseEnd_3039007 : Nat := 173385700375366289426263

theorem tailTrace_3039007 : CollatzResearch.WordTrace tailWord_3039007 prefixEnd_3039007 173385700375366289426263 := by
  unfold tailWord_3039007
  simp only [CollatzResearch.WordTrace]
  refine ⟨110841691301204134919331275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73894460867469423279554183 110841691301204134919331275)
  ·
    refine ⟨166262536951806202378996913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110841691301204134919331275 166262536951806202378996913)
    ·
      refine ⟨124696902713854651784247685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166262536951806202378996913 124696902713854651784247685)
      ·
        refine ⟨23380669258847747209546441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124696902713854651784247685 23380669258847747209546441)
        ·
          refine ⟨17535501944135810407159831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23380669258847747209546441 17535501944135810407159831)
          ·
            refine ⟨26303252916203715610739747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535501944135810407159831 26303252916203715610739747)
            ·
              refine ⟨39454879374305573416109621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26303252916203715610739747 39454879374305573416109621)
              ·
                refine ⟨3698894941341147507760277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39454879374305573416109621 3698894941341147507760277)
                ·
                  refine ⟨173385700375366289426263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3698894941341147507760277 173385700375366289426263)
                  ·
                    rfl

theorem cell23_3039007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 6].length) (baseStart_3039007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039007 prefixEnd_3039007 := by exact prefixLift 3039007
  have htrace : WordTrace (prefixWord ++ tailWord_3039007) baseStart_3039007 baseEnd_3039007 := by
    simpa [prefixWord, tailWord_3039007, baseEnd_3039007] using wordTrace_append hprefix tailTrace_3039007
  have hstable : (prefixWord ++ tailWord_3039007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039007).length < 2 ^ (prefixWord ++ tailWord_3039007).sum := by decide
  have hdescent : baseEnd_3039007 < baseStart_3039007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039028 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3039028 : Nat := 118140960795 + 3039028 * 2 ^ 59
def prefixEnd_3039028 : Nat := 4983230072969 + 3 ^ 40 * 3039028 * 2
def baseEnd_3039028 : Nat := 520160695490680340891257

theorem tailTrace_3039028 : CollatzResearch.WordTrace tailWord_3039028 prefixEnd_3039028 520160695490680340891257 := by
  unfold tailWord_3039028
  simp only [CollatzResearch.WordTrace]
  refine ⟨55421228617064027752922869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73894971489418703670563825 55421228617064027752922869)
  ·
    refine ⟨5195740182849752601836519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55421228617064027752922869 5195740182849752601836519)
    ·
      refine ⟨7793610274274628902754779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5195740182849752601836519 7793610274274628902754779)
      ·
        refine ⟨11690415411411943354132169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793610274274628902754779 11690415411411943354132169)
        ·
          refine ⟨8767811558558957515599127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11690415411411943354132169 8767811558558957515599127)
          ·
            refine ⟨13151717337838436273398691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8767811558558957515599127 13151717337838436273398691)
            ·
              refine ⟨19727576006757654410098037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13151717337838436273398691 19727576006757654410098037)
              ·
                refine ⟨1849460250633530100946691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19727576006757654410098037 1849460250633530100946691)
                ·
                  refine ⟨2774190375950295151420037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849460250633530100946691 2774190375950295151420037)
                  ·
                    refine ⟨520160695490680340891257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774190375950295151420037 520160695490680340891257)
                    ·
                      rfl

theorem cell23_3039028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3039028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039028 prefixEnd_3039028 := by exact prefixLift 3039028
  have htrace : WordTrace (prefixWord ++ tailWord_3039028) baseStart_3039028 baseEnd_3039028 := by
    simpa [prefixWord, tailWord_3039028, baseEnd_3039028] using wordTrace_append hprefix tailTrace_3039028
  have hstable : (prefixWord ++ tailWord_3039028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039028).length < 2 ^ (prefixWord ++ tailWord_3039028).sum := by decide
  have hdescent : baseEnd_3039028 < baseStart_3039028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039077 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3039077 : Nat := 118140960795 + 3039077 * 2 ^ 59
def prefixEnd_3039077 : Nat := 4983230072969 + 3 ^ 40 * 3039077 * 2
def baseEnd_3039077 : Nat := 1560507247024111330961045

theorem tailTrace_3039077 : CollatzResearch.WordTrace tailWord_3039077 prefixEnd_3039077 1560507247024111330961045 := by
  unfold tailWord_3039077
  simp only [CollatzResearch.WordTrace]
  refine ⟨110844244410950536874379485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73896162940633691249586323 110844244410950536874379485)
  ·
    refine ⟨41566591654106451327892307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110844244410950536874379485 41566591654106451327892307)
    ·
      refine ⟨62349887481159676991838461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41566591654106451327892307 62349887481159676991838461)
      ·
        refine ⟨23381207805434878871939423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62349887481159676991838461 23381207805434878871939423)
        ·
          refine ⟨35071811708152318307909135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23381207805434878871939423 35071811708152318307909135)
          ·
            refine ⟨52607717562228477461863703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35071811708152318307909135 52607717562228477461863703)
            ·
              refine ⟨78911576343342716192795555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52607717562228477461863703 78911576343342716192795555)
              ·
                refine ⟨118367364515014074289193333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78911576343342716192795555 118367364515014074289193333)
                ·
                  refine ⟨11096940423282569464611875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118367364515014074289193333 11096940423282569464611875)
                  ·
                    refine ⟨16645410634923854196917813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11096940423282569464611875 16645410634923854196917813)
                    ·
                      refine ⟨1560507247024111330961045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16645410634923854196917813 1560507247024111330961045)
                      ·
                        rfl

theorem cell23_3039077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3039077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039077 prefixEnd_3039077 := by exact prefixLift 3039077
  have htrace : WordTrace (prefixWord ++ tailWord_3039077) baseStart_3039077 baseEnd_3039077 := by
    simpa [prefixWord, tailWord_3039077, baseEnd_3039077] using wordTrace_append hprefix tailTrace_3039077
  have hstable : (prefixWord ++ tailWord_3039077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039077).length < 2 ^ (prefixWord ++ tailWord_3039077).sum := by decide
  have hdescent : baseEnd_3039077 < baseStart_3039077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039084 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_3039084 : Nat := 118140960795 + 3039084 * 2 ^ 59
def prefixEnd_3039084 : Nat := 4983230072969 + 3 ^ 40 * 3039084 * 2
def baseEnd_3039084 : Nat := 520170280462897601191171

theorem tailTrace_3039084 : CollatzResearch.WordTrace tailWord_3039084 prefixEnd_3039084 520170280462897601191171 := by
  unfold tailWord_3039084
  simp only [CollatzResearch.WordTrace]
  refine ⟨55422249860962588534942153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73896333147950118046589537 55422249860962588534942153)
  ·
    refine ⟨41566687395721941401206615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55422249860962588534942153 41566687395721941401206615)
    ·
      refine ⟨62350031093582912101809923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41566687395721941401206615 62350031093582912101809923)
      ·
        refine ⟨93525046640374368152714885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62350031093582912101809923 93525046640374368152714885)
        ·
          refine ⟨17535946245070194028634041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93525046640374368152714885 17535946245070194028634041)
          ·
            refine ⟨13151959683802645521475531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17535946245070194028634041 13151959683802645521475531)
            ·
              refine ⟨19727939525703968282213297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13151959683802645521475531 19727939525703968282213297)
              ·
                refine ⟨14795954644277976211659973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19727939525703968282213297 14795954644277976211659973)
                ·
                  refine ⟨2774241495802120539686245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14795954644277976211659973 2774241495802120539686245)
                  ·
                    refine ⟨520170280462897601191171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2774241495802120539686245 520170280462897601191171)
                    ·
                      rfl

theorem cell23_3039084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_3039084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039084 prefixEnd_3039084 := by exact prefixLift 3039084
  have htrace : WordTrace (prefixWord ++ tailWord_3039084) baseStart_3039084 baseEnd_3039084 := by
    simpa [prefixWord, tailWord_3039084, baseEnd_3039084] using wordTrace_append hprefix tailTrace_3039084
  have hstable : (prefixWord ++ tailWord_3039084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039084).length < 2 ^ (prefixWord ++ tailWord_3039084).sum := by decide
  have hdescent : baseEnd_3039084 < baseStart_3039084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039108 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_3039108 : Nat := 118140960795 + 3039108 * 2 ^ 59
def prefixEnd_3039108 : Nat := 4983230072969 + 3 ^ 40 * 3039108 * 2
def baseEnd_3039108 : Nat := 1560523164924400709673403

theorem tailTrace_3039108 : CollatzResearch.WordTrace tailWord_3039108 prefixEnd_3039108 1560523164924400709673403 := by
  unfold tailWord_3039108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55422687536919114584378989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73896916715892152779171985 55422687536919114584378989)
  ·
    refine ⟨20783507826344667969142121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55422687536919114584378989 20783507826344667969142121)
    ·
      refine ⟨15587630869758500976856591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20783507826344667969142121 15587630869758500976856591)
      ·
        refine ⟨23381446304637751465284887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587630869758500976856591 23381446304637751465284887)
        ·
          refine ⟨35072169456956627197927331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23381446304637751465284887 35072169456956627197927331)
          ·
            refine ⟨52608254185434940796890997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35072169456956627197927331 52608254185434940796890997)
            ·
              refine ⟨4932023829884525699708531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52608254185434940796890997 4932023829884525699708531)
              ·
                refine ⟨7398035744826788549562797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932023829884525699708531 7398035744826788549562797)
                ·
                  refine ⟨2774263404310045706086049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7398035744826788549562797 2774263404310045706086049)
                  ·
                    refine ⟨2080697553232534279564537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774263404310045706086049 2080697553232534279564537)
                    ·
                      refine ⟨1560523164924400709673403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2080697553232534279564537 1560523164924400709673403)
                      ·
                        rfl

theorem cell23_3039108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_3039108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039108 prefixEnd_3039108 := by exact prefixLift 3039108
  have htrace : WordTrace (prefixWord ++ tailWord_3039108) baseStart_3039108 baseEnd_3039108 := by
    simpa [prefixWord, tailWord_3039108, baseEnd_3039108] using wordTrace_append hprefix tailTrace_3039108
  have hstable : (prefixWord ++ tailWord_3039108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039108).length < 2 ^ (prefixWord ++ tailWord_3039108).sum := by decide
  have hdescent : baseEnd_3039108 < baseStart_3039108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039128 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3039128 : Nat := 118140960795 + 3039128 * 2 ^ 59
def prefixEnd_3039128 : Nat := 4983230072969 + 3 ^ 40 * 3039128 * 2
def baseEnd_3039128 : Nat := 1560533434537490631423311

theorem tailTrace_3039128 : CollatzResearch.WordTrace tailWord_3039128 prefixEnd_3039128 1560533434537490631423311 := by
  unfold tailWord_3039128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55423052266882886292243019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73897403022510515056324025 55423052266882886292243019)
  ·
    refine ⟨83134578400324329438364529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55423052266882886292243019 83134578400324329438364529)
    ·
      refine ⟨62350933800243247078773397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83134578400324329438364529 62350933800243247078773397)
      ·
        refine ⟨2922700021886402206817503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62350933800243247078773397 2922700021886402206817503)
        ·
          refine ⟨4384050032829603310226255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922700021886402206817503 4384050032829603310226255)
          ·
            refine ⟨6576075049244404965339383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384050032829603310226255 6576075049244404965339383)
            ·
              refine ⟨9864112573866607448009075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576075049244404965339383 9864112573866607448009075)
              ·
                refine ⟨14796168860799911172013613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9864112573866607448009075 14796168860799911172013613)
                ·
                  refine ⟨5548563322799966689505105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14796168860799911172013613 5548563322799966689505105)
                  ·
                    refine ⟨4161422492099975017128829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5548563322799966689505105 4161422492099975017128829)
                    ·
                      refine ⟨1560533434537490631423311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4161422492099975017128829 1560533434537490631423311)
                      ·
                        rfl

theorem cell23_3039128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3039128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039128 prefixEnd_3039128 := by exact prefixLift 3039128
  have htrace : WordTrace (prefixWord ++ tailWord_3039128) baseStart_3039128 baseEnd_3039128 := by
    simpa [prefixWord, tailWord_3039128, baseEnd_3039128] using wordTrace_append hprefix tailTrace_3039128
  have hstable : (prefixWord ++ tailWord_3039128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039128).length < 2 ^ (prefixWord ++ tailWord_3039128).sum := by decide
  have hdescent : baseEnd_3039128 < baseStart_3039128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039147 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_3039147 : Nat := 118140960795 + 3039147 * 2 ^ 59
def prefixEnd_3039147 : Nat := 4983230072969 + 3 ^ 40 * 3039147 * 2
def baseEnd_3039147 : Nat := 1560543190669926057085723

theorem tailTrace_3039147 : CollatzResearch.WordTrace tailWord_3039147 prefixEnd_3039147 1560543190669926057085723 := by
  unfold tailWord_3039147
  simp only [CollatzResearch.WordTrace]
  refine ⟨110846797520696938829427695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73897865013797959219618463 110846797520696938829427695)
  ·
    refine ⟨166270196281045408244141543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110846797520696938829427695 166270196281045408244141543)
    ·
      refine ⟨249405294421568112366212315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166270196281045408244141543 249405294421568112366212315)
      ·
        refine ⟨374107941632352168549318473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249405294421568112366212315 374107941632352168549318473)
        ·
          refine ⟨280580956224264126411988855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374107941632352168549318473 280580956224264126411988855)
          ·
            refine ⟨420871434336396189617983283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280580956224264126411988855 420871434336396189617983283)
            ·
              refine ⟨631307151504594284426974925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420871434336396189617983283 631307151504594284426974925)
              ·
                refine ⟨236740181814222856660115597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631307151504594284426974925 236740181814222856660115597)
                ·
                  refine ⟨88777568180333571247543349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236740181814222856660115597 88777568180333571247543349)
                  ·
                    refine ⟨8322897016906272304457189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88777568180333571247543349 8322897016906272304457189)
                    ·
                      refine ⟨1560543190669926057085723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8322897016906272304457189 1560543190669926057085723)
                      ·
                        rfl

theorem cell23_3039147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_3039147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039147 prefixEnd_3039147 := by exact prefixLift 3039147
  have htrace : WordTrace (prefixWord ++ tailWord_3039147) baseStart_3039147 baseEnd_3039147 := by
    simpa [prefixWord, tailWord_3039147, baseEnd_3039147] using wordTrace_append hprefix tailTrace_3039147
  have hstable : (prefixWord ++ tailWord_3039147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039147).length < 2 ^ (prefixWord ++ tailWord_3039147).sum := by decide
  have hdescent : baseEnd_3039147 < baseStart_3039147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3039177 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_3039177 : Nat := 118140960795 + 3039177 * 2 ^ 59
def prefixEnd_3039177 : Nat := 4983230072969 + 3 ^ 40 * 3039177 * 2
def baseEnd_3039177 : Nat := 1560558595089560939710585

theorem tailTrace_3039177 : CollatzResearch.WordTrace tailWord_3039177 prefixEnd_3039177 1560558595089560939710585 := by
  unfold tailWord_3039177
  simp only [CollatzResearch.WordTrace]
  refine ⟨110847891710588253953019785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73898594473725502635346523 110847891710588253953019785)
  ·
    refine ⟨83135918782941190464764839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110847891710588253953019785 83135918782941190464764839)
    ·
      refine ⟨124703878174411785697147259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83135918782941190464764839 124703878174411785697147259)
      ·
        refine ⟨187055817261617678545720889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124703878174411785697147259 187055817261617678545720889)
        ·
          refine ⟨140291862946213258909290667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187055817261617678545720889 140291862946213258909290667)
          ·
            refine ⟨210437794419319888363936001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140291862946213258909290667 210437794419319888363936001)
            ·
              refine ⟨157828345814489916272952001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210437794419319888363936001 157828345814489916272952001)
              ·
                refine ⟨118371259360867437204714001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157828345814489916272952001 118371259360867437204714001)
                ·
                  refine ⟨88778444520650577903535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118371259360867437204714001 88778444520650577903535501)
                  ·
                    refine ⟨33291916695243966713825813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88778444520650577903535501 33291916695243966713825813)
                    ·
                      refine ⟨1560558595089560939710585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33291916695243966713825813 1560558595089560939710585)
                      ·
                        rfl

theorem cell23_3039177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_3039177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3039177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3039177 prefixEnd_3039177 := by exact prefixLift 3039177
  have htrace : WordTrace (prefixWord ++ tailWord_3039177) baseStart_3039177 baseEnd_3039177 := by
    simpa [prefixWord, tailWord_3039177, baseEnd_3039177] using wordTrace_append hprefix tailTrace_3039177
  have hstable : (prefixWord ++ tailWord_3039177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3039177).length < 2 ^ (prefixWord ++ tailWord_3039177).sum := by decide
  have hdescent : baseEnd_3039177 < baseStart_3039177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3039177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
